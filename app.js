(() => {
  'use strict';

  // ---------------------------------------------------------------- data sources (all public, no key)
  const ESRI = 'https://services.arcgis.com/P3ePLMYs2RVChkJx/ArcGIS/rest/services';
  const SRC = {
    countries: `${ESRI}/World_Countries_(Generalized)/FeatureServer/0/query`,
    admin:     `${ESRI}/World_Administrative_Divisions/FeatureServer/0/query`,
    cities:    `${ESRI}/World_Cities/FeatureServer/0/query`,
    usaRivers: `${ESRI}/USA_Rivers_and_Streams/FeatureServer/0/query`,
    worldRivers: [
      'https://services5.arcgis.com/XqaKEQIgV03geG0E/ArcGIS/rest/services/World_Major_Rivers_WFL1/FeatureServer/0/query',
      'https://maps.nccs.nasa.gov/mapping/rest/services/base_layers/esri_world_major_rivers/FeatureServer/0/query',
    ],
    overpass: 'https://overpass-api.de/api/interpreter',
  };
  const DPI = 200;                        // sheet resolution (pixels per inch)
  const pt = p => p * DPI / 72;           // points → pixels
  const inch = i => i * DPI;

  // ---------------------------------------------------------------- state
  const state = {
    region: null,          // {type:'country'|'state', name, country, formatted}
    boundary: null,        // GeoJSON geometry (Polygon / MultiPolygon)
    outer: null,           // outer-edge polylines for multi-state regions
    wrap: false,           // true when the region crosses the antimeridian
    bounds: null,
    places: null,          // [{name, lon, lat, pop, capital}]
    rivers: null,          // [{name, lines:[[[lon,lat],...],...]}]
    subdiv: null,          // [{name, geometry}]
    orient: 'landscape',
    weight: 3,
    nCities: 12,
    loading: new Set(),
    seq: 0,                // bumps on every new region; stale fetches are ignored
  };

  const $ = id => document.getElementById(id);
  const canvas = $('sheet'), ctx = canvas.getContext('2d');
  const ov = {
    cities: $('ov-cities'), capitals: $('ov-capitals'), rivers: $('ov-rivers'),
    subdiv: $('ov-subdiv'), grid: $('ov-grid'), labels: $('ov-labels'), title: $('ov-title'),
  };

  // ---------------------------------------------------------------- helpers
  function setStatus(msg, isError) {
    const el = $('status');
    el.textContent = msg;
    el.className = isError ? 'err' : '';
  }
  function busy(on, text) {
    const el = $('busy');
    if (on) { state.loading.add(text); $('busy-text').textContent = text; el.classList.add('show'); }
    else { state.loading.delete(text); if (state.loading.size) $('busy-text').textContent = [...state.loading].pop(); else el.classList.remove('show'); }
  }
  async function getJSON(url, opts) {
    const res = await fetch(url, opts);
    if (!res.ok) throw new Error(`The map service returned an error (${res.status}).`);
    return res.json();
  }
  // Query an ArcGIS feature layer. Errors come back as 200 + {error}, so check for that.
  async function arcQuery(url, params) {
    const q = new URLSearchParams({ f: 'json', ...params });
    const data = await getJSON(`${url}?${q}`);
    if (data.error) throw new Error(data.error.message || 'The map service could not run that query.');
    return data;
  }
  const esc = s => String(s).replace(/'/g, "''");
  const W = lon => (state.wrap && lon < 0) ? lon + 360 : lon;   // antimeridian unwrap

  function eachRing(geom, fn) {
    if (!geom) return;
    if (geom.type === 'Polygon') geom.coordinates.forEach(fn);
    else if (geom.type === 'MultiPolygon') geom.coordinates.forEach(poly => poly.forEach(fn));
  }
  // Combine the polygons of several features into one MultiPolygon
  function mergeGeoms(features) {
    const polys = [];
    features.forEach(f => {
      const g = f.geometry; if (!g) return;
      if (g.type === 'Polygon') polys.push(g.coordinates);
      else if (g.type === 'MultiPolygon') g.coordinates.forEach(p => polys.push(p));
    });
    if (!polys.length) return null;
    return polys.length === 1 ? { type: 'Polygon', coordinates: polys[0] } : { type: 'MultiPolygon', coordinates: polys };
  }
  function computeBounds(geom) {
    let minLon = 180, maxLon = -180, minLat = 90, maxLat = -90;
    eachRing(geom, ring => ring.forEach(([lon, lat]) => {
      if (lon < minLon) minLon = lon; if (lon > maxLon) maxLon = lon;
      if (lat < minLat) minLat = lat; if (lat > maxLat) maxLat = lat;
    }));
    state.wrap = (maxLon - minLon) > 180;
    if (state.wrap) {
      minLon = 360; maxLon = -360;
      eachRing(geom, ring => ring.forEach(([lon]) => { const l = W(lon); if (l < minLon) minLon = l; if (l > maxLon) maxLon = l; }));
    }
    return { minLon, maxLon, minLat, maxLat };
  }
  // Even-odd point-in-polygon test across every ring (holes included)
  function pointInGeom(lon, lat, geom) {
    const x = W(lon), y = lat; let inside = false;
    eachRing(geom, ring => {
      for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
        const xi = W(ring[i][0]), yi = ring[i][1], xj = W(ring[j][0]), yj = ring[j][1];
        if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) inside = !inside;
      }
    });
    return inside;
  }
  function ringCentroid(ring) { // area-weighted centroid of a lon/lat ring
    let a = 0, cx = 0, cy = 0;
    for (let i = 0, n = ring.length - 1; i < n; i++) {
      const [x0, y0] = ring[i], [x1, y1] = ring[i + 1];
      const f = W(x0) * y1 - W(x1) * y0;
      a += f; cx += (W(x0) + W(x1)) * f; cy += (y0 + y1) * f;
    }
    if (Math.abs(a) < 1e-12) return [W(ring[0][0]), ring[0][1], 0];
    return [cx / (3 * a), cy / (3 * a), Math.abs(a / 2)];
  }
  function largestRingCentroid(geom) {
    let best = null;
    const polys = geom.type === 'Polygon' ? [geom.coordinates] : geom.coordinates;
    polys.forEach(poly => { const c = ringCentroid(poly[0]); if (!best || c[2] > best[2]) best = c; });
    return best;
  }
  const slug = s => s.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/(^-|-$)/g, '');
  // Bounding box as a real-longitude ArcGIS envelope (a wrapped region just uses the whole globe's width)
  function envelope() {
    const b = state.bounds;
    return JSON.stringify(state.wrap
      ? { xmin: -180, ymin: b.minLat, xmax: 180, ymax: b.maxLat, spatialReference: { wkid: 4326 } }
      : { xmin: b.minLon, ymin: b.minLat, xmax: b.maxLon, ymax: b.maxLat, spatialReference: { wkid: 4326 } });
  }
  const envParams = () => ({ geometry: envelope(), geometryType: 'esriGeometryEnvelope', inSR: 4326, spatialRel: 'esriSpatialRelIntersects' });

  // ---------------------------------------------------------------- US regions & neighbours
  const US = { AL:'Alabama', AK:'Alaska', AZ:'Arizona', AR:'Arkansas', CA:'California', CO:'Colorado', CT:'Connecticut', DE:'Delaware', DC:'District of Columbia', FL:'Florida', GA:'Georgia', HI:'Hawaii', ID:'Idaho', IL:'Illinois', IN:'Indiana', IA:'Iowa', KS:'Kansas', KY:'Kentucky', LA:'Louisiana', ME:'Maine', MD:'Maryland', MA:'Massachusetts', MI:'Michigan', MN:'Minnesota', MS:'Mississippi', MO:'Missouri', MT:'Montana', NE:'Nebraska', NV:'Nevada', NH:'New Hampshire', NJ:'New Jersey', NM:'New Mexico', NY:'New York', NC:'North Carolina', ND:'North Dakota', OH:'Ohio', OK:'Oklahoma', OR:'Oregon', PA:'Pennsylvania', RI:'Rhode Island', SC:'South Carolina', SD:'South Dakota', TN:'Tennessee', TX:'Texas', UT:'Utah', VT:'Vermont', VA:'Virginia', WA:'Washington', WV:'West Virginia', WI:'Wisconsin', WY:'Wyoming' };
  const US_CODE = Object.fromEntries(Object.entries(US).map(([c, n]) => [n.toUpperCase(), c]));
  const USA = 'United States';
  // land-border adjacency (symmetric), by postal code
  const US_ADJ = {};
  'AL:FL,GA,MS,TN AZ:CA,CO,NV,NM,UT AR:LA,MS,MO,OK,TN,TX CA:NV,OR CO:KS,NE,NM,OK,UT,WY CT:MA,NY,RI DE:MD,NJ,PA DC:MD,VA FL:GA GA:NC,SC,TN ID:MT,NV,OR,UT,WA,WY IL:IN,IA,KY,MO,WI IN:KY,MI,OH IA:MN,MO,NE,SD,WI KS:MO,NE,OK KY:MO,OH,TN,VA,WV LA:MS,TX ME:NH MD:PA,VA,WV MA:NH,NY,RI,VT MI:OH,WI MN:ND,SD,WI MS:TN MO:NE,OK,TN MT:ND,SD,WY NE:SD,WY NV:OR,UT NH:VT NJ:NY,PA NM:OK,TX,UT NY:PA,VT NC:SC,TN,VA ND:SD OH:PA,WV OK:TX OR:WA PA:WV SD:WY TN:VA UT:WY VA:WV'
    .split(' ').forEach(e => { const [k, v] = e.split(':'); v.split(',').forEach(n => { (US_ADJ[k] = US_ADJ[k] || new Set()).add(n); (US_ADJ[n] = US_ADJ[n] || new Set()).add(k); }); });
  // named regions; aliases are matched after stripping filler words ("the", "US", "states", "region"…)
  const REGIONS = [
    ['Pacific Northwest', 'WA OR ID', 'pacific northwest|pnw'],
    ['Northwest', 'WA OR ID MT WY', 'northwest|northwestern'],
    ['West Coast', 'WA OR CA', 'west coast|pacific coast'],
    ['Southwest', 'AZ NM NV UT CO', 'southwest|southwestern'],
    ['Four Corners', 'AZ CO NM UT', 'four corners'],
    ['Mountain West', 'MT ID WY CO UT NV AZ NM', 'mountain west|mountain|rocky mountain|rocky mountains|rockies|intermountain west'],
    ['West', 'WA OR CA NV ID MT WY UT CO AZ NM', 'west|western'],
    ['Great Plains', 'ND SD NE KS OK', 'great plains|plains'],
    ['Midwest', 'OH MI IN IL WI MN IA MO ND SD NE KS', 'midwest|midwestern|middle west'],
    ['Upper Midwest', 'MN WI MI', 'upper midwest'],
    ['Great Lakes', 'MN WI MI IL IN OH PA NY', 'great lakes'],
    ['East North Central', 'OH IN IL MI WI', 'east north central'],
    ['West North Central', 'MN IA MO ND SD NE KS', 'west north central'],
    ['Northeast', 'ME NH VT MA RI CT NY NJ PA', 'northeast|northeastern'],
    ['New England', 'ME NH VT MA RI CT', 'new england'],
    ['Mid-Atlantic', 'NY NJ PA DE MD DC', 'mid atlantic|middle atlantic'],
    ['East Coast', 'ME NH MA RI CT NY NJ DE MD VA NC SC GA FL', 'east coast|atlantic coast'],
    ['South', 'DE MD DC VA WV NC SC GA FL KY TN AL MS AR LA OK TX', 'south|southern'],
    ['Southeast', 'VA WV NC SC GA FL KY TN AL MS AR LA', 'southeast|southeastern'],
    ['South Atlantic', 'DE MD DC VA WV NC SC GA FL', 'south atlantic'],
    ['Deep South', 'AL GA LA MS SC', 'deep south'],
    ['Gulf Coast', 'TX LA MS AL FL', 'gulf coast|gulf'],
    ['East South Central', 'KY TN AL MS', 'east south central'],
    ['West South Central', 'AR LA OK TX', 'west south central'],
    ['Pacific', 'WA OR CA AK HI', 'pacific'],
    ['Contiguous United States', Object.keys(US).filter(c => c !== 'AK' && c !== 'HI').join(' '), 'contiguous|continental|lower 48|lower forty eight|mainland'],
  ].map(([name, codes, aliases]) => ({ name, states: codes.split(' ').map(c => US[c]), aliases: aliases.split('|') }));
  const REGION_BY_ALIAS = new Map(); REGIONS.forEach(r => r.aliases.forEach(a => REGION_BY_ALIAS.set(a, r)));
  const regionKey = q => q.toLowerCase().replace(/[-–_.,]/g, ' ').replace(/\b(the|us|usa|u s|u s a|united states|america|american|states?|region|regional|area|of|coast of)\b/g, ' ').replace(/\s+/g, ' ').trim();
  const NEIGH_RE = /^(.+?)\s+(?:and|&|\+|with|plus)\s+(?:its\s+|the\s+)?(?:nearby|neighbou?ring|neighbou?rs|surrounding|adjacent|bordering|border)(?:\s+(?:states?|provinces?|regions?|areas?))?$/i;
  const AROUND_RE = /^(?:around|near|surrounding|states\s+(?:around|near|bordering))\s+(.+)$/i;

  // ---------------------------------------------------------------- region search
  const ALIASES = {
    'usa': USA, 'us': USA, 'u.s.': USA, 'u.s.a.': USA, 'united states of america': USA, 'america': USA,
    'uk': 'United Kingdom', 'britain': 'United Kingdom', 'great britain': 'United Kingdom', 'uae': 'United Arab Emirates', 'holland': 'Netherlands',
  };
  const regionMatch = r => ({ type: 'region', name: r.name, country: USA, members: r.states, formatted: `${r.name} (${r.states.length} states)`, label: 'US region', exact: true });

  async function findRegion() {
    const raw = $('q').value.trim();
    if (!raw) return;
    const box = $('matches');
    box.innerHTML = ''; box.classList.remove('show');
    busy(true, 'Searching…'); setStatus(`Searching for "${raw}"…`);
    try {
      // "Oregon and nearby states" / "around Oregon" → a state plus its neighbours
      const nm = raw.match(NEIGH_RE) || raw.match(AROUND_RE);
      const neighbours = !!nm;
      let [name, hint] = (nm ? nm[1] : raw).split(',').map(s => s.trim());
      name = ALIASES[name.toLowerCase()] || name;
      if (hint) hint = ALIASES[hint.toLowerCase()] || hint;
      let matches = [];

      // a named US region?
      const reg = REGION_BY_ALIAS.get(regionKey(name));
      if (reg && !neighbours) matches.push(regionMatch(reg));
      // a US postal code?
      const code = name.toUpperCase();
      if (US[code]) matches.push({ type: 'state', name: US[code], country: USA, formatted: `${US[code]}, ${USA}`, label: 'state', exact: true });

      const N = esc(name.toUpperCase());
      const countryWhere = `UPPER(COUNTRY) LIKE '${N}%'` + (name.length === 2 ? ` OR ISO='${N}'` : '');
      const adminWhere = `UPPER(NAME) LIKE '${N}%'` + (hint ? ` AND UPPER(COUNTRY) LIKE '${esc(hint.toUpperCase())}%'` : '');
      const [c, a] = await Promise.all([
        neighbours ? { features: [] } : arcQuery(SRC.countries, { where: countryWhere, outFields: 'COUNTRY,ISO', returnGeometry: false, resultRecordCount: 10 }),
        arcQuery(SRC.admin, { where: adminWhere, outFields: 'NAME,COUNTRY,ADMINTYPE', returnGeometry: false, returnDistinctValues: true, resultRecordCount: 25 }),
      ]);
      const exact = s => s && s.toUpperCase() === name.toUpperCase();
      (c.features || []).forEach(f => { const p = f.attributes; if (p.COUNTRY) matches.push({ type: 'country', name: p.COUNTRY, country: p.COUNTRY, formatted: p.COUNTRY, label: 'country', exact: exact(p.COUNTRY) || exact(p.ISO) }); });
      (a.features || []).forEach(f => { const p = f.attributes; if (p.NAME) matches.push({ type: 'state', name: p.NAME, country: p.COUNTRY, formatted: `${p.NAME}, ${p.COUNTRY}`, label: (p.ADMINTYPE || 'region').toLowerCase(), exact: exact(p.NAME) }); });
      if (neighbours) matches = matches.filter(m => m.type === 'state').map(m => ({ ...m, type: 'neighbours', formatted: `${m.name} and nearby ${m.country === USA ? 'states' : 'regions'}`, label: `${m.label} + neighbours` }));
      // exact matches first, then regions/countries, then alphabetical
      const rank = m => m.type === 'region' ? 0 : m.type === 'country' ? 1 : 2;
      matches.sort((x, y) => (y.exact - x.exact) || (rank(x) - rank(y)) || x.formatted.localeCompare(y.formatted));
      const seen = new Set(); matches = matches.filter(m => !seen.has(m.formatted) && seen.add(m.formatted));
      if (!matches.length) { setStatus(`No country, state, province, or US region called "${name}" was found. Check the spelling, add the country ("Georgia, USA"), or try a region like "New England".`, true); return; }
      if (matches.length === 1 || (matches[0].exact && !matches[1].exact)) { chooseRegion(matches[0]); return; }
      box.innerHTML = '<div class="hint">Several places match — pick one:</div>';
      matches.slice(0, 8).forEach(m => {
        const b = document.createElement('button');
        b.type = 'button'; b.className = 'match';
        b.innerHTML = `<span class="label">${m.formatted}</span><span class="type">${m.label}</span>`;
        b.addEventListener('click', () => { [...box.children].forEach(c => c.classList.remove('active')); b.classList.add('active'); chooseRegion(m); });
        box.appendChild(b);
      });
      box.classList.add('show');
      setStatus('Choose a match on the left.');
    } catch (e) { setStatus(e.message, true); }
    finally { busy(false, 'Searching…'); }
  }

  // Which states/provinces touch this one? US: adjacency table. Elsewhere: spatial query with the (thinned) outline.
  async function neighboursOf(base) {
    if (base.country === USA && US_CODE[base.name.toUpperCase()]) {
      return [...(US_ADJ[US_CODE[base.name.toUpperCase()]] || [])].map(c => US[c]);
    }
    const g = await arcQuery(SRC.admin, { where: `NAME='${esc(base.name)}' AND COUNTRY='${esc(base.country)}'`, outFields: 'NAME', returnGeometry: true, outSR: 4326, geometryPrecision: 3, maxAllowableOffset: 0.02, f: 'geojson' });
    const geom = mergeGeoms(g.features || []);
    if (!geom) return [];
    let total = 0; eachRing(geom, r => total += r.length);
    const step = Math.max(1, Math.ceil(total / 2500)), rings = [];
    eachRing(geom, r => { const t = r.filter((_, i) => i % step === 0); if (t.length > 2) rings.push(t.concat([t[0]])); });
    const body = new URLSearchParams({
      f: 'json', where: `COUNTRY='${esc(base.country)}' AND NAME<>'${esc(base.name)}'`, outFields: 'NAME', returnGeometry: false, returnDistinctValues: true,
      geometry: JSON.stringify({ rings, spatialReference: { wkid: 4326 } }), geometryType: 'esriGeometryPolygon', inSR: 4326,
      spatialRel: 'esriSpatialRelIntersects', distance: 2000, units: 'esriSRUnit_Meter',
    });
    const data = await getJSON(SRC.admin, { method: 'POST', body, headers: { 'Content-Type': 'application/x-www-form-urlencoded' } });
    if (data.error) throw new Error(data.error.message || 'Neighbour lookup failed.');
    return [...new Set((data.features || []).map(f => f.attributes.NAME).filter(Boolean))];
  }

  // Segments that belong to only one member polygon form the outer edge of a multi-state region
  function outerEdges(members) {
    const key = (p, q) => { const a = p[0].toFixed(5) + ',' + p[1].toFixed(5), b = q[0].toFixed(5) + ',' + q[1].toFixed(5); return a < b ? a + '|' + b : b + '|' + a; };
    const count = new Map();
    members.forEach(m => eachRing(m.geometry, ring => { for (let i = 0; i < ring.length - 1; i++) { const k = key(ring[i], ring[i + 1]); count.set(k, (count.get(k) || 0) + 1); } }));
    const outer = [];
    members.forEach(m => eachRing(m.geometry, ring => {
      let cur = null;
      for (let i = 0; i < ring.length - 1; i++) {
        if (count.get(key(ring[i], ring[i + 1])) === 1) { if (!cur) cur = [ring[i]]; cur.push(ring[i + 1]); }
        else if (cur) { outer.push(cur); cur = null; }
      }
      if (cur) outer.push(cur);
    }));
    return outer;
  }

  async function chooseRegion(r) {
    const seq = ++state.seq;
    state.region = r; state.boundary = null; state.outer = null; state.places = state.rivers = state.subdiv = null;
    ['n-cities', 'n-capitals', 'n-rivers', 'n-subdiv'].forEach(id => $(id).textContent = '');
    render();
    busy(true, 'Loading outline…'); setStatus(`Loading the outline of ${r.formatted}…`);
    try {
      if (r.type === 'neighbours') {
        const around = await neighboursOf(r);
        if (seq !== state.seq) return;
        r = { type: 'region', name: `${r.name} and nearby ${r.country === USA ? 'states' : 'regions'}`, country: r.country, members: [r.name, ...around], formatted: `${r.name} and ${around.length} neighbouring ${r.country === USA ? 'states' : 'regions'}`, exact: true };
        state.region = r;
        if (!around.length) setStatus(`No neighbours were found for ${r.members[0]}; showing it alone.`, true);
      }
      const isCountry = r.type === 'country', isRegion = r.type === 'region';
      ov.subdiv.disabled = !(isCountry || isRegion);
      if (ov.subdiv.disabled) { ov.subdiv.checked = false; $('n-subdiv').textContent = 'countries only'; }
      if (isRegion) ov.subdiv.checked = true;

      let data;
      if (isCountry) data = await arcQuery(SRC.countries, { where: `COUNTRY='${esc(r.name)}'`, outFields: 'COUNTRY', returnGeometry: true, outSR: 4326, geometryPrecision: 5, f: 'geojson' });
      else if (isRegion) data = await arcQuery(SRC.admin, { where: `NAME IN (${r.members.map(n => `'${esc(n)}'`).join(',')}) AND COUNTRY='${esc(r.country)}'`, outFields: 'NAME', returnGeometry: true, outSR: 4326, geometryPrecision: 5, resultRecordCount: 2000, f: 'geojson', ...(r.members.length > 12 ? { maxAllowableOffset: 0.01 } : {}) });
      else data = await arcQuery(SRC.admin, { where: `NAME='${esc(r.name)}' AND COUNTRY='${esc(r.country)}'`, outFields: 'NAME', returnGeometry: true, outSR: 4326, geometryPrecision: 5, f: 'geojson' });
      if (seq !== state.seq) return;
      const g = mergeGeoms(data.features || []);
      if (!g) { setStatus(`No outline is available for ${r.formatted}.`, true); return; }
      state.boundary = g;
      state.bounds = computeBounds(g);
      if (isRegion) {
        const byName = new Map();
        (data.features || []).forEach(f => { const n = (f.properties && f.properties.NAME) || ''; if (!byName.has(n)) byName.set(n, []); byName.get(n).push(f); });
        state.subdiv = [...byName].map(([name, feats]) => ({ name, geometry: mergeGeoms(feats) })).filter(m => m.geometry);
        state.outer = outerEdges(state.subdiv);
        $('n-subdiv').textContent = `${state.subdiv.length} states`;
        const missing = r.members.filter(n => !byName.has(n));
        if (missing.length) setStatus(`Not found in the boundary data: ${missing.join(', ')}.`, true);
      }
      render();
      if (!$('status').classList.contains('err')) setStatus(`${r.formatted} ready.`);
      ['jpg', 'pdf', 'print'].forEach(id => $(id).disabled = false);
      refreshOverlays();
    } catch (e) { if (seq === state.seq) setStatus(e.message, true); }
    finally { busy(false, 'Loading outline…'); }
  }

  const regionName = () => state.region ? state.region.name : '';
  // names of the US states on the map (for the USA rivers layer), or null when the map isn't US states
  const usStates = () => {
    const r = state.region; if (!r || r.country !== USA) return null;
    if (r.type === 'state') return [r.name];
    if (r.type === 'region') return r.members;
    return null;
  };

  // ---------------------------------------------------------------- overlays (fetched lazily, cached per region)
  function refreshOverlays() {
    if (!state.boundary) return;
    if ((ov.cities.checked || ov.capitals.checked) && !state.places) loadPlaces();
    if (ov.rivers.checked && !state.rivers) loadRivers();
    if (ov.subdiv.checked && !state.subdiv) loadSubdivisions();
    render();
  }

  async function loadPlaces() {
    const seq = state.seq;
    busy(true, 'Finding cities…');
    try {
      const data = await arcQuery(SRC.cities, {
        ...envParams(), where: '1=1', outFields: 'CITY_NAME,STATUS,POP', orderByFields: 'POP DESC',
        resultRecordCount: 2000, returnGeometry: true, outSR: 4326, f: 'geojson',
      });
      if (seq !== state.seq) return;
      const seen = new Set(), places = [];
      (data.features || []).forEach(f => {
        const p = f.properties || {}, [lon, lat] = f.geometry.coordinates;
        const name = p.CITY_NAME; if (!name) return;
        if (!pointInGeom(lon, lat, state.boundary)) return;        // keep only cities inside the outline
        const key = name + '|' + lon.toFixed(1) + '|' + lat.toFixed(1);
        if (seen.has(key)) return; seen.add(key);
        const st = String(p.STATUS || '');
        places.push({ name, lon, lat, pop: +p.POP || 0, capital: /national/i.test(st) ? 'national' : /provincial/i.test(st) ? 'regional' : null });
      });
      places.sort((a, b) => b.pop - a.pop);
      state.places = places;
      $('n-cities').textContent = places.length ? `${places.length} found` : 'none';
      $('n-capitals').textContent = places.filter(p => p.capital).length || 'none';
      if (!places.length) setStatus('No cities were found inside this region.', true);
    } catch (e) { if (seq === state.seq) { state.places = []; setStatus('Cities could not be loaded: ' + e.message, true); } }
    finally { busy(false, 'Finding cities…'); render(); }
  }

  // GeoJSON LineString / MultiLineString features → [{name, lines}]
  function linesFromGeoJSON(features, nameOf) {
    const out = [];
    features.forEach(f => {
      const g = f.geometry; if (!g) return;
      const lines = g.type === 'LineString' ? [g.coordinates] : g.type === 'MultiLineString' ? g.coordinates : [];
      if (lines.length) out.push({ name: nameOf(f.properties || {}) || '', lines });
    });
    return out;
  }
  async function riversFromOverpass() {
    const b = state.bounds, lo = l => l > 180 ? l - 360 : l;
    const bbox = state.wrap ? `${b.minLat},-180,${b.maxLat},180` : `${b.minLat},${lo(b.minLon)},${b.maxLat},${lo(b.maxLon)}`;
    const post = q => getJSON(SRC.overpass, { method: 'POST', body: 'data=' + encodeURIComponent(q), headers: { 'Content-Type': 'application/x-www-form-urlencoded' } });
    // pass 1: list named river relations in the box (cheap, no geometry); rank by how many segments they have
    const list = await post(`[out:json][timeout:60][bbox:${bbox}];relation["waterway"="river"]["name"];out skel qt 600;`);
    const ids = (list.elements || []).filter(e => e.type === 'relation')
      .sort((x, y) => (y.members || []).length - (x.members || []).length).slice(0, 30).map(e => e.id);
    if (!ids.length) return [];
    // pass 2: geometry for just those
    const osm = await post(`[out:json][timeout:90];rel(id:${ids.join(',')});out geom;`);
    const rivers = [];
    (osm.elements || []).forEach(el => {
      if (el.type !== 'relation') return;
      const lines = [];
      (el.members || []).forEach(m => {
        if (m.type !== 'way' || !m.geometry) return;
        if (m.role && !['', 'main_stream', 'outer', 'main'].includes(m.role)) return;
        lines.push(m.geometry.map(g => [g.lon, g.lat]));
      });
      if (lines.length) rivers.push({ name: (el.tags && (el.tags['name:en'] || el.tags.name)) || '', lines });
    });
    return rivers;
  }
  async function loadRivers() {
    const seq = state.seq;
    busy(true, 'Tracing rivers…');
    try {
      let rivers = null;
      const sts = usStates();
      if (sts) {
        // Esri's USA Rivers and Streams, longest named streams in these states
        const list = sts.map(n => `'${esc(n)}'`).join(','), ulist = sts.map(n => `'${esc(n).toUpperCase()}'`).join(',');
        const data = await arcQuery(SRC.usaRivers, {
          where: `Feature='Stream' AND Name IS NOT NULL AND (State IN (${list}) OR UPPER(State) IN (${ulist}))`,
          outFields: 'Name,Miles', orderByFields: 'Miles DESC', resultRecordCount: Math.min(150, 40 + 20 * sts.length),
          returnGeometry: true, outSR: 4326, geometryPrecision: 4, f: 'geojson',
        });
        rivers = linesFromGeoJSON(data.features || [], p => p.Name);
      } else if (state.region.type === 'country') {
        // Esri's World Major Rivers (two public copies), then OpenStreetMap as a fallback
        for (const url of SRC.worldRivers) {
          try {
            const data = await arcQuery(url, { ...envParams(), where: '1=1', outFields: 'NAME', returnGeometry: true, outSR: 4326, geometryPrecision: 4, f: 'geojson' });
            rivers = linesFromGeoJSON(data.features || [], p => p.NAME || p.name);
            if (rivers.length) break;
          } catch (e) { rivers = null; }
        }
        if (!rivers || !rivers.length) rivers = await riversFromOverpass();
      } else {
        rivers = await riversFromOverpass();
      }
      if (seq !== state.seq) return;
      // keep only rivers that actually enter the outline
      rivers = rivers.filter(r => r.lines.some(line => line.some((c, i) => i % 5 === 0 && pointInGeom(c[0], c[1], state.boundary))));
      state.rivers = rivers;
      $('n-rivers').textContent = rivers.length ? `${rivers.length} found` : 'none';
      if (!rivers.length) setStatus('No major rivers were found inside this region.', true);
    } catch (e) { if (seq === state.seq) { state.rivers = []; setStatus('Rivers could not be loaded: ' + e.message, true); } }
    finally { busy(false, 'Tracing rivers…'); render(); }
  }

  async function loadSubdivisions() {
    const seq = state.seq;
    busy(true, 'Loading internal borders…');
    try {
      const data = await arcQuery(SRC.admin, {
        where: `COUNTRY='${esc(state.region.name)}'`, outFields: 'NAME', returnGeometry: true,
        outSR: 4326, geometryPrecision: 4, maxAllowableOffset: 0.01, resultRecordCount: 2000, f: 'geojson',
      });
      if (seq !== state.seq) return;
      const byName = new Map();
      (data.features || []).forEach(f => {
        const n = (f.properties && f.properties.NAME) || '';
        if (!byName.has(n)) byName.set(n, []);
        byName.get(n).push(f);
      });
      const subs = [...byName].map(([name, feats]) => ({ name, geometry: mergeGeoms(feats) })).filter(s => s.geometry);
      state.subdiv = subs;
      $('n-subdiv').textContent = subs.length ? `${subs.length} found` : 'none';
      if (!subs.length) setStatus('No internal borders are available for this country.', true);
    } catch (e) { if (seq === state.seq) { state.subdiv = []; setStatus('Internal borders could not be loaded: ' + e.message, true); } }
    finally { busy(false, 'Loading internal borders…'); render(); }
  }

  // ---------------------------------------------------------------- drawing
  function sheetSize() {
    return state.orient === 'landscape' ? { w: inch(11), h: inch(8.5) } : { w: inch(8.5), h: inch(11) };
  }
  function makeProjection(b, rect) {
    const k = Math.cos((b.minLat + b.maxLat) / 2 * Math.PI / 180);
    const dw = (b.maxLon - b.minLon) * k, dh = (b.maxLat - b.minLat);
    const s = Math.min(rect.w / dw, rect.h / dh);
    const ox = rect.x + (rect.w - dw * s) / 2, oy = rect.y + (rect.h - dh * s) / 2;
    return { s, k, xy: (lon, lat) => [ox + (W(lon) - b.minLon) * k * s, oy + (b.maxLat - lat) * s] };
  }
  function tracePolygon(geom, proj) {
    ctx.beginPath();
    eachRing(geom, ring => {
      ring.forEach(([lon, lat], i) => { const [x, y] = proj.xy(lon, lat); i ? ctx.lineTo(x, y) : ctx.moveTo(x, y); });
      ctx.closePath();
    });
  }
  function star(x, y, r) {
    ctx.beginPath();
    for (let i = 0; i < 10; i++) {
      const a = -Math.PI / 2 + i * Math.PI / 5, rr = i % 2 ? r * 0.45 : r;
      ctx.lineTo(x + Math.cos(a) * rr, y + Math.sin(a) * rr);
    }
    ctx.closePath();
  }
  function fitFont(px, weight, family) { return `${weight} ${px}px ${family}`; }
  const SANS = '"IBM Plex Sans","Helvetica Neue",Arial,sans-serif';
  const COND = '"Barlow Condensed","Arial Narrow",Impact,sans-serif';
  const MONO = '"IBM Plex Mono",Menlo,Consolas,monospace';
  const SERIF = 'Georgia,"Times New Roman",serif';
  const nice = v => { const p = Math.pow(10, Math.floor(Math.log10(v))); const m = v / p; return (m >= 5 ? 5 : m >= 2.5 ? 2.5 : m >= 2 ? 2 : 1) * p; };

  function render() {
    const { w, h } = sheetSize();
    if (canvas.width !== w || canvas.height !== h) { canvas.width = w; canvas.height = h; }
    fitPreview();
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.fillStyle = '#fff'; ctx.fillRect(0, 0, w, h);
    ctx.strokeStyle = '#000'; ctx.fillStyle = '#000'; ctx.lineJoin = 'round'; ctx.lineCap = 'round';

    const margin = inch(0.5);
    const showTitle = ov.title.checked;
    const top = margin + (showTitle ? inch(0.95) : 0);
    const bottom = h - margin - inch(0.55);
    const frame = { x: margin, y: top, w: w - 2 * margin, h: bottom - top };
    const lw = state.weight * DPI / 100;   // boundary line width in px

    // --- title band
    if (showTitle) {
      const name = state.boundary ? regionName() : 'Outline map';
      ctx.textBaseline = 'alphabetic'; ctx.textAlign = 'left';
      // shrink the title until it clears the Name/Date block on the right
      const titleRoom = frame.w - inch(5.4);
      let tsize = 30; ctx.font = fitFont(pt(tsize), 700, COND);
      while (tsize > 16 && ctx.measureText(name.toUpperCase()).width > titleRoom) { tsize -= 1; ctx.font = fitFont(pt(tsize), 700, COND); }
      ctx.fillText(name.toUpperCase(), frame.x, margin + pt(30));
      if (state.boundary) {
        ctx.font = fitFont(pt(9.5), 400, SANS); ctx.fillStyle = '#333';
        const r = state.region, sub = r.type === 'region'
          ? (r.members.length > 8 ? `${r.members.length} states` : r.members.join(' · '))
          : r.formatted;
        ctx.fillText(sub, frame.x, margin + pt(30) + pt(14));
        ctx.fillStyle = '#000';
      }
      // name / date line, right-aligned
      ctx.font = fitFont(pt(10), 500, SANS); ctx.textAlign = 'right';
      const y = margin + pt(30);
      const dateW = inch(1.4), nameW = inch(2.6), gap = inch(0.25);
      ctx.lineWidth = pt(0.8);
      ctx.fillText('Date', frame.x + frame.w - dateW - pt(6), y);
      ctx.beginPath(); ctx.moveTo(frame.x + frame.w - dateW, y + pt(2)); ctx.lineTo(frame.x + frame.w, y + pt(2)); ctx.stroke();
      const nx = frame.x + frame.w - dateW - gap - inch(0.4);
      ctx.fillText('Name', nx - nameW - pt(6), y);
      ctx.beginPath(); ctx.moveTo(nx - nameW, y + pt(2)); ctx.lineTo(nx, y + pt(2)); ctx.stroke();
      ctx.textAlign = 'left';
    }

    // --- neatline
    ctx.lineWidth = pt(1);
    ctx.strokeRect(frame.x, frame.y, frame.w, frame.h);

    if (!state.boundary) {
      ctx.fillStyle = '#9aa5a8'; ctx.textAlign = 'center'; ctx.font = fitFont(pt(13), 400, SANS);
      ctx.fillText('Find a region to draw its outline here.', frame.x + frame.w / 2, frame.y + frame.h / 2);
      ctx.fillStyle = '#000'; ctx.textAlign = 'left';
      drawCredit(frame, h, margin);
      $('scale-out').textContent = '';
      return;
    }

    const inset = inch(0.3);
    const proj = makeProjection(state.bounds, { x: frame.x + inset, y: frame.y + inset, w: frame.w - 2 * inset, h: frame.h - 2 * inset });
    const labels = [];   // placed label rectangles, for collision avoidance
    const placeLabel = (x, y, tw, th) => {
      if (x < frame.x || y < frame.y || x + tw > frame.x + frame.w || y + th > frame.y + frame.h) return false;
      for (const r of labels) if (x < r.x + r.w && x + tw > r.x && y < r.y + r.h && y + th > r.y) return false;
      labels.push({ x, y, w: tw, h: th }); return true;
    };

    ctx.save();
    ctx.beginPath(); ctx.rect(frame.x, frame.y, frame.w, frame.h); ctx.clip();

    // --- graticule
    if (ov.grid.checked) {
      const b = state.bounds, span = Math.max(b.maxLon - b.minLon, b.maxLat - b.minLat);
      const step = [0.25, 0.5, 1, 2, 5, 10, 15, 20, 30].find(s => span / s <= 8) || 30;
      ctx.lineWidth = Math.max(1, lw * 0.18); ctx.setLineDash([pt(3), pt(3)]);
      ctx.font = fitFont(pt(7), 400, MONO); ctx.fillStyle = '#000';
      for (let lon = Math.ceil(b.minLon / step) * step; lon <= b.maxLon; lon += step) {
        const [x] = proj.xy(lon, b.minLat);
        ctx.beginPath(); ctx.moveTo(x, frame.y); ctx.lineTo(x, frame.y + frame.h); ctx.stroke();
        const real = lon > 180 ? lon - 360 : lon;
        ctx.textAlign = 'center'; ctx.textBaseline = 'top';
        ctx.fillText(`${Math.abs(real)}°${real < 0 ? 'W' : real > 0 ? 'E' : ''}`, x, frame.y + pt(3));
      }
      for (let lat = Math.ceil(b.minLat / step) * step; lat <= b.maxLat; lat += step) {
        const [, y] = proj.xy(b.minLon, lat);
        ctx.beginPath(); ctx.moveTo(frame.x, y); ctx.lineTo(frame.x + frame.w, y); ctx.stroke();
        ctx.textAlign = 'left'; ctx.textBaseline = 'bottom';
        ctx.fillText(`${Math.abs(lat)}°${lat < 0 ? 'S' : lat > 0 ? 'N' : ''}`, frame.x + pt(3), y - pt(2));
      }
      ctx.setLineDash([]);
    }

    // --- internal borders
    if (ov.subdiv.checked && state.subdiv && state.subdiv.length) {
      ctx.lineWidth = Math.max(1, lw * 0.4);
      state.subdiv.forEach(s => { tracePolygon(s.geometry, proj); ctx.stroke(); });
    }

    // --- rivers (clipped to the region)
    if (ov.rivers.checked && state.rivers && state.rivers.length) {
      ctx.save();
      tracePolygon(state.boundary, proj); ctx.clip('evenodd');
      ctx.lineWidth = Math.max(1, lw * 0.45);
      state.rivers.forEach(r => {
        ctx.beginPath();
        r.lines.forEach(line => line.forEach(([lon, lat], i) => { const [x, y] = proj.xy(lon, lat); i ? ctx.lineTo(x, y) : ctx.moveTo(x, y); }));
        ctx.stroke();
      });
      ctx.restore();
    }

    // --- region outline (multi-state regions: only the outer edge is drawn thick)
    ctx.lineWidth = lw;
    if (state.outer) {
      ctx.beginPath();
      state.outer.forEach(line => line.forEach(([lon, lat], i) => { const [x, y] = proj.xy(lon, lat); i ? ctx.lineTo(x, y) : ctx.moveTo(x, y); }));
      ctx.stroke();
    } else { tracePolygon(state.boundary, proj); ctx.stroke(); }

    // --- cities & capitals
    const dotR = pt(3.2) * (0.7 + state.weight * 0.1), starR = dotR * 2.1;
    const drawn = [];
    if (state.places && (ov.cities.checked || ov.capitals.checked)) {
      const caps = ov.capitals.checked ? state.places.filter(p => p.capital) : [];
      const rest = state.places.filter(p => !caps.includes(p));
      const cities = ov.cities.checked ? rest.slice(0, state.nCities) : [];
      caps.forEach(p => {
        const [x, y] = proj.xy(p.lon, p.lat);
        const r = p.capital === 'national' ? starR * 1.25 : starR;
        star(x, y, r); ctx.fillStyle = '#fff'; ctx.fill(); ctx.lineWidth = Math.max(1, lw * 0.35); ctx.stroke();
        ctx.fillStyle = '#000';
        if (p.capital === 'national') { star(x, y, r * 0.55); ctx.fill(); }
        drawn.push({ p, x, y, r });
      });
      cities.forEach(p => {
        const [x, y] = proj.xy(p.lon, p.lat);
        ctx.beginPath(); ctx.arc(x, y, dotR, 0, Math.PI * 2); ctx.fill();
        drawn.push({ p, x, y, r: dotR });
      });
    }

    // --- labels
    if (ov.labels.checked) {
      ctx.textBaseline = 'middle';
      // subdivision names first (largest features, lowest priority visually)
      if (ov.subdiv.checked && state.subdiv && state.subdiv.length) {
        ctx.font = fitFont(pt(7.5), 500, SANS); ctx.fillStyle = '#000'; ctx.textAlign = 'center';
        state.subdiv.forEach(s => {
          if (!s.name) return;
          const c = largestRingCentroid(s.geometry); const [x, y] = proj.xy(c[0] > 180 ? c[0] - 360 : c[0], c[1]);
          const t = s.name.toUpperCase(), tw = ctx.measureText(t).width, th = pt(9);
          if (placeLabel(x - tw / 2, y - th / 2, tw, th)) ctx.fillText(t, x, y);
        });
      }
      // city and capital names, next to their markers
      ctx.textAlign = 'left';
      drawn.forEach(({ p, x, y, r }) => {
        const bold = !!p.capital;
        ctx.font = fitFont(pt(bold ? 9.5 : 8.5), bold ? 600 : 400, SANS);
        const tw = ctx.measureText(p.name).width, th = pt(11), pad = r + pt(3);
        const tries = [[x + pad, y - th / 2], [x - pad - tw, y - th / 2], [x - tw / 2, y - pad - th], [x - tw / 2, y + pad]];
        for (const [lx, ly] of tries) {
          if (placeLabel(lx, ly, tw, th)) {
            ctx.fillStyle = '#fff'; ctx.lineWidth = pt(3); ctx.lineJoin = 'round'; ctx.strokeStyle = '#fff';
            ctx.strokeText(p.name, lx, ly + th / 2);
            ctx.fillStyle = '#000'; ctx.strokeStyle = '#000';
            ctx.fillText(p.name, lx, ly + th / 2);
            break;
          }
        }
      });
      // river names, set along the river
      if (ov.rivers.checked && state.rivers && state.rivers.length) {
        ctx.font = `italic 400 ${pt(7.5)}px ${SERIF}`;
        state.rivers.forEach(r => {
          if (!r.name) return;
          // pick the longest projected line, then its middle segment
          let best = null, bestLen = 0;
          r.lines.forEach(line => {
            const pts = line.map(([lon, lat]) => proj.xy(lon, lat));
            let len = 0; for (let i = 1; i < pts.length; i++) len += Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1]);
            if (len > bestLen) { bestLen = len; best = pts; }
          });
          if (!best || best.length < 2) return;
          const tw = ctx.measureText(r.name).width, th = pt(9), n = best.length;
          // try the middle of the river first, then points either side of it
          const spots = [0.5, 0.35, 0.65, 0.2, 0.8].map(f => Math.min(n - 1, Math.floor(n * f)));
          let cx, cy, ang, placed = false;
          for (const i of spots) {
            const a = best[Math.max(0, i - 2)], b = best[Math.min(n - 1, i + 2)];
            ang = Math.atan2(b[1] - a[1], b[0] - a[0]);
            if (ang > Math.PI / 2) ang -= Math.PI; if (ang < -Math.PI / 2) ang += Math.PI;
            [cx, cy] = best[i];
            if (placeLabel(cx - tw / 2, cy - th, tw, th)) { placed = true; break; }
          }
          if (!placed) return;
          ctx.save(); ctx.translate(cx, cy); ctx.rotate(ang);
          ctx.textAlign = 'center';
          ctx.strokeStyle = '#fff'; ctx.lineWidth = pt(3); ctx.strokeText(r.name, 0, -pt(4));
          ctx.fillStyle = '#000'; ctx.fillText(r.name, 0, -pt(4));
          ctx.restore(); ctx.strokeStyle = '#000';
        });
      }
    }
    ctx.restore(); // frame clip

    // --- north arrow (top-right inside the frame)
    {
      const x = frame.x + frame.w - inch(0.4), y = frame.y + inch(0.55), s = inch(0.16);
      ctx.beginPath(); ctx.moveTo(x, y - s); ctx.lineTo(x + s * 0.45, y + s * 0.6); ctx.lineTo(x, y + s * 0.3); ctx.lineTo(x - s * 0.45, y + s * 0.6); ctx.closePath();
      ctx.lineWidth = pt(1); ctx.fillStyle = '#fff'; ctx.fill(); ctx.stroke();
      ctx.beginPath(); ctx.moveTo(x, y - s); ctx.lineTo(x + s * 0.45, y + s * 0.6); ctx.lineTo(x, y + s * 0.3); ctx.closePath(); ctx.fillStyle = '#000'; ctx.fill();
      ctx.font = fitFont(pt(9), 700, SANS); ctx.textAlign = 'center'; ctx.textBaseline = 'bottom';
      ctx.fillText('N', x, y - s - pt(2));
    }

    // --- scale bar
    {
      const mPerPx = 111320 / proj.s;                 // metres per pixel at the map's centre latitude
      const km = nice(inch(1.8) * mPerPx / 1000);      // a round distance ~1.8 in long
      const barPx = km * 1000 / mPerPx, mi = km * 0.621371;
      const x = frame.x, y = frame.y + frame.h + inch(0.22);
      ctx.lineWidth = pt(1); ctx.fillStyle = '#000';
      ctx.fillRect(x, y, barPx / 2, pt(4)); ctx.strokeRect(x, y, barPx, pt(4));
      ctx.font = fitFont(pt(7.5), 400, MONO); ctx.textBaseline = 'bottom';
      ctx.textAlign = 'left'; ctx.fillText('0', x, y - pt(2));
      ctx.textAlign = 'center'; ctx.fillText(`${km % 1 ? km.toFixed(1) : km} km`, x + barPx, y - pt(2));
      ctx.textAlign = 'left'; ctx.textBaseline = 'top';
      ctx.fillText(`≈ ${mi < 10 ? mi.toFixed(1) : Math.round(mi)} miles`, x, y + pt(6));
      const ratio = mPerPx * DPI / 0.0254;
      const rounded = Number(ratio.toPrecision(2)).toLocaleString('en-US');
      ctx.textAlign = 'center'; ctx.textBaseline = 'alphabetic';
      ctx.fillText(`Scale 1 : ${rounded}`, frame.x + frame.w / 2, y + pt(4));
      $('scale-out').textContent = `1 : ${rounded}`;
    }
    drawCredit(frame, h, margin);
    ctx.textAlign = 'left'; ctx.textBaseline = 'alphabetic';
  }

  function drawCredit(frame, h, margin) {
    ctx.font = fitFont(pt(6.5), 400, MONO); ctx.fillStyle = '#444'; ctx.textAlign = 'right'; ctx.textBaseline = 'bottom';
    ctx.fillText('Sources: Esri, Garmin, USGS · © OpenStreetMap contributors', frame.x + frame.w, h - margin);
    ctx.fillStyle = '#000';
  }

  // scale the canvas element to fit the desk without changing its pixel size
  function fitPreview() {
    const desk = canvas.parentElement, aw = desk.clientWidth, ah = desk.clientHeight;
    if (!aw || !ah) { canvas.style.width = '100%'; canvas.style.height = 'auto'; return; }
    const s = Math.min(aw / canvas.width, ah / canvas.height);
    canvas.style.width = Math.floor(canvas.width * s) + 'px';
    canvas.style.height = Math.floor(canvas.height * s) + 'px';
  }

  // ---------------------------------------------------------------- export
  const fileBase = () => `${slug(regionName()) || 'map'}-outline-map`;
  function exportJPG() {
    const a = document.createElement('a');
    a.href = canvas.toDataURL('image/jpeg', 0.92); a.download = fileBase() + '.jpg';
    document.body.appendChild(a); a.click(); a.remove();
    setStatus(`Saved ${fileBase()}.jpg`);
  }
  function exportPDF() {
    if (!window.jspdf) { setStatus('The PDF library did not load. Check your internet connection and reload the page.', true); return; }
    const { jsPDF } = window.jspdf;
    const doc = new jsPDF({ orientation: state.orient, unit: 'in', format: 'letter' });
    const pw = state.orient === 'landscape' ? 11 : 8.5, ph = state.orient === 'landscape' ? 8.5 : 11;
    doc.addImage(canvas.toDataURL('image/jpeg', 0.92), 'JPEG', 0, 0, pw, ph);
    doc.save(fileBase() + '.pdf');
    setStatus(`Saved ${fileBase()}.pdf`);
  }
  function printMap() {
    const url = canvas.toDataURL('image/png');
    const win = window.open('', '_blank');
    if (!win) { setStatus('The print window was blocked. Allow pop-ups for this page and try again.', true); return; }
    win.document.write(`<!doctype html><html><head><title>${regionName() || 'Outline map'}</title>
      <style>@page{size:letter ${state.orient};margin:0}html,body{margin:0;background:#fff}img{width:100%;height:auto;display:block}</style></head>
      <body><img src="${url}" onload="setTimeout(function(){window.focus();window.print();},250)"></body></html>`);
    win.document.close();
  }

  // ---------------------------------------------------------------- wiring
  $('overlays-toggle').addEventListener('click', () => {
    const btn = $('overlays-toggle'), open = btn.getAttribute('aria-expanded') !== 'true';
    btn.setAttribute('aria-expanded', open);
    $('overlays').classList.toggle('collapsed', !open);
  });
  $('find').addEventListener('click', findRegion);
  $('q').addEventListener('keydown', e => { if (e.key === 'Enter') findRegion(); });
  Object.values(ov).forEach(cb => cb.addEventListener('change', () => {
    $('cities-field').classList.toggle('hidden', !ov.cities.checked);
    refreshOverlays();
  }));
  $('weight').addEventListener('input', e => { state.weight = +e.target.value; $('weight-out').textContent = e.target.value; render(); });
  $('ncities').addEventListener('input', e => { state.nCities = +e.target.value; $('ncities-out').textContent = e.target.value; render(); });
  $('orient').addEventListener('click', e => {
    const b = e.target.closest('button'); if (!b) return;
    state.orient = b.dataset.o;
    [...$('orient').children].forEach(c => c.classList.toggle('on', c === b));
    render();
  });
  $('jpg').addEventListener('click', exportJPG);
  $('pdf').addEventListener('click', exportPDF);
  $('print').addEventListener('click', printMap);
  window.addEventListener('resize', fitPreview);
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(render);
  render();
})();
