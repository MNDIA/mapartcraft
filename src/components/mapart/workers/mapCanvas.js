// eslint-disable-next-line import/no-anonymous-default-export
// eslint-disable-next-line no-restricted-globals

export default function MapWorker (args) {

var coloursJSON;
var MapModes;
var WhereSupportBlocksModes;
var ColourMethods;
var DitherMethods;
var canvasImageData;
var selectedBlocks;
var disabledTones;
var optionValue_modeNBTOrMapdat;
var optionValue_mapSize_x;
var optionValue_mapSize_y;
var optionValue_staircasing;
var optionValue_whereSupportBlocks;
var optionValue_transparency;
var optionValue_transparencyTolerance;
var optionValue_betterColour;
var optionValue_dithering;
var optionValue_dithering_propagation_red;
var optionValue_dithering_propagation_green;
var optionValue_dithering_propagation_blue;

var colourSetsToUse = []; // colourSetIds and shades to use in map
var exactColourCache = new Map(); // for mapping RGB that exactly matches in coloursJSON to colourSetId and tone
var nearestColourCache = new Map(); // RGB -> index of the closest palette entry
var nearestPairCache = new Map(); // RGB -> the closest two palette entries, which ordered dithering picks between
var paletteEntries = []; // flat [{colourSetId, tone, rgb}] view of colourSetsToUse
var paletteCoords = null; // Float64Array, 3 colour-space coordinates per palette entry
var paletteDitherCoords = null; // Float64Array, 3 dither-space coordinates per palette entry
var pixelPaletteIndex = null; // Int32Array, chosen palette entry per pixel (-1 = transparent)
var labCache = new Map();
var lab50Cache = new Map();
var lab65Cache = new Map();
var hctCache = new Map();

var maps = [];

let alphaColorIdx = 61;

/*
  'maps' is a matrix with entries accessable via maps[z][x], each of which corresponds to a 128x128 map. A typical entry is:
  { materials: {}, supportBlockCount: 128 }
  'materials' is a dictionary with keys corresponding to colourSetIds and entries being the number of blocks from this colourSet required to make the map.
*/

// rgb2lab conversion based on the one from redstonehelper's program
// Note the L* axis comes out scaled by 2.55, i.e. on a 0-255 range rather than
// 0-100, so lightness carries ~2.55x the weight of a* and b* in the metric.
// That is deliberate and long-standing: for mapart, lightness is height.
function rgb2labF(r, g, b) {
  let r1 = r / 255.0;
  let g1 = g / 255.0;
  let b1 = b / 255.0;

  r1 = 0.04045 >= r1 ? (r1 /= 12.0) : Math.pow((r1 + 0.055) / 1.055, 2.4);
  g1 = 0.04045 >= g1 ? (g1 /= 12.0) : Math.pow((g1 + 0.055) / 1.055, 2.4);
  b1 = 0.04045 >= b1 ? (b1 /= 12.0) : Math.pow((b1 + 0.055) / 1.055, 2.4);
  let f = (0.43605202 * r1 + 0.3850816 * g1 + 0.14308742 * b1) / 0.964221,
    h = 0.22249159 * r1 + 0.71688604 * g1 + 0.060621485 * b1,
    k = (0.013929122 * r1 + 0.097097 * g1 + 0.7141855 * b1) / 0.825211,
    l = 0.008856452 < h ? Math.pow(h, 1 / 3) : (903.2963 * h + 16.0) / 116.0,
    m = 500.0 * ((0.008856452 < f ? Math.pow(f, 1 / 3) : (903.2963 * f + 16.0) / 116.0) - l),
    n = 200.0 * (l - (0.008856452 < k ? Math.pow(k, 1 / 3) : (903.2963 * k + 16.0) / 116.0));

  return [2.55 * (116.0 * l - 16.0) + 0.5, m + 0.5, n + 0.5];
}

function rgb2lab(rgb) {
  let val = (rgb[0] << 16) + (rgb[1] << 8) + rgb[2];
  if (labCache.has(val)) return labCache.get(val);
  const lab = rgb2labF(rgb[0], rgb[1], rgb[2]);
  labCache.set(val, lab);
  return lab;
}

//Code based on culori.js - https://culorijs.org/

function labF(y) {
  return (0.00885645167903563081717167575546 < y ? Math.cbrt(y) : (903.2962962962962962962962962963 * y + 16) / 116);
}

function rgb2lab50F(red, green, blue) {
  // sRGB must be linearised before the XYZ matrix is applied, otherwise this is not L*a*b* at all
  let r1 = linearized(red);
  let g1 = linearized(green);
  let b1 = linearized(blue);

  let x = (0.436065742824811 * r1 + 0.3851514688337912 * g1 + 0.14307845442264197 * b1) / 0.96429567642956764295676429567643,
    y = 0.22249319175623702 * r1 + 0.7168870538238823 * g1 + 0.06061979053616537 * b1,
    z = (0.013923904500943465 * r1 + 0.09708128566574634 * g1 + 0.7140993584005155 * b1) / 0.82510460251046025104602510460251;
  let f1 = labF(y);

  let l = 116 * f1 - 16;
  let a = 0;
  let b = 0;

  if (r1 !== g1 || g1 !== b1) {
    let f0 = (0.00885645167903563081717167575546 < x ? Math.cbrt(x) : (903.2962962962962962962962962963 * x + 16) / 116);
    let f2 = (0.00885645167903563081717167575546 < z ? Math.cbrt(z) : (903.2962962962962962962962962963 * z + 16) / 116);
    a = 500 * (f0 - f1);
    b = 200 * (f1 - f2);
  }

  return [l, a, b];
}

function rgb2lab50(rgb) {
  let val = (rgb[0] << 16) + (rgb[1] << 8) + rgb[2];
  if (lab50Cache.has(val)) return lab50Cache.get(val);
  const lab50 = rgb2lab50F(rgb[0], rgb[1], rgb[2]);
  lab50Cache.set(val, lab50);
  return lab50;
}

//Code based on culori.js - https://culorijs.org/
function rgb2lab65F(red, green, blue) {
  // sRGB must be linearised before the XYZ matrix is applied, otherwise this is not L*a*b* at all
  let r1 = linearized(red);
  let g1 = linearized(green);
  let b1 = linearized(blue);

  let x = (0.4123907992659593 * r1 + 0.357584339383878 * g1 + 0.1804807884018343 * b1) / 0.95045592705167173252279635258359,
    y = 0.2126390058715102 * r1 + 0.715168678767756 * g1 + 0.0721923153607337 * b1,
    z = (0.0193308187155918 * r1 + 0.119194779794626 * g1 + 0.9505321522496607 * b1) / 1.0890577507598784194528875379939;
  let f1 = labF(y);

  let l = 116 * f1 - 16;
  let a = 0;
  let b = 0;

  if (r1 !== g1 || g1 !== b1) {
    let f0 = (0.00885645167903563081717167575546 < x ? Math.cbrt(x) : (903.2962962962962962962962962963 * x + 16) / 116);
    let f2 = (0.00885645167903563081717167575546 < z ? Math.cbrt(z) : (903.2962962962962962962962962963 * z + 16) / 116);
    a = 500 * (f0 - f1);
    b = 200 * (f1 - f2);
  }

  return [l, a, b];
}

function rgb2lab65(rgb) {
  let val = (rgb[0] << 16) + (rgb[1] << 8) + rgb[2];
  if (lab65Cache.has(val)) return lab65Cache.get(val);
  const lab65 = rgb2lab65F(rgb[0], rgb[1], rgb[2]);
  lab65Cache.set(val, lab65);
  return lab65;
}

//Code based on material-foundation - https://github.com/material-foundation/material-color-utilities
function linearized(channel) {
  const normalized = channel / 255.0;
  if (normalized <= 0.040449936) {
    return normalized / 12.92;
  } else {
    return Math.pow((normalized + 0.055) / 1.055, 2.4); //NOT multiplied by 100.0
  }
}

function signum(num) {
  if (num < 0) {
    return -1;
  } else if (num > 0) {
    return 1;
  } else {
    return 0;
  }
}

function rgb2xyz(rgb) {
  const r1 = linearized(rgb[0]);
  const g1 = linearized(rgb[1]);
  const b1 = linearized(rgb[2]);

  const x = 0.41233895 * r1 + 0.35762064 * g1 + 0.18051042 * b1;
  const y = 0.2126 * r1 + 0.7152 * g1 + 0.0722 * b1;
  const z = 0.01932141 * r1 + 0.11916382 * g1 + 0.95034478 * b1;

  return [x, y, z]; // NOT multiplied by 100.0
}

function rgb2hctF(red, green, blue) {
  const xyz = rgb2xyz([red, green, blue]);
  const x = xyz[0];
  const y = xyz[1];
  const z = xyz[2];

  const rD = (0.401288 * x + 0.650173 * y - 0.051461 * z) * 1.0211777027575200;
  const gD = (-0.250268 * x + 1.204414 * y + 0.045854 * z) * 0.98630772942801237;
  const bD = (-0.002079 * x + 0.048952 * y + 0.953127 * z) * 0.93396050828022992;

  const rAF = Math.pow((0.38848145378003529 * Math.abs(rD)) / 100.0, 0.42);
  const gAF = Math.pow((0.38848145378003529 * Math.abs(gD)) / 100.0, 0.42);
  const bAF = Math.pow((0.38848145378003529 * Math.abs(bD)) / 100.0, 0.42);

  const rA = (signum(rD) * 400.0 * rAF) / (rAF + 27.13);
  const gA = (signum(gD) * 400.0 * gAF) / (gAF + 27.13);
  const bA = (signum(bD) * 400.0 * bAF) / (bAF + 27.13);

  const a = (11.0 * rA + -12.0 * gA + bA) / 11.0;
  const b = (rA + gA - 2.0 * bA) / 9.0;
  const u = (20.0 * rA + 20.0 * gA + 21.0 * bA) / 20.0;
  const p2 = (40.0 * rA + 20.0 * gA + bA) / 20.0;

  const atan2 = Math.atan2(b, a);
  const atanDegrees = (atan2 * 180.0) / Math.PI;
  const hue = atanDegrees < 0 ? atanDegrees + 360.0 :
      atanDegrees >= 360 ? atanDegrees - 360.0 : atanDegrees;
  const hueRadians = (hue * Math.PI) / 180.0;

  const j = 100.0 * Math.pow(p2 * 0.03391879108791669, 1.3173270022537198);
  const huePrime = hue < 20.14 ? hue + 360 : hue;
  const p1 = 3911.227617099521 * 0.25 * (Math.cos((huePrime * Math.PI) / 180.0 + 2.0) + 3.8);
  const t = (p1 * Math.sqrt(a * a + b * b)) / (u + 0.305);
  const alpha = Math.pow(t, 0.9) * 0.8834525670408592;

  const m = alpha * Math.sqrt(j / 100.0) * 0.78948261793049368;
  const mstar = 43.859649122807014 * Math.log(1.0 + 0.0228 * m);

  const astar = mstar * Math.cos(hueRadians);
  const bstar = mstar * Math.sin(hueRadians);
  const Lstar = 116.0 * labF(y) - 16.0;

  return [Lstar, astar, bstar];
}

function rgb2hct(rgb) {
  const val = (rgb[0] << 16) + (rgb[1] << 8) + rgb[2];
  if (hctCache.has(val)) return hctCache.get(val);
  const hct = rgb2hctF(rgb[0], rgb[1], rgb[2]);
  hctCache.set(val, hct);
  return hct;
}

// ---------------------------------------------------------------------------
// Colour-space handling
//
// Every colour method used here maps an sRGB triplet onto a *rectangular*
// 3-vector (L*a*b*, a scaled L*a*b*, HCT's L*/a*/b* form, or plain RGB).
// That matters for dithering: error diffusion needs a space in which
// differences are meaningful and additive, so we carry the dither error in
// exactly the same space the colour metric is defined on.
//
// This mirrors SlopeCraft's imageConvert.hpp, which keeps its `dither_c3`
// accumulator in the working colour space rather than in 8-bit sRGB.
// ---------------------------------------------------------------------------

function isCiede2000Method(methodUniqueId) {
  return methodUniqueId === ColourMethods.Ciede2000_Lab50.uniqueId || methodUniqueId === ColourMethods.Ciede2000_Lab65.uniqueId;
}

// Maps an 8-bit RGB triplet into the coordinates of the currently selected colour method.
function colourToSpace(rgb) {
  switch (optionValue_betterColour) {
    case ColourMethods.MapartCraftDefault.uniqueId:
      return rgb2lab(rgb);
    case ColourMethods.Cie76_Lab50.uniqueId:
    case ColourMethods.Ciede2000_Lab50.uniqueId:
      return rgb2lab50(rgb);
    case ColourMethods.Cie76_Lab65.uniqueId:
    case ColourMethods.Ciede2000_Lab65.uniqueId:
      return rgb2lab65(rgb);
    case ColourMethods.Hct.uniqueId:
      return rgb2hct(rgb);
    default:
      // Euclidian, and the GA converter's final pass
      return [rgb[0], rgb[1], rgb[2]];
  }
}

// As colourToSpace, but for a continuous sRGB triplet: no cache, no rounding.
function colourToSpaceF(r, g, b) {
  switch (optionValue_betterColour) {
    case ColourMethods.MapartCraftDefault.uniqueId:
      return rgb2labF(r, g, b);
    case ColourMethods.Cie76_Lab50.uniqueId:
    case ColourMethods.Ciede2000_Lab50.uniqueId:
      return rgb2lab50F(r, g, b);
    case ColourMethods.Cie76_Lab65.uniqueId:
    case ColourMethods.Ciede2000_Lab65.uniqueId:
      return rgb2lab65F(r, g, b);
    case ColourMethods.Hct.uniqueId:
      return rgb2hctF(r, g, b);
    default:
      return [r, g, b];
  }
}

// ---------------------------------------------------------------------------
// Dither space
//
// The space the diffused quantisation error accumulates in. It is deliberately
// NOT the colour metric's space: error diffusion works by preserving the local
// *mean*, and a mean is only preserved under a linear map. Accumulating error
// in L*a*b* (as SlopeCraft's imageConvert.hpp does, carrying `dither_c3` in
// whichever space the metric uses) preserves the mean of L*a*b* instead, which
// on smooth mid-tone ramps shifts the mean the viewer actually sees, because
// L* is a cube root of luminance.
//
// Light is what physically averages when a mapart is seen from a distance or
// downscaled, so the error is accumulated in linear light. Choosing the
// nearest colour stays fully perceptual: the accumulated value is converted
// back to sRGB and handed to the selected colour metric.
// ---------------------------------------------------------------------------

// Inverse of linearized(): linear light in [0, 1] back to sRGB on 0-255.
function delinearized(value) {
  const clamped = value <= 0 ? 0 : value >= 1 ? 1 : value;
  if (clamped <= 0.0031308) {
    return clamped * 12.92 * 255.0;
  }
  return (1.055 * Math.pow(clamped, 1.0 / 2.4) - 0.055) * 255.0;
}

// "linear" accumulates error in linear light, "srgb" in gamma-encoded sRGB.
const DITHER_SPACE = "linear";

function clampDitherSpace(value) {
  const top = DITHER_SPACE === "srgb" ? 255 : 1;
  return value <= 0 ? 0 : value >= top ? top : value;
}

function rgbToDitherSpace(r, g, b) {
  if (DITHER_SPACE === "srgb") {
    return [r, g, b];
  }
  return [linearized(r), linearized(g), linearized(b)];
}

function ditherSpaceToRgb(d0, d1, d2) {
  if (DITHER_SPACE === "srgb") {
    return [d0, d1, d2];
  }
  return [delinearized(d0), delinearized(d1), delinearized(d2)];
}

// x^7, as four multiplications. CIEDE2000 needs it twice per comparison and
// Math.pow is far slower than the chain for a fixed small integer exponent.
function pow7(x) {
  const x2 = x * x;
  const x3 = x2 * x;
  return x3 * x3 * x;
}

const POW_25_7 = 6103515625; // 25^7

// CIEDE2000 between two points that are *already* in L*a*b*. `cStd`, the chroma
// of the first point, is passed in by the palette search, which hoists it out
// of its loop; it is derived here when omitted.
// Code based on culori.js - https://culorijs.org/
function ciede2000InLab(lStd, aStd, bStd, lSmp, aSmp, bSmp, cStdIn) {
  let cStd = cStdIn === undefined ? Math.sqrt(aStd * aStd + bStd * bStd) : cStdIn;
  let cSmp = Math.sqrt(aSmp * aSmp + bSmp * bSmp);
  let cAvg = (cStd + cSmp) / 2;

  let cAvgPow7 = pow7(cAvg);
  let G = 0.5 * (1 - Math.sqrt(cAvgPow7 / (cAvgPow7 + POW_25_7)));

  let apStd = aStd * (1 + G);
  let apSmp = aSmp * (1 + G);

  let cpStd = Math.sqrt(apStd * apStd + bStd * bStd);
  let cpSmp = Math.sqrt(apSmp * apSmp + bSmp * bSmp);

  let hpStd = Math.abs(apStd) + Math.abs(bStd) === 0 ? 0 : Math.atan2(bStd, apStd);
  hpStd += (hpStd < 0) * 2 * Math.PI;

  let hpSmp = Math.abs(apSmp) + Math.abs(bSmp) === 0 ? 0 : Math.atan2(bSmp, apSmp);
  hpSmp += (hpSmp < 0) * 2 * Math.PI;

  let dL = lSmp - lStd;
  let dC = cpSmp - cpStd;

  let cpStdtimescpSmpZero = cpStd === 0 && cpSmp === 0;
  let dhp = cpStdtimescpSmpZero ? 0 : hpSmp - hpStd;
  dhp -= (dhp > Math.PI) * 2 * Math.PI;
  dhp += (dhp < -Math.PI) * 2 * Math.PI;

  let dH = 2 * Math.sqrt(cpStd * cpSmp) * Math.sin(dhp / 2);

  let Lp = (lStd + lSmp) / 2;
  let Cp = (cpStd + cpSmp) / 2;

  let hp;
  if (cpStdtimescpSmpZero) {
    hp = hpStd + hpSmp;
  } else {
    hp = (hpStd + hpSmp) / 2;
    hp -= (Math.abs(hpStd - hpSmp) > Math.PI) * Math.PI;
    hp += (hp < 0) * 2 * Math.PI;
  }

  let Lpminus50 = Lp - 50;
  let Lpm50 = Lpminus50 * Lpminus50;
  let T =
    1 -
    0.17 * Math.cos(hp - Math.PI / 6) +
    0.24 * Math.cos(2 * hp) +
    0.32 * Math.cos(3 * hp + Math.PI / 30) -
    0.2 * Math.cos(4 * hp - (63 * Math.PI) / 180);

  let Sl = 1 + (0.015 * Lpm50) / Math.sqrt(20 + Lpm50);
  let Sc = 1 + 0.045 * Cp;
  let Sh = 1 + 0.015 * Cp * T;

  const hpOffset = ((180 / Math.PI) * hp - 275) / 25;
  let deltaTheta = ((30 * Math.PI) / 180) * Math.exp(-1 * (hpOffset * hpOffset));
  const CpPow7 = pow7(Cp);
  let Rc = 2 * Math.sqrt(CpPow7 / (CpPow7 + POW_25_7));

  let Rt = -1 * Math.sin(2 * deltaTheta) * Rc;

  let dLdivSl = dL / Sl;
  let dCdivSc = dC / Sc;
  let dHdivSh = dH / Sh;
  return dLdivSl * dLdivSl + dCdivSc * dCdivSc + dHdivSh * dHdivSh + (((Rt * dC) / Sc) * dH) / Sh;
}

// Distance between two points that are already in the active colour space.
function metricDistanceInSpace(x0, x1, x2, y0, y1, y2) {
  if (isCiede2000Method(optionValue_betterColour)) {
    return ciede2000InLab(x0, x1, x2, y0, y1, y2);
  }
  const d0 = x0 - y0;
  const d1 = x1 - y1;
  const d2 = x2 - y2;
  return d0 * d0 + d1 * d1 + d2 * d2;
}

// ---------------------------------------------------------------------------
// Flat palette
//
// colourSetsToUse is a nested {colourSetId -> {tone -> rgb}} structure; the
// quantiser wants a flat, index-addressable list whose colour-space
// coordinates are computed exactly once instead of on every pixel comparison.
// ---------------------------------------------------------------------------

function setupPalette() {
  paletteEntries = [];
  colourSetsToUse.forEach((colourSet) => {
    Object.keys(colourSet.tonesRGB).forEach((toneKey) => {
      paletteEntries.push({
        colourSetId: colourSet.colourSetId,
        tone: toneKey,
        rgb: colourSet.tonesRGB[toneKey],
      });
    });
  });

  paletteCoords = new Float64Array(paletteEntries.length * 3);
  paletteDitherCoords = new Float64Array(paletteEntries.length * 3);
  for (let i = 0; i < paletteEntries.length; i++) {
    const rgb = paletteEntries[i].rgb;
    const coords = colourToSpace(rgb);
    paletteCoords[i * 3] = coords[0];
    paletteCoords[i * 3 + 1] = coords[1];
    paletteCoords[i * 3 + 2] = coords[2];
    const ditherCoords = rgbToDitherSpace(rgb[0], rgb[1], rgb[2]);
    paletteDitherCoords[i * 3] = ditherCoords[0];
    paletteDitherCoords[i * 3 + 1] = ditherCoords[1];
    paletteDitherCoords[i * 3 + 2] = ditherCoords[2];
  }
}

// Nearest palette entry to a point already expressed in the active colour space.
//
// Both branches scan the whole palette. Shortlisting the palette by plain
// L*a*b* distance and scoring only the shortlist with CIEDE2000 is tempting and
// several times faster, but it is not equivalent: CIEDE2000's chroma and hue
// weighting lets a colour that is not among the sixteen nearest in L*a*b* still
// win, which measurably changes around 1.6% of pixels.
function nearestPaletteIndexInSpace(v0, v1, v2) {
  const n = paletteEntries.length;
  let bestIdx = -1;
  let bestDist = Infinity;

  if (isCiede2000Method(optionValue_betterColour)) {
    // The source point's chroma does not vary over the palette, so it is
    // computed once here rather than once per comparison.
    const cStd = Math.sqrt(v1 * v1 + v2 * v2);
    for (let i = 0; i < n; i++) {
      const dist = ciede2000InLab(v0, v1, v2, paletteCoords[i * 3], paletteCoords[i * 3 + 1], paletteCoords[i * 3 + 2], cStd);
      if (dist < bestDist) {
        bestDist = dist;
        bestIdx = i;
      }
    }
    return bestIdx;
  }

  for (let i = 0; i < n; i++) {
    const d0 = paletteCoords[i * 3] - v0;
    const d1 = paletteCoords[i * 3 + 1] - v1;
    const d2 = paletteCoords[i * 3 + 2] - v2;
    const dist = d0 * d0 + d1 * d1 + d2 * d2;
    if (dist < bestDist) {
      bestDist = dist;
      bestIdx = i;
    }
  }
  return bestIdx;
}

// The closest two palette entries to a point already expressed in the active
// colour space. Ordered dithering alternates between them on a fixed lattice,
// so it needs the runner-up and both distances, not just the winner.
function nearestPaletteIndexPairInSpace(v0, v1, v2) {
  const n = paletteEntries.length;
  let nearestIndex = -1;
  let nearestDistance = Infinity;
  let runnerUpIndex = -1;
  let runnerUpDistance = Infinity;
  for (let i = 0; i < n; i++) {
    const dist = metricDistanceInSpace(v0, v1, v2, paletteCoords[i * 3], paletteCoords[i * 3 + 1], paletteCoords[i * 3 + 2]);
    if (dist < nearestDistance) {
      runnerUpDistance = nearestDistance;
      runnerUpIndex = nearestIndex;
      nearestDistance = dist;
      nearestIndex = i;
    } else if (dist < runnerUpDistance) {
      runnerUpDistance = dist;
      runnerUpIndex = i;
    }
  }
  if (runnerUpIndex === -1) {
    // a single-entry palette: there is nothing to alternate with
    runnerUpIndex = nearestIndex;
    runnerUpDistance = nearestDistance;
  } else {
    // If the two candidates are closer to each other than the runner-up is to
    // the source pixel, mixing them buys nothing but noise; collapse to the best.
    const nearest = nearestIndex * 3;
    const runnerUp = runnerUpIndex * 3;
    const between = metricDistanceInSpace(
      paletteCoords[nearest],
      paletteCoords[nearest + 1],
      paletteCoords[nearest + 2],
      paletteCoords[runnerUp],
      paletteCoords[runnerUp + 1],
      paletteCoords[runnerUp + 2]
    );
    if (between <= runnerUpDistance) {
      runnerUpIndex = nearestIndex;
      runnerUpDistance = nearestDistance;
    }
  }
  return { nearestIndex, nearestDistance, runnerUpIndex, runnerUpDistance };
}

// RGB-keyed cached wrappers, used where the input really is an 8-bit pixel
// (undithered pass, ordered dithers, GA seeding).
function nearestPaletteIndexFor(pixelRGB) {
  const RGBBinary = (pixelRGB[0] << 16) + (pixelRGB[1] << 8) + pixelRGB[2];
  const cached = nearestColourCache.get(RGBBinary);
  if (cached !== undefined) {
    return cached;
  }
  const c = colourToSpace(pixelRGB);
  const idx = nearestPaletteIndexInSpace(c[0], c[1], c[2]);
  nearestColourCache.set(RGBBinary, idx);
  return idx;
}


function nearestPaletteIndexPairFor(pixelRGB) {
  const RGBBinary = (pixelRGB[0] << 16) + (pixelRGB[1] << 8) + pixelRGB[2];
  const cached = nearestPairCache.get(RGBBinary);
  if (cached !== undefined) {
    return cached;
  }
  const c = colourToSpace(pixelRGB);
  const result = nearestPaletteIndexPairInSpace(c[0], c[1], c[2]);
  nearestPairCache.set(RGBBinary, result);
  return result;
}

function setupColourSetsToUse() {
  let colourSetIdsToUse = []; // get selected colour sets
  Object.keys(selectedBlocks).forEach((key) => {
    if (selectedBlocks[key] !== "-1") {
      colourSetIdsToUse.push(key);
    }
  });

  // now get appropriate shades
  const toneKeys = Object.values(Object.values(MapModes).find((mapMode) => mapMode.uniqueId === optionValue_modeNBTOrMapdat).staircaseModes).find(
    (staircaseMode) => staircaseMode.uniqueId === optionValue_staircasing
  ).toneKeys;

  for (const colourSetId of colourSetIdsToUse) {
    let tonesRGB = {};
    for (const toneKey of toneKeys) {
      if (disabledTones[colourSetId].has(toneKey))
        continue;

      tonesRGB[toneKey] = coloursJSON[colourSetId].tonesRGB[toneKey];
    }

    if (Object.keys(tonesRGB).length === 0)
      continue;

    colourSetsToUse.push({
      colourSetId: colourSetId,
      tonesRGB: tonesRGB,
    });
  }
}

function setupExactColourCache() {
  // we do not care what staircasing option is selected etc as this does not matter
  // this is for exactly matching colours, whose values are never repeated in coloursJSON
  for (const [colourSetId, colourSet] of Object.entries(coloursJSON)) {
    for (const [toneKey, toneRGB] of Object.entries(colourSet.tonesRGB)) {
      const RGBBinary = (toneRGB[0] << 16) + (toneRGB[1] << 8) + toneRGB[2];
      exactColourCache.set(RGBBinary, {
        colourSetId: colourSetId,
        tone: toneKey,
      });
    }
  }
}

function exactRGBToColourSetIdAndTone(pixelRGB) {
  const RGBBinary = (pixelRGB[0] << 16) + (pixelRGB[1] << 8) + pixelRGB[2];
  return exactColourCache.get(RGBBinary);
}

function isSupportBlockMandatoryForColourSetIdAndTone(colourSetIdAndTone) {
  return coloursJSON[colourSetIdAndTone.colourSetId].blocks[selectedBlocks[colourSetIdAndTone.colourSetId]].supportBlockMandatory;
}

function getMapartImageDataAndMaterials() {
  for (let y = 0; y < optionValue_mapSize_y; y++) {
    let mapsRowToAdd = [];
    for (let x = 0; x < optionValue_mapSize_x; x++) {
      let mapEntryToAdd = { materials: {}, supportBlockCount: 0 };
      colourSetsToUse.forEach((colourSet) => {
        mapEntryToAdd.materials[colourSet.colourSetId] = 0;
      });
      mapsRowToAdd.push(mapEntryToAdd);
    }
    maps.push(mapsRowToAdd);
  }

  if (colourSetsToUse.length === 0) {
    return;
  }

  if (optionValue_modeNBTOrMapdat === MapModes.SCHEMATIC_NBT.uniqueId) {
    maps.forEach((row) =>
      row.forEach((map) => {
        map.supportBlockCount = 128; // initialise with noobline count
      })
    );
  }

  if (optionValue_betterColour === ColourMethods.GaCvter.uniqueId) {
    runGaConverter();
  } else {
    quantiseImage();
  }

  // -------------------------------------------------------------------------
  // Materials and support-block accounting.
  //
  // Runs as a second pass in raster order: the quantiser may walk rows
  // backwards (serpentine dithering), and this pass reads the already-decided
  // colours of the pixels to the north, so it cannot be interleaved with it.
  // -------------------------------------------------------------------------
  for (let i = 0; i < canvasImageData.data.length; i += 4) {
    const indexA = i + 3;

    const multimapWidth = optionValue_mapSize_x * 128;
    const multimap_x = (i / 4) % multimapWidth;
    const multimap_y = (i / 4 - multimap_x) / multimapWidth;
    const whichMap_x = Math.floor(multimap_x / 128);
    const whichMap_y = Math.floor(multimap_y / 128);
    const individualMap_y = multimap_y % 128;

    const paletteIndex = pixelPaletteIndex[i / 4];
    if (paletteIndex < 0) {
      continue; // fully transparent mapdat pixel: no block, no material
    }
    const closestColourSetIdAndTone = paletteEntries[paletteIndex];
      if (canvasImageData.data[indexA] !== 0) {
        // support-block count: mapdat can skip this
        if (optionValue_modeNBTOrMapdat === MapModes.SCHEMATIC_NBT.uniqueId) {
          switch (optionValue_whereSupportBlocks) {
            case WhereSupportBlocksModes.NONE.uniqueId: {
              break;
            }
            case WhereSupportBlocksModes.IMPORTANT.uniqueId: {
              if (isSupportBlockMandatoryForColourSetIdAndTone(closestColourSetIdAndTone)) {
                maps[whichMap_y][whichMap_x].supportBlockCount += 1;
              }
              break;
            }
            case WhereSupportBlocksModes.ALL_OPTIMIZED.uniqueId: {
              // for AllOptimized and AllDoubleOptimized we need to know the block south's y-position / does it need support to be able to determine
              // whether a block needs support underneath; hence we do add support blocks '1-cycle behind' in the for-loop
              switch (individualMap_y) {
                case 0: {
                  // we now know about the first block in the column which allows us to determine noobline support blocks
                  if (
                    // first under-support block
                    closestColourSetIdAndTone.tone === "dark" ||
                    (closestColourSetIdAndTone.tone === "normal" && isSupportBlockMandatoryForColourSetIdAndTone(closestColourSetIdAndTone))
                  ) {
                    maps[whichMap_y][whichMap_x].supportBlockCount += 1;
                  }
                  if (
                    // second under-support block
                    closestColourSetIdAndTone.tone === "dark" &&
                    isSupportBlockMandatoryForColourSetIdAndTone(closestColourSetIdAndTone)
                  ) {
                    maps[whichMap_y][whichMap_x].supportBlockCount += 1;
                  }
                  break;
                }
                case 1: {
                  // first block in column; special since noobline to the North
                  const coloursBlock0_index = i - 4 * 128 * optionValue_mapSize_x; //exactRGBToColourSetIdAndTone
                  const coloursBlock0 = exactRGBToColourSetIdAndTone([
                    canvasImageData.data[coloursBlock0_index],
                    canvasImageData.data[coloursBlock0_index + 1],
                    canvasImageData.data[coloursBlock0_index + 2],
                  ]);
                  if (
                    // first under-support block
                    coloursBlock0.tone === "light" ||
                    closestColourSetIdAndTone.tone === "dark" ||
                    (closestColourSetIdAndTone.tone === "normal" && isSupportBlockMandatoryForColourSetIdAndTone(closestColourSetIdAndTone)) ||
                    isSupportBlockMandatoryForColourSetIdAndTone(coloursBlock0)
                  ) {
                    maps[whichMap_y][whichMap_x].supportBlockCount += 1;
                  }
                  if (
                    // second under-support block
                    closestColourSetIdAndTone.tone === "dark" &&
                    isSupportBlockMandatoryForColourSetIdAndTone(closestColourSetIdAndTone)
                  ) {
                    maps[whichMap_y][whichMap_x].supportBlockCount += 1;
                  }
                  break;
                }
                case 127: {
                  // falls through
                  // special case 127 also accounts for final block in column since we are 1-cycle behind in out for-loop; no lookahead.
                  // falls through to default case to also account for block 126 as expected too
                  const penultimateColoursBlock_index = i - 4 * 128 * optionValue_mapSize_x;
                  const penultimateColoursBlock = exactRGBToColourSetIdAndTone([
                    canvasImageData.data[penultimateColoursBlock_index],
                    canvasImageData.data[penultimateColoursBlock_index + 1],
                    canvasImageData.data[penultimateColoursBlock_index + 2],
                  ]);
                  if (
                    // first under-support block
                    closestColourSetIdAndTone.tone === "light" ||
                    isSupportBlockMandatoryForColourSetIdAndTone(closestColourSetIdAndTone) ||
                    (closestColourSetIdAndTone.tone === "normal" && isSupportBlockMandatoryForColourSetIdAndTone(penultimateColoursBlock))
                  ) {
                    maps[whichMap_y][whichMap_x].supportBlockCount += 1;
                  }
                  if (
                    // second under-support block
                    closestColourSetIdAndTone.tone === "light" &&
                    isSupportBlockMandatoryForColourSetIdAndTone(penultimateColoursBlock)
                  ) {
                    maps[whichMap_y][whichMap_x].supportBlockCount += 1;
                  }
                }
                // eslint-disable-next-line no-fallthrough
                default: {
                  // average block in column
                  const coloursBlock_north_index = i - 4 * 128 * optionValue_mapSize_x * 2;
                  const coloursBlock_north = exactRGBToColourSetIdAndTone([
                    canvasImageData.data[coloursBlock_north_index],
                    canvasImageData.data[coloursBlock_north_index + 1],
                    canvasImageData.data[coloursBlock_north_index + 2],
                  ]);
                  const coloursBlock_index = i - 4 * 128 * optionValue_mapSize_x;
                  const coloursBlock = exactRGBToColourSetIdAndTone([
                    canvasImageData.data[coloursBlock_index],
                    canvasImageData.data[coloursBlock_index + 1],
                    canvasImageData.data[coloursBlock_index + 2],
                  ]);
                  const coloursBlock_south = closestColourSetIdAndTone;
                  if (
                    // first under-support block
                    coloursBlock.tone === "light" ||
                    coloursBlock_south.tone === "dark" ||
                    (coloursBlock_south.tone === "normal" && isSupportBlockMandatoryForColourSetIdAndTone(coloursBlock_south)) ||
                    isSupportBlockMandatoryForColourSetIdAndTone(coloursBlock) ||
                    (coloursBlock.tone === "normal" && isSupportBlockMandatoryForColourSetIdAndTone(coloursBlock_north))
                  ) {
                    maps[whichMap_y][whichMap_x].supportBlockCount += 1;
                  }
                  if (
                    // second under-support block
                    (coloursBlock_south.tone === "dark" && isSupportBlockMandatoryForColourSetIdAndTone(coloursBlock_south)) ||
                    (coloursBlock.tone === "light" && isSupportBlockMandatoryForColourSetIdAndTone(coloursBlock_north))
                  ) {
                    maps[whichMap_y][whichMap_x].supportBlockCount += 1;
                  }
                  break;
                }
              }
              break;
            }
            case WhereSupportBlocksModes.ALL_DOUBLE_OPTIMIZED.uniqueId: {
              switch (individualMap_y) {
                case 0: {
                  // noobline
                  maps[whichMap_y][whichMap_x].supportBlockCount += 1;
                  if (closestColourSetIdAndTone.tone === "dark") {
                    maps[whichMap_y][whichMap_x].supportBlockCount += 1;
                  }
                  break;
                }
                case 127: {
                  // falls through
                  maps[whichMap_y][whichMap_x].supportBlockCount += 1;
                  if (closestColourSetIdAndTone.tone === "light") {
                    maps[whichMap_y][whichMap_x].supportBlockCount += 1;
                  }
                }
                // eslint-disable-next-line no-fallthrough
                default: {
                  maps[whichMap_y][whichMap_x].supportBlockCount += 1;
                  const coloursBlock_north_index = i - 4 * 128 * optionValue_mapSize_x;
                  const coloursBlock_north = exactRGBToColourSetIdAndTone([
                    canvasImageData.data[coloursBlock_north_index],
                    canvasImageData.data[coloursBlock_north_index + 1],
                    canvasImageData.data[coloursBlock_north_index + 2],
                  ]);
                  if (coloursBlock_north.tone === "light" || closestColourSetIdAndTone.tone === "dark") {
                    maps[whichMap_y][whichMap_x].supportBlockCount += 1;
                  }
                  break;
                }
              }
              break;
            }
            default: {
              break;
            }
          }
          maps[whichMap_y][whichMap_x].materials[closestColourSetIdAndTone.colourSetId] += 1;
        }
      }
      if (canvasImageData.data[indexA] === 0 && selectedBlocks[alphaColorIdx] > -1) {
        maps[whichMap_y][whichMap_x].materials[alphaColorIdx] += 1;
      }
  }
}

const ERROR_DIFFUSION_METHOD_IDS = [
  "FloydSteinberg",
  "FloydSteinberg_20",
  "FloydSteinberg_24",
  "Atkinson",
  "Atkinson_6",
  "Atkinson_10",
  "Atkinson_12",
  "SierraFilterLite",
  "Fan",
  "ShiauFan",
  "ShiauFan2",
  "JarvisJudiceNinke",
  "Stucki",
  "Burkes",
  "Sierra",
  "SierraTworow",
];

const ORDERED_METHOD_IDS = ["Bayer22", "Bayer33", "Bayer44", "Bayer88", "Ordered33", "ClusterDot44", "Halftone88", "VoidAndCluster1414"];

function ditherMethodFamily(chosenDitherMethod) {
  if (ERROR_DIFFUSION_METHOD_IDS.some((key) => DitherMethods[key] !== undefined && DitherMethods[key].uniqueId === chosenDitherMethod.uniqueId)) {
    return "errorDiffusion";
  }
  if (ORDERED_METHOD_IDS.some((key) => DitherMethods[key] !== undefined && DitherMethods[key].uniqueId === chosenDitherMethod.uniqueId)) {
    return "ordered";
  }
  return "none";
}

/*
  Quantises the whole image to the palette, writing the result back into
  canvasImageData and recording the chosen palette entry per pixel.

  Two things here follow SlopeCraft (utilities/ColorManip/imageConvert.hpp)
  rather than the previous implementation:

  1. The diffused error lives in dedicated float buffers, in the same colour
     space the colour metric uses. Previously the error was added straight back
     into canvasImageData.data, which is a Uint8ClampedArray: every write was
     rounded to an integer and clamped to [0, 255], so sub-unit error was
     discarded outright and error near black or white was thrown away. That is
     SlopeCraft's `dither_c3`, an Eigen::ArrayXXf per channel.

  2. Rows alternate direction (serpentine / boustrophedon scanning) with the
     kernel mirrored on right-to-left rows, which is SlopeCraft's
     dithermap_LR / dithermap_RL pair. A fixed left-to-right scan makes
     Floyd-Steinberg drag its error consistently one way and produces the
     familiar diagonal "worm" texture on smooth gradients.
*/
function quantiseImage() {
  const data = canvasImageData.data;
  const width = optionValue_mapSize_x * 128;
  const height = optionValue_mapSize_y * 128;
  pixelPaletteIndex = new Int32Array(width * height).fill(-1);

  const chosenDitherMethod =
    DitherMethods[Object.keys(DitherMethods).find((ditherMethodKey) => DitherMethods[ditherMethodKey].uniqueId === optionValue_dithering)];
  const family = ditherMethodFamily(chosenDitherMethod);
  const ditherMatrix = family === "none" ? null : chosenDitherMethod.ditherMatrix;
  const divisor = family === "errorDiffusion" ? chosenDitherMethod.ditherDivisor : 1;

  // Per-channel propagation strength, as a fraction.
  const propagation = [
    optionValue_dithering_propagation_red / 100.0,
    optionValue_dithering_propagation_green / 100.0,
    optionValue_dithering_propagation_blue / 100.0,
  ];

  // Rolling float error buffers: the current row and the two rows below it.
  // Every kernel in ditherMethods.json spans at most 3 rows and +/-2 columns.
  let errorRow0 = new Float64Array(width * 3);
  let errorRow1 = new Float64Array(width * 3);
  let errorRow2 = new Float64Array(width * 3);

  for (let y = 0; y < height; y++) {
    postMessage({
      head: "PROGRESS_REPORT",
      body: y / height,
    });

    // Serpentine scanning, for error diffusion only: ordered dithers are
    // position-indexed and an undithered pass has nothing to carry.
    const rightToLeft = family === "errorDiffusion" && y % 2 === 1;

    for (let step = 0; step < width; step++) {
      const x = rightToLeft ? width - 1 - step : step;
      const pixel = y * width + x;
      const i = pixel * 4;
      const indexA = i + 3;

      if (optionValue_modeNBTOrMapdat === MapModes.MAPDAT.uniqueId && optionValue_transparency && data[indexA] < optionValue_transparencyTolerance) {
        // we specially reserve 0,0,0,0 for transparent in mapdats
        data[i] = 0;
        data[i + 1] = 0;
        data[i + 2] = 0;
        data[indexA] = 0;
        continue; // no colour chosen, so there is no quantisation error to spread
      }

      if (data[indexA] !== 0 || selectedBlocks[alphaColorIdx] < 0) {
        data[indexA] = 255; // full opacity
      }

      const sourcePixel = [data[i], data[i + 1], data[i + 2]];
      let paletteIndex;

      if (family === "ordered") {
        // How far the pixel sits between its two nearest palette colours decides
        // how often the lattice should fall to the runner-up instead of the winner.
        const pair = nearestPaletteIndexPairFor(sourcePixel);
        const latticeCells = ditherMatrix[0].length * ditherMatrix.length;
        const threshold = ditherMatrix[x % ditherMatrix[0].length][y % ditherMatrix.length];
        if ((pair.nearestDistance * (latticeCells + 1)) / pair.runnerUpDistance > threshold) {
          paletteIndex = pair.runnerUpIndex;
        } else {
          paletteIndex = pair.nearestIndex;
        }
      } else if (family === "none") {
        paletteIndex = nearestPaletteIndexFor(sourcePixel);
      } else {
        // Error diffusion. The pixel is carried in dither space (linear light)
        // and the accumulated error is added there, at full float precision.
        const source = rgbToDitherSpace(sourcePixel[0], sourcePixel[1], sourcePixel[2]);
        const base = x * 3;
        // Clamped before use: out-of-gamut coordinates have no colour to match
        // against, and letting them accumulate makes the error run away.
        const v0 = clampDitherSpace(source[0] + errorRow0[base]);
        const v1 = clampDitherSpace(source[1] + errorRow0[base + 1]);
        const v2 = clampDitherSpace(source[2] + errorRow0[base + 2]);

        // Matching stays perceptual: back to sRGB, then into the chosen metric.
        const asRgb = ditherSpaceToRgb(v0, v1, v2);
        const metric = colourToSpaceF(asRgb[0], asRgb[1], asRgb[2]);
        paletteIndex = nearestPaletteIndexInSpace(metric[0], metric[1], metric[2]);

        const chosen = paletteIndex * 3;
        const error0 = (v0 - paletteDitherCoords[chosen]) * propagation[0];
        const error1 = (v1 - paletteDitherCoords[chosen + 1]) * propagation[1];
        const error2 = (v2 - paletteDitherCoords[chosen + 2]) * propagation[2];

        // ditherMatrix is indexed [dy][dx + 2], with the current pixel at [0][2].
        for (let dy = 0; dy < 3; dy++) {
          if (y + dy >= height) {
            break;
          }
          const targetRow = dy === 0 ? errorRow0 : dy === 1 ? errorRow1 : errorRow2;
          const kernelRow = ditherMatrix[dy];
          for (let dx = -2; dx <= 2; dx++) {
            if (dy === 0 && dx <= 0) {
              continue; // the current pixel and everything already visited on this row
            }
            const rawWeight = kernelRow[dx + 2];
            if (rawWeight === 0) {
              continue;
            }
            // On right-to-left rows the kernel is mirrored, which is equivalent
            // to mirroring the offset it is applied at.
            const targetX = rightToLeft ? x - dx : x + dx;
            if (targetX < 0 || targetX >= width) {
              continue; // never carry error across the edge of the multimap
            }
            const weight = rawWeight / divisor;
            const target = targetX * 3;
            targetRow[target] += error0 * weight;
            targetRow[target + 1] += error1 * weight;
            targetRow[target + 2] += error2 * weight;
          }
        }
      }

      const chosenColour = paletteEntries[paletteIndex].rgb;
      data[i] = chosenColour[0];
      data[i + 1] = chosenColour[1];
      data[i + 2] = chosenColour[2];
      pixelPaletteIndex[pixel] = paletteIndex;
    }

    // Advance the rolling window: row y+1 becomes the current row.
    const recycled = errorRow0;
    errorRow0 = errorRow1;
    errorRow1 = errorRow2;
    errorRow2 = recycled;
    errorRow2.fill(0);
  }
}

// ===========================================================================
// GA colour method, ported from SlopeCraft
// ===========================================================================
const GA_POPULATION_SIZE = 50; // SlopeCraft GA_converter_option::popSize
const GA_MAX_GENERATIONS = 200; // SlopeCraft GA_converter_option::maxGeneration
const GA_MAX_FAIL_TIMES = 50; // SlopeCraft GA_converter_option::maxFailTimes
const GA_CROSSOVER_PROB = 0.8; // SlopeCraft GA_converter_option::crossoverProb
const GA_MUTATION_PROB = 0.01; // SlopeCraft GA_converter_option::mutationProb
const GA_STRONG_MUTATION_RATIO = 0.01; // privateMutateFun<true>'s per-pixel rate
const GA_TOURNAMENT_SIZE = 3; // GAConverter::GAConverter -> setTournamentSize(3)
const GA_ORDER_MAX = 4; // GACvterDefines.hpp OrderMax

// GACvterDefines.hpp `Gaussian`
const GA_GAUSSIAN = [2, 4, 5, 4, 2, 4, 9, 12, 9, 4, 5, 12, 15, 12, 5, 4, 9, 12, 9, 4, 2, 4, 5, 4, 2];
const GA_GAUSSIAN_SUM = 159;

const GA_GRAY_MAX = 255; // GACvterDefines.hpp GrayMax
const GA_GRAY_WEIGHT = 1 + Math.pow(1.5, 2.2) + Math.pow(0.6, 2.2);

// GACvterDefines.hpp RGB2Gray_Gamma; r, g, b in [0, 1]
function rgb2GrayGamma(r, g, b) {
  const poweredSum = Math.pow(r, 2.2) + Math.pow(1.5 * g, 2.2) + Math.pow(0.6 * b, 2.2);
  return Math.pow(poweredSum / GA_GRAY_WEIGHT, 1.0 / 2.2);
}

// 5x5 Gaussian then 3x3 Sobel magnitude, both 'valid' (no padding), exactly as
// GACvterDefines.hpp applyGaussian + applySobel. Shrinks by 6 in each axis.
function gaEdgeFeature(gray, width, height, blurScratch, edgeOut) {
  const blurWidth = width - 4;
  const blurHeight = height - 4;
  for (let r = 0; r < blurHeight; r++) {
    for (let c = 0; c < blurWidth; c++) {
      let sum = 0;
      for (let kr = 0; kr < 5; kr++) {
        const rowBase = (r + kr) * width + c;
        const kernelBase = kr * 5;
        sum +=
          gray[rowBase] * GA_GAUSSIAN[kernelBase] +
          gray[rowBase + 1] * GA_GAUSSIAN[kernelBase + 1] +
          gray[rowBase + 2] * GA_GAUSSIAN[kernelBase + 2] +
          gray[rowBase + 3] * GA_GAUSSIAN[kernelBase + 3] +
          gray[rowBase + 4] * GA_GAUSSIAN[kernelBase + 4];
      }
      blurScratch[r * blurWidth + c] = sum / GA_GAUSSIAN_SUM;
    }
  }

  const edgeWidth = blurWidth - 2;
  const edgeHeight = blurHeight - 2;
  for (let r = 0; r < edgeHeight; r++) {
    for (let c = 0; c < edgeWidth; c++) {
      const top = r * blurWidth + c;
      const mid = top + blurWidth;
      const bottom = mid + blurWidth;
      const p00 = blurScratch[top];
      const p01 = blurScratch[top + 1];
      const p02 = blurScratch[top + 2];
      const p10 = blurScratch[mid];
      const p12 = blurScratch[mid + 2];
      const p20 = blurScratch[bottom];
      const p21 = blurScratch[bottom + 1];
      const p22 = blurScratch[bottom + 2];
      const gx = p00 + 2 * p01 + p02 - (p20 + 2 * p21 + p22);
      const gy = p02 - p00 + 2 * (p12 - p10) + p22 - p20;
      edgeOut[r * edgeWidth + c] = Math.sqrt(gx * gx + gy * gy);
    }
  }
}

// Runs fn with a different colour method temporarily active. The colour caches
// and the palette coordinates are method-dependent, so both are rebuilt.
function withColourMethod(methodUniqueId, fn) {
  const previous = optionValue_betterColour;
  optionValue_betterColour = methodUniqueId;
  nearestColourCache.clear();
  nearestPairCache.clear();
  setupPalette();
  try {
    return fn();
  } finally {
    optionValue_betterColour = previous;
    nearestColourCache.clear();
    nearestPairCache.clear();
    setupPalette();
  }
}

// Entry point for the GaCvter colour method; getMapartImageDataAndMaterials
// calls this instead of quantiseImage, then this calls quantiseImage itself.
function runGaConverter() {
  const data = canvasImageData.data;
  const width = optionValue_mapSize_x * 128;
  const height = optionValue_mapSize_y * 128;
  const pixelCount = width * height;

  // The Gaussian and Sobel passes are 'valid', so anything under 7x7 has no
  // edge map at all; a palette of under 2 entries leaves the GA nothing to
  // choose between either.
  if (width < 7 || height < 7 || paletteEntries.length < 2) {
    quantiseImage();
    return;
  }

  const orderMax = Math.min(GA_ORDER_MAX, paletteEntries.length);

  // --- per-pixel candidate shortlist (SlopeCraft sortColor::calculate) ------
  // The nearest `orderMax` palette entries by plain Euclidean RGB distance.
  const candidates = new Int32Array(pixelCount * GA_ORDER_MAX);
  const opaque = new Uint8Array(pixelCount);
  const sortColourCache = new Map();
  const paletteCount = paletteEntries.length;
  const scratchDist = new Float64Array(paletteCount);

  for (let pixel = 0; pixel < pixelCount; pixel++) {
    const i = pixel * 4;
    if (data[i + 3] === 0) {
      continue; // transparent: excluded from the edge map, and left to quantiseImage
    }
    opaque[pixel] = 1;
    const r = data[i];
    const g = data[i + 1];
    const b = data[i + 2];
    const key = (r << 16) + (g << 8) + b;
    let shortlist = sortColourCache.get(key);
    if (shortlist === undefined) {
      for (let p = 0; p < paletteCount; p++) {
        const rgb = paletteEntries[p].rgb;
        const dr = rgb[0] - r;
        const dg = rgb[1] - g;
        const db = rgb[2] - b;
        scratchDist[p] = dr * dr + dg * dg + db * db;
      }
      shortlist = new Int32Array(GA_ORDER_MAX);
      for (let o = 0; o < GA_ORDER_MAX; o++) {
        let bestIdx = 0;
        let bestDist = Infinity;
        for (let p = 0; p < paletteCount; p++) {
          if (scratchDist[p] < bestDist) {
            bestDist = scratchDist[p];
            bestIdx = p;
          }
        }
        shortlist[o] = bestIdx;
        scratchDist[bestIdx] = Infinity;
      }
      sortColourCache.set(key, shortlist);
    }
    const base = pixel * GA_ORDER_MAX;
    for (let o = 0; o < GA_ORDER_MAX; o++) {
      candidates[base + o] = shortlist[o];
    }
  }

  // --- grayscale lookup for the palette (updateMapColor2GrayLUT) -----------
  const paletteGray = new Float64Array(paletteCount);
  for (let p = 0; p < paletteCount; p++) {
    const rgb = paletteEntries[p].rgb;
    paletteGray[p] = GA_GRAY_MAX * rgb2GrayGamma(rgb[0] / 255.0, rgb[1] / 255.0, rgb[2] / 255.0);
  }

  // --- edge map of the source image (GAConverter::setRawImage) -------------
  const blurScratch = new Float64Array((width - 4) * (height - 4));
  const edgeWidth = width - 6;
  const edgeHeight = height - 6;
  const edgeSize = edgeWidth * edgeHeight;
  const sourceEdge = new Float64Array(edgeSize);
  const candidateEdge = new Float64Array(edgeSize);
  const gray = new Float64Array(pixelCount);

  for (let pixel = 0; pixel < pixelCount; pixel++) {
    if (!opaque[pixel]) {
      gray[pixel] = 0;
      continue;
    }
    const i = pixel * 4;
    gray[pixel] = GA_GRAY_MAX * rgb2GrayGamma(data[i] / 255.0, data[i + 1] / 255.0, data[i + 2] / 255.0);
  }
  gaEdgeFeature(gray, width, height, blurScratch, sourceEdge);

  // GAConverter::fFun -- log10 of the mean absolute edge-map difference.
  // Lower is better (heu::FitnessOption::FITNESS_LESS_BETTER).
  function fitness(genome) {
    for (let pixel = 0; pixel < pixelCount; pixel++) {
      gray[pixel] = opaque[pixel] ? paletteGray[candidates[pixel * GA_ORDER_MAX + genome[pixel]]] : 0;
    }
    gaEdgeFeature(gray, width, height, blurScratch, candidateEdge);
    let total = 0;
    for (let e = 0; e < edgeSize; e++) {
      total += Math.abs(candidateEdge[e] - sourceEdge[e]);
    }
    return Math.log10(total / pixelCount);
  }

  // --- seeds: the results of the other colour methods ----------------------
  // SlopeCraft seeds with RGB, RGB_Better, Lab94, HSV and XYZ; these are this
  // project's equivalents. CIEDE2000 is left out: it would contribute the same
  // direction as CIE76 for many times the cost.
  const seedMethods = [
    ColourMethods.Euclidian.uniqueId,
    ColourMethods.MapartCraftDefault.uniqueId,
    ColourMethods.Cie76_Lab65.uniqueId,
    ColourMethods.Cie76_Lab50.uniqueId,
    ColourMethods.Hct.uniqueId,
  ];
  const seeds = [];
  for (const method of seedMethods) {
    const seed = new Uint8Array(pixelCount);
    withColourMethod(method, () => {
      for (let pixel = 0; pixel < pixelCount; pixel++) {
        if (!opaque[pixel]) {
          continue;
        }
        const i = pixel * 4;
        const chosen = nearestPaletteIndexFor([data[i], data[i + 1], data[i + 2]]);
        // GAConverter::setSeeds: find which of the shortlisted candidates this is
        const base = pixel * GA_ORDER_MAX;
        for (let o = 0; o < orderMax; o++) {
          if (candidates[base + o] === chosen) {
            seed[pixel] = o;
            break;
          }
        }
      }
    });
    seeds.push(seed);
  }

  // --- GA operators (GAConverter.cpp) --------------------------------------
  const randomOrder = () => Math.floor(Math.random() * orderMax);
  // GACvterDefines.hpp makeMutateMap: pick an order that differs from the current one
  const differentOrder = (current) => {
    const pick = Math.floor(Math.random() * (orderMax - 1));
    return pick >= current ? pick + 1 : pick;
  };

  function mutate(parent, strong) {
    const child = Uint8Array.from(parent);
    if (strong) {
      for (let pixel = 0; pixel < pixelCount; pixel++) {
        if (Math.random() <= GA_STRONG_MUTATION_RATIO) {
          child[pixel] = differentOrder(child[pixel]);
        }
      }
    } else {
      const pixel = Math.floor(Math.random() * pixelCount);
      child[pixel] = differentOrder(child[pixel]);
    }
    return child;
  }

  // GAConverter::iFun
  function createIndividual() {
    if (Math.random() < 1.0 / 3) {
      // random, but consistent per source colour
      const orderByColour = new Map();
      const individual = new Uint8Array(pixelCount);
      for (let pixel = 0; pixel < pixelCount; pixel++) {
        if (!opaque[pixel]) {
          continue;
        }
        const i = pixel * 4;
        const key = (data[i] << 16) + (data[i + 1] << 8) + data[i + 2];
        let order = orderByColour.get(key);
        if (order === undefined) {
          order = randomOrder();
          orderByColour.set(key, order);
        }
        individual[pixel] = order;
      }
      return individual;
    }
    const seed = seeds[Math.floor(Math.random() * seeds.length)];
    return mutate(seed, Math.random() < 0.4);
  }

  // GAConverter::cFun -- split the image at a random point and take each of the
  // four quadrants from either parent.
  function crossover(parentA, parentB) {
    const splitRow = 1 + Math.floor(Math.random() * (height - 3));
    const splitCol = 1 + Math.floor(Math.random() * (width - 3));
    const parents = [parentA, parentB];
    const children = [new Uint8Array(pixelCount), new Uint8Array(pixelCount)];
    for (let c = 0; c < 2; c++) {
      const child = children[c];
      const topLeft = parents[Math.random() < 0.5 ? 0 : 1];
      const topRight = parents[Math.random() < 0.5 ? 0 : 1];
      const bottomLeft = parents[Math.random() < 0.5 ? 0 : 1];
      const bottomRight = parents[Math.random() < 0.5 ? 0 : 1];
      for (let y = 0; y < height; y++) {
        const rowBase = y * width;
        const left = y < splitRow ? topLeft : bottomLeft;
        const right = y < splitRow ? topRight : bottomRight;
        for (let x = 0; x < splitCol; x++) {
          child[rowBase + x] = left[rowBase + x];
        }
        for (let x = splitCol; x < width; x++) {
          child[rowBase + x] = right[rowBase + x];
        }
      }
    }
    return children;
  }

  // --- the GA itself (heu::SOGA, tournament selection, elitism) ------------
  let population = [];
  for (let i = 0; i < GA_POPULATION_SIZE; i++) {
    const genome = createIndividual();
    population.push({ genome: genome, fitness: fitness(genome) });
  }

  function tournamentPick(pool) {
    let best = pool[Math.floor(Math.random() * pool.length)];
    for (let t = 1; t < GA_TOURNAMENT_SIZE; t++) {
      const challenger = pool[Math.floor(Math.random() * pool.length)];
      if (challenger.fitness < best.fitness) {
        best = challenger;
      }
    }
    return best;
  }

  let bestEver = population[0];
  for (const individual of population) {
    if (individual.fitness < bestEver.fitness) {
      bestEver = individual;
    }
  }

  let failTimes = 0;
  for (let generation = 0; generation < GA_MAX_GENERATIONS; generation++) {
    postMessage({
      head: "PROGRESS_REPORT",
      body: generation / GA_MAX_GENERATIONS,
    });

    const offspring = [];
    for (let pair = 0; pair < GA_POPULATION_SIZE / 2; pair++) {
      if (Math.random() >= GA_CROSSOVER_PROB) {
        continue;
      }
      const children = crossover(tournamentPick(population).genome, tournamentPick(population).genome);
      offspring.push({ genome: children[0], fitness: 0 }, { genome: children[1], fitness: 0 });
    }

    // GAConverter::__impl_recordFitness: mutation is strong for the first half
    // of the run, then weak, so the search coarsens early and refines late.
    const strongMutation = generation * 2 < GA_MAX_GENERATIONS;
    for (const individual of population) {
      if (Math.random() < GA_MUTATION_PROB) {
        offspring.push({ genome: mutate(individual.genome, strongMutation), fitness: 0 });
      }
    }

    for (const individual of offspring) {
      individual.fitness = fitness(individual.genome);
    }

    const pool = population.concat(offspring);
    let generationBest = pool[0];
    for (const individual of pool) {
      if (individual.fitness < generationBest.fitness) {
        generationBest = individual;
      }
    }

    const survivors = [generationBest]; // elitism
    while (survivors.length < GA_POPULATION_SIZE) {
      survivors.push(tournamentPick(pool));
    }
    population = survivors;

    if (generationBest.fitness < bestEver.fitness) {
      bestEver = generationBest;
      failTimes = 0;
    } else {
      failTimes++;
      if (failTimes >= GA_MAX_FAIL_TIMES) {
        break;
      }
    }
  }

  // --- write the winner back (GAConverter::resultImage) --------------------
  const best = bestEver.genome;
  for (let pixel = 0; pixel < pixelCount; pixel++) {
    if (!opaque[pixel]) {
      continue;
    }
    const rgb = paletteEntries[candidates[pixel * GA_ORDER_MAX + best[pixel]]].rgb;
    const i = pixel * 4;
    data[i] = rgb[0];
    data[i + 1] = rgb[1];
    data[i + 2] = rgb[2];
  }

  // MapImageCvter::convert_image feeds the GA result back through the normal
  // conversion, so that the dither setting still applies. The image is already
  // made of palette colours, so with dithering off this pass is exact.
  quantiseImage();
}

onmessage = (e) => {
  coloursJSON = e.data.body.coloursJSON;
  MapModes = e.data.body.MapModes;
  WhereSupportBlocksModes = e.data.body.WhereSupportBlocksModes;
  ColourMethods = e.data.body.ColourMethods;
  DitherMethods = e.data.body.DitherMethods;
  canvasImageData = e.data.body.canvasImageData;
  selectedBlocks = e.data.body.selectedBlocks;
  disabledTones = e.data.body.disabledTones;
  optionValue_modeNBTOrMapdat = e.data.body.optionValue_modeNBTOrMapdat;
  optionValue_mapSize_x = e.data.body.optionValue_mapSize_x;
  optionValue_mapSize_y = e.data.body.optionValue_mapSize_y;
  optionValue_staircasing = e.data.body.optionValue_staircasing;
  optionValue_whereSupportBlocks = e.data.body.optionValue_whereSupportBlocks;
  optionValue_transparency = e.data.body.optionValue_transparency;
  optionValue_transparencyTolerance = e.data.body.optionValue_transparencyTolerance;
  optionValue_betterColour = e.data.body.optionValue_betterColour;
  optionValue_dithering = e.data.body.optionValue_dithering;
  optionValue_dithering_propagation_red = e.data.body.optionValue_dithering_propagation_red;
  optionValue_dithering_propagation_green = e.data.body.optionValue_dithering_propagation_green;
  optionValue_dithering_propagation_blue = e.data.body.optionValue_dithering_propagation_blue;

  setupColourSetsToUse();
  setupPalette();
  setupExactColourCache();
  getMapartImageDataAndMaterials();
  postMessage({
    head: "PIXELS_MATERIALS_CURRENTSELECTEDBLOCKS",
    body: {
      pixels: canvasImageData,
      maps: maps,
      currentSelectedBlocks: selectedBlocks,
    },
  });
};

};
