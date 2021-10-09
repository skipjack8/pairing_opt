use super::super::bn256::check_curve_init;
use super::super::mcl::{
    mclBnG1_add, mclBnG1_dbl, mclBnG1_neg, mclBnG1_normalize, Fp as mcl_fq, G1 as mcl_g1,
};
use super::g2::G2Affine;
use super::{Bn256, Fq, Fq12, FqRepr, Fr, FrRepr};
use crate::{CurveAffine, CurveProjective, EncodedPoint, Engine, GroupDecodingError, RawEncodable};
use ff::{BitIterator, Field, PrimeField, PrimeFieldRepr, SqrtField};

use crate::mcl::{mclBnFp_add, mclBnFp_inv, mclBnFp_sqr};
use rand::{Rand, Rng};
use std::fmt;
use std::ops::{AddAssign, MulAssign, SubAssign};

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct G1Affine {
    pub(crate) x: Fq,
    pub(crate) y: Fq,
    pub(crate) infinity: bool,
}

impl ::std::fmt::Display for G1Affine {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        if self.infinity {
            write!(f, "{}(Infinity)", "G1")
        } else {
            write!(f, "{}(x={}, y={})", "G1", self.x, self.y)
        }
    }
}

#[derive(Copy, Clone, Debug, Eq)]
pub struct G1(pub(crate) mcl_g1);

impl ::std::fmt::Display for G1 {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}", self.into_affine())
    }
}

impl PartialEq for G1 {
    fn eq(&self, other: &G1) -> bool {
        self.0.eq(&other.0)
    }
}

impl G1Affine {
    fn mul_bits<S: AsRef<[u64]>>(&self, bits: BitIterator<S>) -> G1 {
        let mut res = G1::zero();
        for i in bits {
            res.double();
            if i {
                res.add_assign_mixed(self)
            }
        }
        res
    }

    /// Attempts to construct an affine point given an x-coordinate. The
    /// point is not guaranteed to be in the prime order subgroup.
    ///
    /// If and only if `greatest` is set will the lexicographically
    /// largest y-coordinate be selected.
    fn get_point_from_x(x: Fq, greatest: bool) -> Option<G1Affine> {
        // Compute x^3 + b
        let mut x3b = x;
        x3b.square();
        x3b.mul_assign(&x);
        x3b.add_assign(&G1Affine::get_coeff_b());

        x3b.sqrt().map(|y| {
            let mut negy = y;
            negy.negate();

            G1Affine {
                x: x,
                y: if (y < negy) ^ greatest { y } else { negy },
                infinity: false,
            }
        })
    }

    fn is_on_curve(&self) -> bool {
        if self.is_zero() {
            true
        } else {
            // Check that the point is on the curve
            let mut y2 = self.y;
            y2.square();

            let mut x3b = self.x;
            x3b.square();
            x3b.mul_assign(&self.x);
            x3b.add_assign(&Self::get_coeff_b());

            y2 == x3b
        }
    }
}

impl CurveAffine for G1Affine {
    type Engine = Bn256;
    type Scalar = Fr;
    type Base = Fq;
    type Prepared = G1Prepared;
    type Projective = G1;
    type Uncompressed = G1Uncompressed;
    type Compressed = G1Compressed;
    type Pair = G2Affine;
    type PairingResult = Fq12;

    fn zero() -> Self {
        G1Affine {
            x: Fq::zero(),
            y: Fq::one(),
            infinity: true,
        }
    }

    fn one() -> Self {
        Self::get_generator()
    }

    fn is_zero(&self) -> bool {
        self.infinity
    }

    fn mul<S: Into<<Self::Scalar as PrimeField>::Repr>>(&self, by: S) -> G1 {
        let bits = BitIterator::new(by.into());
        self.mul_bits(bits)
    }

    fn negate(&mut self) {
        if !self.is_zero() {
            self.y.negate();
        }
    }

    fn prepare(&self) -> Self::Prepared {
        G1Prepared::from_affine(*self)
    }

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        self.perform_pairing(other)
    }

    fn into_projective(&self) -> G1 {
        (*self).into()
    }

    #[inline(always)]
    fn as_xy(&self) -> (&Self::Base, &Self::Base) {
        (&self.x, &self.y)
    }

    #[inline(always)]
    fn into_xy_unchecked(self) -> (Self::Base, Self::Base) {
        (self.x, self.y)
    }

    #[inline(always)]
    fn from_xy_unchecked(x: Self::Base, y: Self::Base) -> Self {
        let infinity = x.is_zero() && y.is_zero();
        Self {
            x: x,
            y: y,
            infinity,
        }
    }

    fn from_xy_checked(x: Self::Base, y: Self::Base) -> Result<Self, GroupDecodingError> {
        let infinity = x.is_zero() && y.is_zero();
        let affine = Self {
            x: x,
            y: y,
            infinity,
        };

        if !affine.is_on_curve() {
            Err(GroupDecodingError::NotOnCurve)
        } else {
            Ok(affine)
        }
    }

    fn a_coeff() -> Self::Base {
        Self::Base::zero()
    }

    fn b_coeff() -> Self::Base {
        G1Affine::get_coeff_b()
    }
}

impl CurveProjective for G1 {
    type Engine = Bn256;
    type Scalar = Fr;
    type Base = Fq;
    type Affine = G1Affine;

    // The point at infinity is always represented by
    // Z = 0.
    fn zero() -> Self {
        check_curve_init();
        Self(mcl_g1::zero())
    }

    fn one() -> Self {
        G1Affine::one().into()
    }

    // The point at infinity is always represented by
    // Z = 0.
    fn is_zero(&self) -> bool {
        check_curve_init();
        self.0.is_zero()
    }

    fn is_normalized(&self) -> bool {
        self.is_zero() || self.0.z.is_one()
    }

    //TODO:: not change now
    fn batch_normalization(v: &mut [Self]) {
        // Montgomery’s Trick and Fast Implementation of Masked AES
        // Genelle, Prouff and Quisquater
        // Section 3.2

        // First pass: compute [a, ab, abc, ...]
        let mut prod = Vec::with_capacity(v.len());
        let mut tmp = mcl_fq::one();
        check_curve_init();
        for g in v
            .iter_mut()
            // Ignore normalized elements
            .filter(|g| !g.is_normalized())
        {
            tmp.mul_assign(&g.0.z);
            prod.push(tmp);
        }

        // Invert `tmp`.
        unsafe { mclBnFp_inv(&mut tmp, &tmp) }; // Guaranteed to be nonzero.

        // Second pass: iterate backwards to compute inverses
        for (g, s) in v
            .iter_mut()
            // Backwards
            .rev()
            // Ignore normalized elements
            .filter(|g| !g.is_normalized())
            // Backwards, skip last element, fill in one for last term.
            .zip(prod.into_iter().rev().skip(1).chain(Some(mcl_fq::one())))
        {
            // tmp := tmp * g.z; g.z := tmp * s = 1/z
            let mut newtmp = tmp;
            newtmp.mul_assign(&g.0.z);
            g.0.z = tmp;
            g.0.z.mul_assign(&s);
            tmp = newtmp;
        }

        // Perform affine transformations
        for g in v.iter_mut().filter(|g| !g.is_normalized()) {
            let mut z = g.0.z; // 1/z
            unsafe { mclBnFp_sqr(&mut z, &z) };
            g.0.x.mul_assign(&z); // x/z^2
            z.mul_assign(&g.0.z); // 1/z^3
            g.0.y.mul_assign(&z); // y/z^3
            g.0.z = mcl_fq::one(); // z = 1
        }
    }

    fn double(&mut self) {
        check_curve_init();
        unsafe { mclBnG1_dbl(&mut self.0, &self.0) };
    }

    fn add_assign(&mut self, other: &Self) {
        check_curve_init();
        unsafe { mclBnG1_add(&mut self.0, &self.0, &other.0) };
    }
    //TODO: not change now
    fn add_assign_mixed(&mut self, other: &Self::Affine) {
        if other.is_zero() {
            return;
        }

        if self.is_zero() {
            self.0.x = other.x.0;
            self.0.y = other.y.0;
            self.0.z = mcl_fq::one();
            return;
        }

        // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl

        // Z1Z1 = Z1^2
        let mut z1z1 = self.0.z;
        unsafe { mclBnFp_sqr(&mut z1z1, &z1z1) };

        // U2 = X2*Z1Z1
        let mut u2 = other.x.0;
        u2.mul_assign(&z1z1);

        // S2 = Y2*Z1*Z1Z1
        let mut s2 = other.y.0;
        s2.mul_assign(&self.0.z);
        s2.mul_assign(&z1z1);

        if self.0.x == u2 && self.0.y == s2 {
            // The two points are equal, so we double.
            self.double();
        } else {
            // If we're adding -a and a together, self.z becomes zero as H becomes zero.

            // H = U2-X1
            let mut h = u2;
            h.sub_assign(&self.0.x);

            // HH = H^2
            let mut hh = h;
            unsafe { mclBnFp_sqr(&mut hh, &hh) };

            // I = 4*HH
            let mut i = hh;
            unsafe {
                mclBnFp_add(&mut i, &i, &i);
                mclBnFp_add(&mut i, &i, &i);
            }

            // J = H*I
            let mut j = h;
            j.mul_assign(&i);

            // r = 2*(S2-Y1)
            let mut r = s2;
            r.sub_assign(&self.0.y);
            unsafe { mclBnFp_add(&mut r, &r, &r) };

            // V = X1*I
            let mut v = self.0.x;
            v.mul_assign(&i);

            // X3 = r^2 - J - 2*V
            self.0.x = r;
            unsafe { mclBnFp_sqr(&mut self.0.x, &self.0.x) };
            self.0.x.sub_assign(&j);
            self.0.x.sub_assign(&v);
            self.0.x.sub_assign(&v);

            // Y3 = r*(V-X3)-2*Y1*J
            j.mul_assign(&self.0.y); // J = 2*Y1*J
            unsafe { mclBnFp_add(&mut j, &j, &j) };
            self.0.y = v;
            self.0.y.sub_assign(&self.0.x);
            self.0.y.mul_assign(&r);
            self.0.y.sub_assign(&j);

            // Z3 = (Z1+H)^2-Z1Z1-HH
            self.0.z.add_assign(&h);
            unsafe { mclBnFp_sqr(&mut self.0.z, &self.0.z) };
            self.0.z.sub_assign(&z1z1);
            self.0.z.sub_assign(&hh);
        }
    }

    fn negate(&mut self) {
        check_curve_init();
        unsafe { mclBnG1_neg(&mut self.0, &self.0) };
    }
    // TODO: not change now
    fn mul_assign<S: Into<<Self::Scalar as PrimeField>::Repr>>(&mut self, other: S) {
        let mut res = Self::zero();

        let mut found_one = false;

        for i in BitIterator::new(other.into()) {
            if found_one {
                res.double();
            } else {
                found_one = i;
            }

            if i {
                res.add_assign(self);
            }
        }

        *self = res;
    }

    fn into_affine(&self) -> G1Affine {
        (*self).into()
    }

    fn recommended_wnaf_for_scalar(scalar: <Self::Scalar as PrimeField>::Repr) -> usize {
        Self::empirical_recommended_wnaf_for_scalar(scalar)
    }

    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        Self::empirical_recommended_wnaf_for_num_scalars(num_scalars)
    }

    fn as_xyz(&self) -> (&Self::Base, &Self::Base, &Self::Base) {
        unimplemented!("not implement for projective");
    }

    fn into_xyz_unchecked(self) -> (Self::Base, Self::Base, Self::Base) {
        (Fq(self.0.x), Fq(self.0.y), Fq(self.0.z))
    }

    fn from_xyz_unchecked(x: Self::Base, y: Self::Base, z: Self::Base) -> Self {
        Self(mcl_g1 {
            x: x.0,
            y: y.0,
            z: z.0,
        })
    }

    fn from_xyz_checked(
        _x: Self::Base,
        _y: Self::Base,
        _z: Self::Base,
    ) -> Result<Self, GroupDecodingError> {
        unimplemented!("on curve check is not implemented for projective")
    }
}

// The affine point X, Y is represented in the jacobian
// coordinates with Z = 1.
impl From<G1Affine> for G1 {
    fn from(p: G1Affine) -> G1 {
        if p.is_zero() {
            G1::zero()
        } else {
            G1(mcl_g1 {
                x: p.x.0,
                y: p.y.0,
                z: Fq::one().0,
            })
        }
    }
}

// The projective point X, Y, Z is represented in the affine
// coordinates as X/Z^2, Y/Z^3.
impl From<G1> for G1Affine {
    fn from(p: G1) -> G1Affine {
        if p.is_zero() {
            G1Affine::zero()
        } else if p.0.z.is_one() {
            // If Z is one, the point is already normalized.
            G1Affine {
                x: Fq(p.0.x),
                y: Fq(p.0.y),
                infinity: false,
            }
        } else {
            let mut res = unsafe { mcl_g1::uninit() };
            unsafe { mclBnG1_normalize(&mut res, &p.0) };

            G1Affine {
                x: Fq(res.x),
                y: Fq(res.y),
                infinity: false,
            }
        }
    }
}

impl RawEncodable for G1Affine {
    fn into_raw_uncompressed_le(&self) -> Self::Uncompressed {
        let mut res = Self::Uncompressed::empty();
        {
            let mut writer = &mut res.0[..];

            self.x.into_raw_repr().write_le(&mut writer).unwrap();
            self.y.into_raw_repr().write_le(&mut writer).unwrap();
        }

        res
    }

    /// Creates a point from raw encoded coordinates without checking on curve
    fn from_raw_uncompressed_le_unchecked(
        encoded: &Self::Uncompressed,
        _infinity: bool,
    ) -> Result<Self, GroupDecodingError> {
        let copy = encoded.0;

        if copy.iter().all(|b| *b == 0) {
            return Ok(Self::zero());
        }

        let mut x = FqRepr([0; 4]);
        let mut y = FqRepr([0; 4]);

        {
            let mut reader = &copy[..];
            x.read_le(&mut reader).unwrap();
            y.read_le(&mut reader).unwrap();
        }

        Ok(G1Affine {
            x: Fq::from_raw_repr(x)
                .map_err(|e| GroupDecodingError::CoordinateDecodingError("x coordinate", e))?,
            y: Fq::from_raw_repr(y)
                .map_err(|e| GroupDecodingError::CoordinateDecodingError("y coordinate", e))?,
            infinity: false,
        })
    }

    fn from_raw_uncompressed_le(
        encoded: &Self::Uncompressed,
        _infinity: bool,
    ) -> Result<Self, GroupDecodingError> {
        let affine = Self::from_raw_uncompressed_le_unchecked(&encoded, _infinity)?;

        if !affine.is_on_curve() {
            Err(GroupDecodingError::NotOnCurve)
        } else {
            Ok(affine)
        }
    }
}

#[derive(Copy, Clone)]
pub struct G1Uncompressed([u8; 64]);

impl Rand for G1 {
    fn rand<R: Rng>(rng: &mut R) -> Self {
        loop {
            let x = rng.gen();
            let greatest = rng.gen();

            if let Some(p) = G1Affine::get_point_from_x(x, greatest) {
                if !p.is_zero() {
                    if p.is_on_curve() {
                        return p.into_projective();
                    }
                }
            }
        }
    }
}

impl Rand for G1Affine {
    fn rand<R: Rng>(rng: &mut R) -> Self {
        loop {
            let x = rng.gen();
            let greatest = rng.gen();

            if let Some(p) = G1Affine::get_point_from_x(x, greatest) {
                if !p.is_zero() {
                    if p.is_on_curve() {
                        return p;
                    }
                }
            }
        }
    }
}

impl AsRef<[u8]> for G1Uncompressed {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsMut<[u8]> for G1Uncompressed {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl fmt::Debug for G1Uncompressed {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.0[..].fmt(formatter)
    }
}

impl EncodedPoint for G1Uncompressed {
    type Affine = G1Affine;

    fn empty() -> Self {
        G1Uncompressed([0; 64])
    }
    fn size() -> usize {
        64
    }
    fn into_affine(&self) -> Result<G1Affine, GroupDecodingError> {
        let affine = self.into_affine_unchecked()?;

        if !affine.is_on_curve() {
            Err(GroupDecodingError::NotOnCurve)
        } else {
            Ok(affine)
        }
    }
    fn into_affine_unchecked(&self) -> Result<G1Affine, GroupDecodingError> {
        // Create a copy of this representation.
        let mut copy = self.0;

        if copy[0] & (1 << 6) != 0 {
            // This is the point at infinity, which means that if we mask away
            // the first two bits, the entire representation should consist
            // of zeroes.
            copy[0] &= 0x3f;

            if copy.iter().all(|b| *b == 0) {
                Ok(G1Affine::zero())
            } else {
                Err(GroupDecodingError::UnexpectedInformation)
            }
        } else {
            if copy[0] & (1 << 7) != 0 {
                // The bit indicating the y-coordinate should be lexicographically
                // largest is set, but this is an uncompressed element.
                return Err(GroupDecodingError::UnexpectedInformation);
            }

            // Unset the two most significant bits.
            copy[0] &= 0x3f;

            let mut x = FqRepr([0; 4]);
            let mut y = FqRepr([0; 4]);

            {
                let mut reader = &copy[..];

                x.read_be(&mut reader).unwrap();
                y.read_be(&mut reader).unwrap();
            }

            Ok(G1Affine {
                x: Fq::from_repr(x)
                    .map_err(|e| GroupDecodingError::CoordinateDecodingError("x coordinate", e))?,
                y: Fq::from_repr(y)
                    .map_err(|e| GroupDecodingError::CoordinateDecodingError("y coordinate", e))?,
                infinity: false,
            })
        }
    }
    fn from_affine(affine: G1Affine) -> Self {
        let mut res = Self::empty();

        if affine.is_zero() {
            // Set the second-most significant bit to indicate this point
            // is at infinity.
            res.0[0] |= 1 << 6;
        } else {
            let mut writer = &mut res.0[..];

            affine.x.into_repr().write_be(&mut writer).unwrap();
            affine.y.into_repr().write_be(&mut writer).unwrap();
        }

        res
    }
}

#[derive(Copy, Clone)]
pub struct G1Compressed([u8; 32]);

impl AsRef<[u8]> for G1Compressed {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsMut<[u8]> for G1Compressed {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl fmt::Debug for G1Compressed {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.0[..].fmt(formatter)
    }
}

impl EncodedPoint for G1Compressed {
    type Affine = G1Affine;

    fn empty() -> Self {
        G1Compressed([0; 32])
    }
    fn size() -> usize {
        32
    }
    fn into_affine(&self) -> Result<G1Affine, GroupDecodingError> {
        let affine = self.into_affine_unchecked()?;

        // NB: Decompression guarantees that it is on the curve already.

        Ok(affine)
    }
    fn into_affine_unchecked(&self) -> Result<G1Affine, GroupDecodingError> {
        // Create a copy of this representation.
        let mut copy = self.0;

        if copy[0] & (1 << 6) != 0 {
            // This is the point at infinity, which means that if we mask away
            // the first two bits, the entire representation should consist
            // of zeroes.
            copy[0] &= 0x3f;

            if copy.iter().all(|b| *b == 0) {
                Ok(G1Affine::zero())
            } else {
                Err(GroupDecodingError::UnexpectedInformation)
            }
        } else {
            // Determine if the intended y coordinate must be greater
            // lexicographically.
            let greatest = copy[0] & (1 << 7) != 0;

            // Unset the two most significant bits.
            copy[0] &= 0x3f;

            let mut x = FqRepr([0; 4]);

            {
                let mut reader = &copy[..];

                x.read_be(&mut reader).unwrap();
            }

            // Interpret as Fq element.
            let x = Fq::from_repr(x)
                .map_err(|e| GroupDecodingError::CoordinateDecodingError("x coordinate", e))?;

            G1Affine::get_point_from_x(x, greatest).ok_or(GroupDecodingError::NotOnCurve)
        }
    }
    fn from_affine(affine: G1Affine) -> Self {
        let mut res = Self::empty();

        if affine.is_zero() {
            // Set the second-most significant bit to indicate this point
            // is at infinity.
            res.0[0] |= 1 << 6;
        } else {
            {
                let mut writer = &mut res.0[..];

                affine.x.into_repr().write_be(&mut writer).unwrap();
            }

            let mut negy = affine.y;
            negy.negate();

            // Set the third most significant bit if the correct y-coordinate
            // is lexicographically largest.
            if affine.y > negy {
                res.0[0] |= 1 << 7;
            }
        }

        res
    }
}

impl G1Affine {
    // fn scale_by_cofactor(&self) -> G1 {
    //     self.into_projective()
    // }

    fn get_generator() -> Self {
        G1Affine {
            x: super::fq::G1_GENERATOR_X,
            y: super::fq::G1_GENERATOR_Y,
            infinity: false,
        }
    }

    fn get_coeff_b() -> Fq {
        super::fq::B_COEFF
    }

    fn perform_pairing(&self, other: &G2Affine) -> Fq12 {
        super::Bn256::pairing(*self, *other)
    }
}

impl G1 {
    fn empirical_recommended_wnaf_for_scalar(scalar: FrRepr) -> usize {
        let num_bits = scalar.num_bits() as usize;

        if num_bits >= 130 {
            4
        } else if num_bits >= 34 {
            3
        } else {
            2
        }
    }

    fn empirical_recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        const RECOMMENDATIONS: [usize; 12] =
            [1, 3, 7, 20, 43, 120, 273, 563, 1630, 3128, 7933, 62569];

        let mut ret = 4;
        for r in &RECOMMENDATIONS {
            if num_scalars > *r {
                ret += 1;
            } else {
                break;
            }
        }

        ret
    }
}

#[derive(Clone, Debug)]
pub struct G1Prepared(pub(crate) G1Affine);

impl G1Prepared {
    pub fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    pub fn from_affine(p: G1Affine) -> Self {
        G1Prepared(p)
    }
}

#[test]
fn g1_generator() {
    use SqrtField;

    let mut x = Fq::zero();
    let mut i = 0;
    loop {
        // y^2 = x^3 + b
        let mut rhs = x;
        rhs.square();
        rhs.mul_assign(&x);
        rhs.add_assign(&G1Affine::get_coeff_b());

        if let Some(y) = rhs.sqrt() {
            let yrepr = y.into_repr();
            let mut negy = y;
            negy.negate();
            let negyrepr = negy.into_repr();

            let p = G1Affine {
                x: x,
                y: if yrepr < negyrepr { y } else { negy },
                infinity: false,
            };

            let g1 = p.into_projective();
            if !g1.is_zero() {
                assert_eq!(i, 1);
                let g1 = G1Affine::from(g1);

                assert_eq!(g1, G1Affine::one());
                break;
            }
        }

        i += 1;
        x.add_assign(&Fq::one());
    }
}

#[test]

fn test_base_point_addition_and_doubling() {
    let mut a = G1::one();
    print!("{}\n\n", a);

    a.add_assign(&G1::one());

    print!("{}\n\n", a);
}

#[test]
fn g1_curve_tests() {
    crate::tests::curve::curve_tests::<G1>();
    crate::tests::curve::random_transformation_tests::<G1>();
}
