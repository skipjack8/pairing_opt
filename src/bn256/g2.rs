use super::super::bn256::check_curve_init;
use super::super::mcl::{
    mclBnFp2_add, mclBnFp2_inv, mclBnFp2_sqr, mclBnG2_add, mclBnG2_dbl, mclBnG2_neg, G2 as mcl_g2,
};
use super::g1::G1Affine;
use super::{Bn256, Fq, Fq12, Fq2, FqRepr, Fr, FrRepr};
use crate::{CurveAffine, CurveProjective, EncodedPoint, Engine, GroupDecodingError};
use ff::{BitIterator, Field, PrimeField, PrimeFieldRepr, SqrtField};
use rand::{Rand, Rng};
use std::fmt;
use std::ops::{AddAssign, MulAssign, SubAssign};

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct G2Affine {
    pub(crate) x: Fq2,
    pub(crate) y: Fq2,
    pub(crate) infinity: bool,
}

impl ::std::fmt::Display for G2Affine {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        if self.infinity {
            write!(f, "{}(Infinity)", "G2")
        } else {
            write!(f, "{}(x={}, y={})", "G2", self.x, self.y)
        }
    }
}

#[derive(Copy, Clone, Debug, Eq)]
pub struct G2(pub(crate) mcl_g2);

impl ::std::fmt::Display for G2 {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}", self.into_affine())
    }
}

impl PartialEq for G2 {
    fn eq(&self, other: &G2) -> bool {
        check_curve_init();
        self.0.eq(&other.0)
    }
}

impl G2Affine {
    fn mul_bits<S: AsRef<[u64]>>(&self, bits: BitIterator<S>) -> G2 {
        let mut res = G2::zero();
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
    fn get_point_from_x(x: Fq2, greatest: bool) -> Option<G2Affine> {
        // Compute x^3 + b
        let mut x3b = x;
        x3b.square();
        x3b.mul_assign(&x);
        x3b.add_assign(&G2Affine::get_coeff_b());

        x3b.sqrt().map(|y| {
            let mut negy = y;
            negy.negate();

            G2Affine {
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

impl CurveAffine for G2Affine {
    type Engine = Bn256;
    type Scalar = Fr;
    type Base = Fq2;
    type Prepared = G2Prepared;
    type Projective = G2;
    type Uncompressed = G2Uncompressed;
    type Compressed = G2Compressed;
    type Pair = G1Affine;
    type PairingResult = Fq12;

    fn zero() -> Self {
        G2Affine {
            x: Fq2::zero(),
            y: Fq2::one(),
            infinity: true,
        }
    }

    fn one() -> Self {
        Self::get_generator()
    }

    fn is_zero(&self) -> bool {
        self.infinity
    }

    fn mul<S: Into<<Self::Scalar as PrimeField>::Repr>>(&self, by: S) -> G2 {
        let bits = BitIterator::new(by.into());
        self.mul_bits(bits)
    }

    fn negate(&mut self) {
        if !self.is_zero() {
            self.y.negate();
        }
    }

    fn prepare(&self) -> Self::Prepared {
        G2Prepared::from_affine(*self)
    }

    fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
        self.perform_pairing(other)
    }

    fn into_projective(&self) -> G2 {
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
        G2Affine::get_coeff_b()
    }
}

impl CurveProjective for G2 {
    type Engine = Bn256;
    type Scalar = Fr;
    type Base = Fq2;
    type Affine = G2Affine;

    // The point at infinity is always represented by
    // Z = 0.
    fn zero() -> Self {
        check_curve_init();
        Self(mcl_g2::zero())
    }

    fn one() -> Self {
        G2Affine::one().into()
    }

    // The point at infinity is always represented by
    // Z = 0.
    fn is_zero(&self) -> bool {
        check_curve_init();
        self.0.is_zero()
    }

    fn is_normalized(&self) -> bool {
        self.is_zero() || self.0.z == Fq2::one().0
    }

    //TODO:: not change now
    fn batch_normalization(v: &mut [Self]) {
        // Montgomery’s Trick and Fast Implementation of Masked AES
        // Genelle, Prouff and Quisquater
        // Section 3.2

        // First pass: compute [a, ab, abc, ...]
        let mut prod = Vec::with_capacity(v.len());
        let mut tmp = Fq2::one().0;
        for g in v
            .iter_mut()
            // Ignore normalized elements
            .filter(|g| !g.is_normalized())
        {
            tmp.mul_assign(&g.0.z);
            prod.push(tmp);
        }

        // Invert `tmp`.
        unsafe { mclBnFp2_inv(&mut tmp, &tmp) }; // Guaranteed to be nonzero.

        // Second pass: iterate backwards to compute inverses
        for (g, s) in v
            .iter_mut()
            // Backwards
            .rev()
            // Ignore normalized elements
            .filter(|g| !g.is_normalized())
            // Backwards, skip last element, fill in one for last term.
            .zip(prod.into_iter().rev().skip(1).chain(Some(Fq2::one().0)))
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
            unsafe { mclBnFp2_sqr(&mut z, &z) }; // 1/z^2
            g.0.x.mul_assign(&z); // x/z^2
            z.mul_assign(&g.0.z); // 1/z^3
            g.0.y.mul_assign(&z); // y/z^3
            g.0.z = Fq2::one().0; // z = 1
        }
    }

    fn double(&mut self) {
        check_curve_init();
        unsafe { mclBnG2_dbl(&mut self.0, &self.0) };
    }

    fn add_assign(&mut self, other: &Self) {
        check_curve_init();
        unsafe { mclBnG2_add(&mut self.0, &self.0, &other.0) };
    }

    //TODO: not change now
    fn add_assign_mixed(&mut self, other: &Self::Affine) {
        if other.is_zero() {
            return;
        }

        if self.is_zero() {
            self.0.x = other.x.0;
            self.0.y = other.y.0;
            self.0.z = Fq2::one().0;
            return;
        }

        // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl

        // Z1Z1 = Z1^2
        let mut z1z1 = self.0.z;
        unsafe { mclBnFp2_sqr(&mut z1z1, &z1z1) };

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
            unsafe { mclBnFp2_sqr(&mut hh, &hh) };

            // I = 4*HH
            let mut i = hh;
            unsafe {
                mclBnFp2_add(&mut i, &i, &i);
                mclBnFp2_add(&mut i, &i, &i);
            }

            // J = H*I
            let mut j = h;
            j.mul_assign(&i);

            // r = 2*(S2-Y1)
            let mut r = s2;
            r.sub_assign(&self.0.y);
            unsafe {
                mclBnFp2_add(&mut r, &r, &r);
            }

            // V = X1*I
            let mut v = self.0.x;
            v.mul_assign(&i);

            // X3 = r^2 - J - 2*V
            self.0.x = r;
            unsafe { mclBnFp2_sqr(&mut self.0.x, &self.0.x) };
            self.0.x.sub_assign(&j);
            self.0.x.sub_assign(&v);
            self.0.x.sub_assign(&v);

            // Y3 = r*(V-X3)-2*Y1*J
            j.mul_assign(&self.0.y); // J = 2*Y1*J
            unsafe { mclBnFp2_add(&mut j, &j, &j) };
            self.0.y = v;
            self.0.y.sub_assign(&self.0.x);
            self.0.y.mul_assign(&r);
            self.0.y.sub_assign(&j);

            // Z3 = (Z1+H)^2-Z1Z1-HH
            self.0.z.add_assign(&h);
            unsafe { mclBnFp2_sqr(&mut self.0.z, &self.0.z) };
            self.0.z.sub_assign(&z1z1);
            self.0.z.sub_assign(&hh);
        }
    }

    fn negate(&mut self) {
        check_curve_init();
        unsafe { mclBnG2_neg(&mut self.0, &self.0) };
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

    fn into_affine(&self) -> G2Affine {
        (*self).into()
    }

    fn recommended_wnaf_for_scalar(scalar: <Self::Scalar as PrimeField>::Repr) -> usize {
        Self::empirical_recommended_wnaf_for_scalar(scalar)
    }

    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        Self::empirical_recommended_wnaf_for_num_scalars(num_scalars)
    }

    fn as_xyz(&self) -> (&Self::Base, &Self::Base, &Self::Base) {
        unimplemented!("do not implement");
    }

    fn into_xyz_unchecked(self) -> (Self::Base, Self::Base, Self::Base) {
        (Fq2(self.0.x), Fq2(self.0.y), Fq2(self.0.z))
    }

    fn from_xyz_unchecked(x: Self::Base, y: Self::Base, z: Self::Base) -> Self {
        Self(mcl_g2 {
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
impl From<G2Affine> for G2 {
    fn from(p: G2Affine) -> G2 {
        if p.is_zero() {
            G2::zero()
        } else {
            G2(mcl_g2 {
                x: p.x.0,
                y: p.y.0,
                z: Fq2::one().0,
            })
        }
    }
}

// The projective point X, Y, Z is represented in the affine
// coordinates as X/Z^2, Y/Z^3.
impl From<G2> for G2Affine {
    fn from(p: G2) -> G2Affine {
        if p.is_zero() {
            G2Affine::zero()
        } else if p.0.z == Fq2::one().0 {
            // If Z is one, the point is already normalized.
            G2Affine {
                x: Fq2(p.0.x),
                y: Fq2(p.0.y),
                infinity: false,
            }
        } else {
            let mut p_norm = unsafe { mcl_g2::uninit() };
            mcl_g2::normalize(&mut p_norm, &p.0);

            G2Affine {
                x: Fq2(p_norm.x),
                y: Fq2(p_norm.y),
                infinity: false,
            }
        }
    }
}

impl Rand for G2 {
    fn rand<R: Rng>(rng: &mut R) -> Self {
        loop {
            let x = rng.gen();
            let greatest = rng.gen();

            if let Some(p) = G2Affine::get_point_from_x(x, greatest) {
                if !p.is_zero() {
                    if p.is_on_curve() {
                        return p.scale_by_cofactor();
                    }
                }
            }
        }
    }
}

impl Rand for G2Affine {
    fn rand<R: Rng>(rng: &mut R) -> Self {
        let r = G2::rand(rng);
        return r.into_affine();
    }
}

#[derive(Copy, Clone)]
pub struct G2Uncompressed([u8; 128]);

impl AsRef<[u8]> for G2Uncompressed {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsMut<[u8]> for G2Uncompressed {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl fmt::Debug for G2Uncompressed {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.0[..].fmt(formatter)
    }
}

impl EncodedPoint for G2Uncompressed {
    type Affine = G2Affine;

    fn empty() -> Self {
        G2Uncompressed([0; 128])
    }
    fn size() -> usize {
        128
    }
    fn into_affine(&self) -> Result<G2Affine, GroupDecodingError> {
        let affine = self.into_affine_unchecked()?;

        if !affine.is_on_curve() {
            Err(GroupDecodingError::NotOnCurve)
        } else {
            Ok(affine)
        }
    }
    fn into_affine_unchecked(&self) -> Result<G2Affine, GroupDecodingError> {
        // Create a copy of this representation.
        let mut copy = self.0;

        if copy[0] & (1 << 7) != 0 {
            // Distinguisher bit is set, but this should be uncompressed!
            return Err(GroupDecodingError::UnexpectedCompressionMode);
        }

        if copy[0] & (1 << 6) != 0 {
            // This is the point at infinity, which means that if we mask away
            // the first two bits, the entire representation should consist
            // of zeroes.
            copy[0] &= 0x3f;

            if copy.iter().all(|b| *b == 0) {
                Ok(G2Affine::zero())
            } else {
                Err(GroupDecodingError::UnexpectedInformation)
            }
        } else {
            // Unset the two most significant bits.
            copy[0] &= 0x3f;

            let mut x_c0 = FqRepr([0; 4]);
            let mut x_c1 = FqRepr([0; 4]);
            let mut y_c0 = FqRepr([0; 4]);
            let mut y_c1 = FqRepr([0; 4]);

            {
                let mut reader = &copy[..];

                x_c1.read_be(&mut reader).unwrap();
                x_c0.read_be(&mut reader).unwrap();
                y_c1.read_be(&mut reader).unwrap();
                y_c0.read_be(&mut reader).unwrap();
            }

            let x_c0 = Fq::from_repr(x_c0)
                .map_err(|e| GroupDecodingError::CoordinateDecodingError("x coordinate (c0)", e))?;
            let x_c1 = Fq::from_repr(x_c1)
                .map_err(|e| GroupDecodingError::CoordinateDecodingError("x coordinate (c1)", e))?;
            let y_c0 = Fq::from_repr(y_c0)
                .map_err(|e| GroupDecodingError::CoordinateDecodingError("y coordinate (c0)", e))?;
            let y_c1 = Fq::from_repr(y_c1)
                .map_err(|e| GroupDecodingError::CoordinateDecodingError("y coordinate (c1)", e))?;

            Ok(G2Affine {
                x: Fq2::from_fq(x_c0, x_c1),
                y: Fq2::from_fq(y_c0, y_c1),
                infinity: false,
            })
        }
    }
    fn from_affine(affine: G2Affine) -> Self {
        let mut res = Self::empty();

        if affine.is_zero() {
            // Set the second-most significant bit to indicate this point
            // is at infinity.
            res.0[0] |= 1 << 6;
        } else {
            let mut writer = &mut res.0[..];

            affine.x.c1().into_repr().write_be(&mut writer).unwrap();
            affine.x.c0().into_repr().write_be(&mut writer).unwrap();
            affine.y.c1().into_repr().write_be(&mut writer).unwrap();
            affine.y.c0().into_repr().write_be(&mut writer).unwrap();
        }

        res
    }
}

#[derive(Copy, Clone)]
pub struct G2Compressed([u8; 64]);

impl AsRef<[u8]> for G2Compressed {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsMut<[u8]> for G2Compressed {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl fmt::Debug for G2Compressed {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.0[..].fmt(formatter)
    }
}

impl EncodedPoint for G2Compressed {
    type Affine = G2Affine;

    fn empty() -> Self {
        G2Compressed([0; 64])
    }
    fn size() -> usize {
        64
    }
    fn into_affine(&self) -> Result<G2Affine, GroupDecodingError> {
        let affine = self.into_affine_unchecked()?;

        // NB: Decompression guarantees that it is on the curve already.

        Ok(affine)
    }
    fn into_affine_unchecked(&self) -> Result<G2Affine, GroupDecodingError> {
        // Create a copy of this representation.
        let mut copy = self.0;

        if copy[0] & (1 << 6) != 0 {
            // This is the point at infinity, which means that if we mask away
            // the first two bits, the entire representation should consist
            // of zeroes.
            copy[0] &= 0x3f;

            if copy.iter().all(|b| *b == 0) {
                Ok(G2Affine::zero())
            } else {
                Err(GroupDecodingError::UnexpectedInformation)
            }
        } else {
            // Determine if the intended y coordinate must be greater
            // lexicographically.
            let greatest = copy[0] & (1 << 7) != 0;

            // Unset the two most significant bits.
            copy[0] &= 0x3f;

            let mut x_c1 = FqRepr([0; 4]);
            let mut x_c0 = FqRepr([0; 4]);

            {
                let mut reader = &copy[..];

                x_c1.read_be(&mut reader).unwrap();
                x_c0.read_be(&mut reader).unwrap();
            }

            let x_c0 = Fq::from_repr(x_c0)
                .map_err(|e| GroupDecodingError::CoordinateDecodingError("x coordinate (c0)", e))?;
            let x_c1 = Fq::from_repr(x_c1)
                .map_err(|e| GroupDecodingError::CoordinateDecodingError("x coordinate (c1)", e))?;

            // Interpret as Fq element.
            let x = Fq2::from_fq(x_c0, x_c1);

            G2Affine::get_point_from_x(x, greatest).ok_or(GroupDecodingError::NotOnCurve)
        }
    }
    fn from_affine(affine: G2Affine) -> Self {
        let mut res = Self::empty();

        if affine.is_zero() {
            // Set the second-most significant bit to indicate this point
            // is at infinity.
            res.0[0] |= 1 << 6;
        } else {
            {
                let mut writer = &mut res.0[..];

                affine.x.c1().into_repr().write_be(&mut writer).unwrap();
                affine.x.c0().into_repr().write_be(&mut writer).unwrap();
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

impl G2Affine {
    fn scale_by_cofactor(&self) -> G2 {
        // G2 cofactor = 2p - n = 2q - r
        // 0x30644e72e131a029b85045b68181585e06ceecda572a2489345f2299c0f9fa8d
        let cofactor = BitIterator::new([
            0x345f2299c0f9fa8d,
            0x06ceecda572a2489,
            0xb85045b68181585e,
            0x30644e72e131a029,
        ]);
        self.mul_bits(cofactor)
    }

    fn get_generator() -> Self {
        G2Affine {
            x: Fq2::from_fq(super::fq::G2_GENERATOR_X_C0, super::fq::G2_GENERATOR_X_C1),
            y: Fq2::from_fq(super::fq::G2_GENERATOR_Y_C0, super::fq::G2_GENERATOR_Y_C1),
            infinity: false,
        }
    }

    fn get_coeff_b() -> Fq2 {
        super::fq::B_COEFF_FQ2
    }

    fn perform_pairing(&self, other: &G1Affine) -> Fq12 {
        super::Bn256::pairing(*other, *self)
    }
}

impl G2 {
    fn empirical_recommended_wnaf_for_scalar(scalar: FrRepr) -> usize {
        let num_bits = scalar.num_bits() as usize;

        if num_bits >= 103 {
            4
        } else if num_bits >= 37 {
            3
        } else {
            2
        }
    }

    fn empirical_recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        const RECOMMENDATIONS: [usize; 11] = [1, 3, 8, 20, 47, 126, 260, 826, 1501, 4555, 84071];

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
pub struct G2Prepared {
    pub(crate) coeffs: Vec<(Fq2, Fq2, Fq2)>,
    pub(crate) infinity: bool,
}

// This generator does not take a random element in Fp2
// and tries to increment it to be on a curve, but
// generates a random scalar and multiplies predefined generator by it

#[test]
fn g2_generator() {
    use SqrtField;

    let mut x = Fq2::zero();
    loop {
        // y^2 = x^3 + b
        let mut rhs = x;
        rhs.square();
        rhs.mul_assign(&x);
        rhs.add_assign(&G2Affine::get_coeff_b());

        if let Some(y) = rhs.sqrt() {
            let mut negy = y;
            negy.negate();

            let p = G2Affine {
                x: x,
                y: if y < negy { y } else { negy },
                infinity: false,
            };

            let g2 = p.into_projective();
            if !g2.is_zero() {
                let _g2 = G2Affine::from(g2);
                break;
            }
        }

        x.add_assign(&Fq2::one());
    }
}

#[test]
fn test_generate_g2_in_subgroup() {
    use SqrtField;

    let mut x = Fq2::zero();
    loop {
        // y^2 = x^3 + b
        let mut rhs = x;
        rhs.square();
        rhs.mul_assign(&x);
        rhs.add_assign(&G2Affine::get_coeff_b());

        if let Some(y) = rhs.sqrt() {
            let mut negy = y;
            negy.negate();

            let p = G2Affine {
                x: x,
                y: if y < negy { y } else { negy },
                infinity: false,
            };

            let g2 = p.into_projective();
            let mut minus_one = Fr::one();
            minus_one.negate();

            let mut expected_zero = p.mul(minus_one);
            expected_zero.add_assign(&g2);

            if !expected_zero.is_zero() {
                let p = expected_zero.into_affine();
                let scaled_by_cofactor = p.scale_by_cofactor();
                if scaled_by_cofactor.is_zero() {
                    let g2 = G2Affine::from(expected_zero);
                    println!("Invalid subgroup point = {}", g2);
                    return;
                }
            }
        }

        x.add_assign(&Fq2::one());
    }
}

#[cfg(test)]
use rand::{SeedableRng, XorShiftRng};

#[test]
fn g2_generator_on_curve() {
    use SqrtField;

    let gen = G2Affine::get_generator();
    let x = gen.x;
    // y^2 = x^3 + 3/xi
    let mut rhs = x;
    rhs.square();
    rhs.mul_assign(&x);
    rhs.add_assign(&G2Affine::get_coeff_b());

    if let Some(y) = rhs.sqrt() {
        let mut negy = y;
        negy.negate();

        let p = G2Affine {
            x: x,
            y: if y < negy { y } else { negy },
            infinity: false,
        };

        assert_eq!(p.y, gen.y);
        assert_eq!(p, G2Affine::one());
        return;
    }
    panic!();
}

#[test]
fn g2_curve_tests() {
    crate::tests::curve::curve_tests::<G2>();
    crate::tests::curve::random_transformation_tests::<G2>();
}

#[test]

fn test_b_coeff() {
    let b2 = G2Affine::get_coeff_b();
    print!("{}\n\n", b2);
}

#[test]

fn test_base_point_addition_and_doubling() {
    let mut two = G2::one();
    two.add_assign(&G2::one());

    let one = G2::one();

    let mut three21 = two;
    three21.add_assign(&one);

    let mut three12 = one;
    three12.add_assign(&two);

    assert_eq!(three12, three21);
}

#[test]
fn test_addition_and_doubling() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        let a = G2::rand(&mut rng);
        assert!(a.into_affine().is_on_curve());
        let b = G2::rand(&mut rng);
        let c = G2::rand(&mut rng);
        let a_affine = a.into_affine();
        let b_affine = b.into_affine();
        let c_affine = c.into_affine();

        // a + a should equal the doubling
        {
            let mut aplusa = a;
            aplusa.add_assign(&a);

            let mut aplusamixed = a;
            aplusamixed.add_assign_mixed(&a.into_affine());

            let mut adouble = a;
            adouble.double();

            assert_eq!(aplusa, adouble);
            assert_eq!(aplusamixed, adouble);
        }

        let mut ab = a;
        ab.add_assign(&b);

        let mut ba = b;
        ba.add_assign(&a);

        assert_eq!(ab, ba, "Addition should not depend on order");

        let mut tmp = vec![G2::zero(); 6];

        // (a + b) + c
        tmp[0] = a;
        tmp[0].add_assign(&b);
        tmp[0].add_assign(&c);

        // a + (b + c)
        tmp[1] = b;
        tmp[1].add_assign(&c);
        tmp[1].add_assign(&a);

        // (a + c) + b
        tmp[2] = a;
        tmp[2].add_assign(&c);
        tmp[2].add_assign(&b);

        // Mixed addition

        // (a + b) + c
        tmp[3] = a_affine.into_projective();
        tmp[3].add_assign_mixed(&b_affine);
        tmp[3].add_assign_mixed(&c_affine);

        // a + (b + c)
        tmp[4] = b_affine.into_projective();
        tmp[4].add_assign_mixed(&c_affine);
        tmp[4].add_assign_mixed(&a_affine);

        // (a + c) + b
        tmp[5] = a_affine.into_projective();
        tmp[5].add_assign_mixed(&c_affine);
        tmp[5].add_assign_mixed(&b_affine);

        // Comparisons
        for i in 0..6 {
            for j in 0..6 {
                assert_eq!(tmp[i], tmp[j]);
                assert_eq!(tmp[i].into_affine(), tmp[j].into_affine());
            }

            assert!(tmp[i] != a);
            assert!(tmp[i] != b);
            assert!(tmp[i] != c);

            assert!(a != tmp[i]);
            assert!(b != tmp[i]);
            assert!(c != tmp[i]);
        }
    }
}

#[test]
fn random_negation_tests() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        // let r = G2::rand(&mut rng);
        // assert!(r.into_affine().is_on_curve());

        let mut r = G2::one();
        let k = Fr::rand(&mut rng);
        r.mul_assign(k);

        let s = Fr::rand(&mut rng);
        let mut sneg = s;
        sneg.negate();

        let mut t1 = r;
        t1.mul_assign(s);

        let mut t2 = r;
        t2.mul_assign(sneg);

        let mut t3 = t1;
        t3.add_assign(&t2);
        assert!(t3.is_zero());

        let mut t4 = t1;
        t4.add_assign_mixed(&t2.into_affine());
        assert!(t4.is_zero());

        t1.negate();
        assert_eq!(t1, t2);
    }
}

#[test]
fn mul_by_order_tests() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    for _ in 0..1000 {
        // let r = G2::rand(&mut rng);

        let mut r = G2::one();
        let k = Fr::rand(&mut rng);
        r.mul_assign(k);

        let order = Fr::char();

        let mut q = G2::one();
        q.mul_assign(order);
        assert!(q.is_zero());

        r.mul_assign(order);
        assert!(r.is_zero());

        let mut t = G2::rand(&mut rng);
        t.mul_assign(order);
        assert!(t.is_zero());
    }
}
