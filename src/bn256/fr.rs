//! An implementation of the BN256 mcl_fr field $\mathbb{F}_q$
//! where `q = 21888242871839275222246405745257275088548364400416034343698204186575808495617`
//! where `generator = 7`
use core::{
    cmp, fmt, mem,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use std::hash::{Hash, Hasher};

use crate::bn256::check_curve_init;
use crate::mcl::Fr as mcl_fr;
use crate::mcl::*;
use ff::{Field, PrimeField, PrimeFieldDecodingError};

/// Represents an element of the scalar field $\mathbb{F}_q$ of the BN256 elliptic
/// curve construction.
///
/// The inner representation is stored in Montgomery form.

#[derive(Default, Clone, Copy)]
pub struct Fr(pub(crate) mcl_fr);

/// Representation of a `Fr`, in regular coordinates.
#[derive(Copy, Clone, Default)]
pub struct FrRepr(pub [u64; 4]);

impl AsRef<[u64]> for FrRepr {
    fn as_ref(&self) -> &[u64] {
        &self.0
    }
}

impl AsMut<[u64]> for FrRepr {
    fn as_mut(&mut self) -> &mut [u64] {
        &mut self.0
    }
}

impl AsRef<mcl_fr> for Fr {
    fn as_ref(&self) -> &mcl_fr {
        &self.0
    }
}

impl AsMut<mcl_fr> for Fr {
    fn as_mut(&mut self) -> &mut mcl_fr {
        &mut self.0
    }
}

const LIMBS: usize = 4;
const LIMB_BITS: usize = 64;

//21888242871839275222246405745257275088548364400416034343698204186575808495617
const MODULUS: FrRepr = FrRepr([
    0x43e1f593f0000001,
    0x2833e84879b97091,
    0xb85045b68181585d,
    0x30644e72e131a029,
]);

/// R = 2^256 mod q
const R: FrRepr = FrRepr([1, 0, 0, 0]);

impl fmt::Debug for FrRepr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "0x")?;
        for &b in self.0.iter().rev() {
            write!(f, "{:016x}", b)?;
        }
        Ok(())
    }
}

impl fmt::Display for FrRepr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "0x")?;
        for &b in self.0.iter().rev() {
            write!(f, "{:016x}", b)?;
        }
        Ok(())
    }
}

impl From<u64> for FrRepr {
    fn from(val: u64) -> FrRepr {
        FrRepr([val, 0, 0, 0])
    }
}

impl Ord for FrRepr {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        for (a, b) in self.0.iter().rev().zip(other.0.iter().rev()) {
            match a.cmp(b) {
                cmp::Ordering::Greater => {
                    return cmp::Ordering::Greater;
                }
                cmp::Ordering::Less => {
                    return cmp::Ordering::Less;
                }
                cmp::Ordering::Equal => {}
            }
        }

        cmp::Ordering::Equal
    }
}

impl PartialOrd for FrRepr {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for FrRepr {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl Eq for FrRepr {}

impl Hash for FrRepr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for limb in self.as_ref().iter() {
            limb.hash(state);
        }
    }
}

impl ::rand::Rand for FrRepr {
    #[inline(always)]
    fn rand<R: ::rand::Rng>(rng: &mut R) -> Self {
        FrRepr(rng.gen())
    }
}

impl ff::PrimeFieldRepr for FrRepr {
    fn sub_noborrow(&mut self, other: &Self) {
        let mut borrow = 0;

        for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
            *a = ff::sbb(*a, *b, &mut borrow);
        }
    }

    fn add_nocarry(&mut self, other: &Self) {
        let mut carry = 0;

        for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
            *a = ff::adc(*a, *b, &mut carry);
        }
    }

    fn num_bits(&self) -> u32 {
        let mut ret = (LIMBS as u32) * LIMB_BITS as u32;
        for i in self.0.iter().rev() {
            let leading = i.leading_zeros();
            ret -= leading;
            if leading != LIMB_BITS as u32 {
                break;
            }
        }

        ret
    }

    fn is_zero(&self) -> bool {
        self.0.iter().all(|&e| e == 0)
    }

    fn is_odd(&self) -> bool {
        self.0[0] & 1 == 1
    }

    fn is_even(&self) -> bool {
        !self.is_odd()
    }

    fn div2(&mut self) {
        let mut t = 0;
        for i in self.0.iter_mut().rev() {
            let t2 = *i << 63;
            *i >>= 1;
            *i |= t;
            t = t2;
        }
    }

    fn shr(&mut self, mut n: u32) {
        if n as usize >= LIMB_BITS * LIMBS {
            *self = Self::from(0);
            return;
        }

        while n >= LIMB_BITS as u32 {
            let mut t = 0;
            for i in self.0.iter_mut().rev() {
                mem::swap(&mut t, i);
            }
            n -= LIMB_BITS as u32;
        }

        if n > 0 {
            let mut t = 0;
            for i in self.0.iter_mut().rev() {
                let t2 = *i << (LIMB_BITS as u32 - n);
                *i >>= n;
                *i |= t;
                t = t2;
            }
        }
    }

    fn mul2(&mut self) {
        let mut last = 0;
        for i in &mut self.0 {
            let tmp = *i >> 63;
            *i <<= 1;
            *i |= last;
            last = tmp;
        }
    }

    fn shl(&mut self, mut n: u32) {
        if n as usize >= LIMB_BITS * LIMBS {
            *self = Self::from(0);
            return;
        }

        while n >= LIMB_BITS as u32 {
            let mut t = 0;
            for i in &mut self.0 {
                mem::swap(&mut t, i);
            }
            n -= LIMB_BITS as u32;
        }

        if n > 0 {
            let mut t = 0;
            for i in &mut self.0 {
                let t2 = *i >> (LIMB_BITS as u32 - n);
                *i <<= n;
                *i |= t;
                t = t2;
            }
        }
    }
}

pub const S: u32 = 28;

impl fmt::Debug for Fr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Fr({:?})", self.into_repr())
    }
}

impl fmt::Display for Fr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Fr({})", self.into_repr())
    }
}

impl PartialEq for Fr {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0.d[0] == other.0.d[0]
            && self.0.d[1] == other.0.d[1]
            && self.0.d[2] == other.0.d[2]
            && self.0.d[3] == other.0.d[3]
    }
}
impl Eq for Fr {}

impl Ord for Fr {
    #[inline(always)]
    fn cmp(&self, other: &Fr) -> ::std::cmp::Ordering {
        self.into_repr().cmp(&other.into_repr())
    }
}

impl PartialOrd for Fr {
    #[inline(always)]
    fn partial_cmp(&self, other: &Fr) -> Option<::std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl From<Fr> for FrRepr {
    fn from(val: Fr) -> Self {
        val.into_repr()
    }
}

impl From<Fr> for mcl_fr {
    fn from(val: Fr) -> mcl_fr {
        val.0
    }
}

impl From<mcl_fr> for Fr {
    fn from(val: mcl_fr) -> Fr {
        Fr(val)
    }
}

impl From<u64> for Fr {
    fn from(val: u64) -> Fr {
        Fr::from_repr(FrRepr::from(val)).expect("u64 is alaways in the field")
    }
}

impl<'a> Neg for &'a Fr {
    type Output = Fr;

    #[inline]
    fn neg(self) -> Fr {
        let mut out = *self;
        out.negate();

        out
    }
}

impl Neg for Fr {
    type Output = Fr;

    #[inline]
    fn neg(self) -> Fr {
        -&self
    }
}

impl<'a, 'b> Sub<&'b Fr> for &'a Fr {
    type Output = Fr;

    #[inline]
    fn sub(self, rhs: &'b Fr) -> Fr {
        self.sub(rhs)
    }
}

impl<'a, 'b> Add<&'b Fr> for &'a Fr {
    type Output = Fr;

    #[inline]
    fn add(self, rhs: &'b Fr) -> Fr {
        self.add(rhs)
    }
}

impl<'a, 'b> Mul<&'b Fr> for &'a Fr {
    type Output = Fr;

    #[inline]
    fn mul(self, rhs: &'b Fr) -> Fr {
        self.mul(rhs)
    }
}

impl ff::Field for Fr {
    fn zero() -> Self {
        Fr(mcl_fr { d: [0, 0, 0, 0] })
    }

    fn one() -> Self {
        Fr(mcl_fr {
            d: [
                0xac96341c4ffffffb,
                0x36fc76959f60cd29,
                0x666ea36f7879462e,
                0xe0a77c19a07df2f,
            ],
        })
    }

    fn is_zero(&self) -> bool {
        self == &Self::zero()
    }

    fn square(&mut self) {
        check_curve_init();
        unsafe { mclBnFr_sqr(&mut self.0, &self.0) }
    }

    fn double(&mut self) {
        check_curve_init();
        unsafe { mclBnFr_add(self.as_mut(), self.as_ref(), self.as_ref()) }
    }

    fn negate(&mut self) {
        check_curve_init();
        unsafe { mclBnFr_neg(self.as_mut(), self.as_ref()) };
    }

    fn add_assign(&mut self, other: &Self) {
        check_curve_init();
        self.as_mut().add_assign(other.as_ref());
    }

    fn sub_assign(&mut self, other: &Self) {
        check_curve_init();
        self.as_mut().sub_assign(other.as_ref());
    }

    fn mul_assign(&mut self, other: &Self) {
        check_curve_init();
        self.as_mut().mul_assign(other.as_ref());
    }

    fn inverse(&self) -> Option<Self> {
        check_curve_init();
        if self.is_zero() {
            return None;
        }

        let mut x = unsafe { mcl_fr::uninit() };
        mcl_fr::inv(&mut x, self.as_ref());

        Some(Fr(x))
    }

    fn frobenius_map(&mut self, _: usize) {
        // This has no effect in a prime field.
    }
}

impl Hash for Fr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for limb in self.as_ref().d.iter() {
            limb.hash(state);
        }
    }
}

impl ::rand::Rand for Fr {
    /// Computes a uniformly random element using rejection sampling.
    /// `_rng` is for compatible with old call
    fn rand<R: ::rand::Rng>(_rng: &mut R) -> Self {
        check_curve_init();
        let mut x = mcl_fr::default();
        x.set_by_csprng();
        Fr(x)
    }
}

impl FrRepr {
    pub const fn new(raw: [u64; 4]) -> Self {
        FrRepr(raw)
    }
}

const R2: Fr = Fr(mcl_fr {
    d: [
        0x1bb8e645ae216da7,
        0x53fe3ab1e35c59e3,
        0x8c49833d53bb8085,
        0x0216d0b17f4e44a5,
    ],
});
impl ff::PrimeField for Fr {
    type Repr = FrRepr;

    fn from_repr(repr: Self::Repr) -> Result<Self, ff::PrimeFieldDecodingError> {
        if FrRepr(repr.0) < MODULUS {
            let mut out = Fr(mcl_fr { d: repr.0 });
            out.mul_assign(&R2);

            Ok(out)
        } else {
            Err(ff::PrimeFieldDecodingError::NotInField(
                "not in field".to_string(),
            ))
        }
    }
    fn from_raw_repr(repr: Self::Repr) -> Result<Self, PrimeFieldDecodingError> {
        if FrRepr(repr.0) < MODULUS {
            Ok(Fr(mcl_fr { d: repr.0 }))
        } else {
            Err(ff::PrimeFieldDecodingError::NotInField(
                "not in field".to_string(),
            ))
        }
    }
    /// Convert a biginteger representation into a prime field element, if
    /// the number is an element of the field.
    fn into_repr(&self) -> Self::Repr {
        check_curve_init();
        let mut out = unsafe { mcl_fr::uninit() };
        mcl_fr::mul(&mut out, self.as_ref(), &mcl_fr { d: R.0 });
        FrRepr(out.d)
    }

    fn into_raw_repr(&self) -> Self::Repr {
        FrRepr(self.0.d)
    }

    fn char() -> Self::Repr {
        MODULUS
    }

    const NUM_BITS: u32 = 254;

    const CAPACITY: u32 = 253;
    fn multiplicative_generator() -> Self {
        Fr::from_repr(FrRepr::new([7, 0, 0, 0])).unwrap()
    }

    const S: u32 = S;

    // 2 ^ s * t = modulus -1, root_of_unity = 7 ^ t
    fn root_of_unity() -> Self {
        Fr(mcl_fr {
            d: [
                0x9632c7c5b639feb8,
                0x985ce3400d0ff299,
                0xb2dd880001b0ecd8,
                0x1d69070d6d98ce29,
            ],
        })
    }
}

impl ff::SqrtField for Fr {
    fn legendre(&self) -> ff::LegendreSymbol {
        const MOD_MINUS_1_OVER_2: [u64; 4] = [
            0xa1f0fac9f8000000,
            0x9419f4243cdcb848,
            0xdc2822db40c0ac2e,
            0x183227397098d014,
        ];
        // s = self^((modulus - 1) // 2)
        let s = self.pow(MOD_MINUS_1_OVER_2);
        if s == Self::zero() {
            ff::LegendreSymbol::Zero
        } else if s == Self::one() {
            ff::LegendreSymbol::QuadraticResidue
        } else {
            ff::LegendreSymbol::QuadraticNonResidue
        }
    }

    fn sqrt(&self) -> Option<Self> {
        // Tonelli-Shank's algorithm for q mod 16 = 1
        // https://eprint.iacr.org/2012/685.pdf (page 12, algorithm 5)
        match self.legendre() {
            ff::LegendreSymbol::Zero => Some(*self),
            ff::LegendreSymbol::QuadraticNonResidue => None,
            ff::LegendreSymbol::QuadraticResidue => {
                let mut c = Self::root_of_unity();
                //r = self.pow(t_plus_1_over_2)
                let mut r = self.pow([
                    0xcdcb848a1f0faca0,
                    0xc0ac2e9419f4243,
                    0x98d014dc2822db4,
                    0x183227397,
                ]);
                let mut t = self.pow([
                    0x9b9709143e1f593f,
                    0x181585d2833e8487,
                    0x131a029b85045b68,
                    0x30644e72e,
                ]);
                let mut m = S;

                while t != Self::one() {
                    let mut i = 1;
                    {
                        let mut t2i = t;
                        t2i.square();
                        loop {
                            if t2i == Self::one() {
                                break;
                            }
                            t2i.square();
                            i += 1;
                        }
                    }

                    for _ in 0..(m - i - 1) {
                        c.square();
                    }
                    r = r.mul(&c);
                    c.square();
                    t = t.mul(&c);
                    m = i;
                }

                Some(r)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct NotInFieldError;

impl fmt::Display for NotInFieldError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Not in field")
    }
}

impl std::error::Error for NotInFieldError {}

impl Fr {
    /// Attempts to convert a little-endian byte representation of
    /// a Fr into a `Fr`, failing if the input is not canonical.
    pub fn from_bytes_le(bytes: &[u8; 32]) -> Option<Fr> {
        check_curve_init();
        let mut raw = unsafe { mcl_fr::uninit() };

        let l = raw.deserialize(bytes);

        if l {
            Some(Fr(raw))
        } else {
            None
        }
    }

    /// Attempts to convert a big-endian byte representation of
    /// a Fr into a `Fr`, failing if the input is not canonical.
    pub fn from_bytes_be(bytes: &[u8; 32]) -> Option<Fr> {
        let mut bytes = bytes.clone();
        bytes.reverse();

        Fr::from_bytes_le(&bytes)
    }

    /// Converts an element of `Fr` into a byte representation in
    /// little-endian byte order.
    pub fn to_bytes_le(&self) -> [u8; 32] {
        check_curve_init();

        let mut out = [0u8; 32];
        out.copy_from_slice(&self.0.serialize());

        out
    }

    /// Converts an element of `Fr` into a byte representation in
    /// big-endian byte order.
    pub fn to_bytes_be(&self) -> [u8; 32] {
        let mut out = self.to_bytes_le();
        out.reverse();

        out
    }

    /// Multiplies `rhs` by `self`, returning the result.
    #[inline]
    pub fn mul(&self, rhs: &Self) -> Self {
        check_curve_init();

        let mut out = unsafe { mcl_fr::uninit() };
        mcl_fr::mul(&mut out, self.as_ref(), rhs.as_ref());

        Fr(out)
    }

    /// Subtracts `rhs` from `self`, returning the result.
    #[inline]
    pub fn sub(&self, rhs: &Self) -> Self {
        check_curve_init();

        let mut out = unsafe { mcl_fr::uninit() };
        mcl_fr::sub(&mut out, self.as_ref(), rhs.as_ref());

        Fr(out)
    }

    /// Adds `rhs` to `self`, returning the result.
    #[inline]
    pub fn add(&self, rhs: &Self) -> Self {
        check_curve_init();

        let mut out = unsafe { mcl_fr::uninit() };
        mcl_fr::add(&mut out, self.as_ref(), rhs.as_ref());

        Fr(out)
    }

    /// Returns true if this element is zero.
    pub fn is_zero(&self) -> bool {
        self.0.d.iter().all(|&e| e == 0)
    }

    #[inline(always)]
    fn is_valid(&self) -> bool {
        check_curve_init();
        self.0.is_valid()
    }
}

#[cfg(test)]
mod tests {
    use super::{Fr, FrRepr, MODULUS, R};
    use crate::mcl::Fr as mcl_fr;
    use crate::rand::Rand;
    use ff::{Field, PrimeField, PrimeFieldRepr, SqrtField};

    /// INV = -(q^{-1} mod 2^64) mod 2^64
    const INV: u64 = 0xc2e1f593efffffff;

    /// R^2 = 2^512 mod q
    const R2: FrRepr = FrRepr([
        0x1bb8e645ae216da7,
        0x53fe3ab1e35c59e3,
        0x8c49833d53bb8085,
        0x216d0b17f4e44a5,
    ]);

    const LARGEST: Fr = Fr(mcl_fr {
        d: [
            0x43e1f593f0000000,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ],
    });

    #[test]
    fn test_inv() {
        // Compute -(q^{-1} mod 2^64) mod 2^64 by exponentiating
        // by totient(2**64) - 1

        let mut inv = 1u64;
        for _ in 0..63 {
            inv = inv.wrapping_mul(inv);
            inv = inv.wrapping_mul(MODULUS.0[0]);
        }
        inv = inv.wrapping_neg();

        assert_eq!(inv, INV);
    }

    #[test]
    fn test_debug() {
        assert_eq!(
            format!("{:?}", Fr::zero()),
            "Fr(0x0000000000000000000000000000000000000000000000000000000000000000)"
        );
        assert_eq!(
            format!("{:?}", Fr::one()),
            "Fr(0x0000000000000000000000000000000000000000000000000000000000000001)"
        );
        assert_eq!(
            format!("{:?}", Fr::from_repr(R2).unwrap()),
            "Fr(0x0216d0b17f4e44a58c49833d53bb808553fe3ab1e35c59e31bb8e645ae216da7)"
        );
    }

    #[test]
    fn test_equality() {
        assert_eq!(Fr::zero(), Fr::zero());
        assert_eq!(Fr::one(), Fr::one());
        assert_eq!(Fr::from_repr(R2).unwrap(), Fr::from_repr(R2).unwrap());

        assert_ne!(Fr::zero(), Fr::one());
        assert_ne!(Fr::one(), Fr::from_repr(R2).unwrap());
    }

    #[test]
    fn test_to_bytes() {
        assert_eq!(
            Fr::zero().to_bytes_le(),
            [
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0
            ]
        );

        assert_eq!(
            Fr::one().to_bytes_le(),
            [
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0
            ]
        );

        assert_eq!(
            Fr::from_repr(R2).unwrap().to_bytes_le(),
            [
                167, 109, 33, 174, 69, 230, 184, 27, 227, 89, 92, 227, 177, 58, 254, 83, 133, 128,
                187, 83, 61, 131, 73, 140, 165, 68, 78, 127, 177, 208, 22, 2
            ]
        );

        assert_eq!(
            (-&Fr::one()).to_bytes_le(),
            [
                0, 0, 0, 240, 147, 245, 225, 67, 145, 112, 185, 121, 72, 232, 51, 40, 93, 88, 129,
                129, 182, 69, 80, 184, 41, 160, 49, 225, 114, 78, 100, 48,
            ]
        );
    }

    #[test]
    fn test_from_bytes() {
        assert_eq!(
            Fr::from_bytes_le(&[
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0
            ])
            .unwrap(),
            Fr::zero()
        );

        assert_eq!(
            Fr::from_bytes_le(&[
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0
            ])
            .unwrap(),
            Fr::one()
        );

        assert_eq!(
            Fr::from_bytes_le(&[
                167, 109, 33, 174, 69, 230, 184, 27, 227, 89, 92, 227, 177, 58, 254, 83, 133, 128,
                187, 83, 61, 131, 73, 140, 165, 68, 78, 127, 177, 208, 22, 2
            ])
            .unwrap(),
            Fr::from_repr(R2).unwrap(),
        );

        // -1 should work
        assert!(Fr::from_bytes_le(&[
            0, 0, 0, 240, 147, 245, 225, 67, 145, 112, 185, 121, 72, 232, 51, 40, 93, 88, 129, 129,
            182, 69, 80, 184, 41, 160, 49, 225, 114, 78, 100, 48
        ])
        .is_some());

        // modulus is invalid
        assert!(Fr::from_bytes_le(&[
            1, 0, 0, 240, 147, 245, 225, 67, 145, 112, 185, 121, 72, 232, 51, 40, 93, 88, 129, 129,
            182, 69, 80, 184, 41, 160, 49, 225, 114, 78, 100, 48
        ])
        .is_none());

        // Anything larger than the modulus is invalid
        assert!(Fr::from_bytes_le(&[
            2, 0, 0, 240, 147, 245, 225, 67, 145, 112, 185, 121, 72, 232, 51, 40, 93, 88, 129, 129,
            182, 69, 80, 184, 41, 160, 49, 225, 114, 78, 100, 48
        ])
        .is_none());
        assert!(Fr::from_bytes_le(&[
            1, 0, 0, 240, 147, 245, 225, 67, 145, 112, 185, 121, 72, 232, 51, 40, 93, 88, 129, 129,
            182, 69, 80, 184, 41, 160, 49, 225, 114, 78, 100, 49
        ])
        .is_none());
        assert!(Fr::from_bytes_le(&[
            1, 0, 0, 240, 147, 245, 225, 67, 145, 112, 185, 121, 72, 232, 51, 40, 93, 88, 129, 129,
            182, 69, 80, 184, 41, 161, 49, 225, 114, 78, 100, 48
        ])
        .is_none());
    }

    #[test]
    fn test_zero() {
        assert_eq!(Fr::zero(), -&Fr::zero());
        assert_eq!(Fr::zero(), &Fr::zero() + &Fr::zero());
        assert_eq!(Fr::zero(), &Fr::zero() - &Fr::zero());
        assert_eq!(Fr::zero(), &Fr::zero() * &Fr::zero());
    }

    #[test]
    fn test_addition() {
        let mut tmp = LARGEST;
        tmp.add_assign(&LARGEST);

        assert_eq!(
            tmp,
            Fr(mcl_fr {
                d: [
                    0x43e1f593efffffff,
                    0x2833e84879b97091,
                    0xb85045b68181585d,
                    0x30644e72e131a029,
                ]
            })
        );

        let mut tmp = LARGEST;
        tmp.add_assign(&Fr(mcl_fr { d: [1, 0, 0, 0] }));

        assert_eq!(tmp, Fr::zero());
    }

    #[test]
    fn test_negation() {
        let tmp = -&LARGEST;

        assert_eq!(tmp, Fr(mcl_fr { d: [1, 0, 0, 0] }));

        let tmp = -&Fr::zero();
        assert_eq!(tmp, Fr::zero());
        let tmp = -&Fr(mcl_fr { d: [1, 0, 0, 0] });
        assert_eq!(tmp, LARGEST);

        {
            let mut a = Fr::zero();
            a = -a;

            assert!(a.is_zero());
        }

        let mut rng = rand::thread_rng();

        for _ in 0..1000000 {
            // Ensure (a - (-a)) = 0.
            let mut a = Fr::rand(&mut rng);
            let mut b = a;
            b = -b;
            a.add_assign(&b);

            assert!(a.is_zero());
        }
    }

    #[test]
    fn test_subtraction() {
        let mut tmp = LARGEST;
        tmp = &tmp - &LARGEST;

        assert_eq!(tmp, Fr::zero());

        let mut tmp = Fr::zero();
        tmp = &tmp - &LARGEST;

        let mut tmp2 = Fr(mcl_fr { d: MODULUS.0 });
        tmp2 = &tmp2 - &LARGEST;

        assert_eq!(tmp, tmp2);
    }

    #[test]
    fn test_multiplication() {
        let mut tmp = Fr(mcl_fr {
            d: [
                0x6b7e9b8faeefc81a,
                0xe30a8463f348ba42,
                0xeff3cb67a8279c9c,
                0x30303651bd7c774d,
            ],
        });
        tmp = &tmp
            * &Fr(mcl_fr {
                d: [
                    0x13ae28e3bc35ebeb,
                    0xa10f4488075cae2c,
                    0x8160e95a853c3b5d,
                    0x1ae3f03b561a841d,
                ],
            });
        assert_eq!(
            tmp,
            Fr(mcl_fr {
                d: [
                    0x3070c6119986c002,
                    0x357b4df705fda102,
                    0x456c17d9f59d9c1,
                    0x58728afef6b7c0c,
                ]
            })
        );

        let mut rng = rand::thread_rng();

        for _ in 0..1000 {
            // Ensure that (a * b) * c = a * (b * c)
            let a = Fr::rand(&mut rng);
            let b = Fr::rand(&mut rng);
            let c = Fr::rand(&mut rng);

            let mut tmp1 = a;
            tmp1 = &tmp1 * &b;
            tmp1 = &tmp1 * &c;

            let mut tmp2 = b;
            tmp2 = &tmp2 * &c;
            tmp2 = &tmp2 * &a;

            assert_eq!(tmp1, tmp2);
        }

        for _ in 0..1000000 {
            // Ensure that r * (a + b + c) = r*a + r*b + r*c

            let r = Fr::rand(&mut rng);
            let mut a = Fr::rand(&mut rng);
            let mut b = Fr::rand(&mut rng);
            let mut c = Fr::rand(&mut rng);

            let mut tmp1 = a;
            tmp1 = &tmp1 + &b;
            tmp1 = &tmp1 + &c;
            tmp1 = &tmp1 * &r;

            a = &a * &r;
            b = &b * &r;
            c = &c * &r;

            a = &a + &b;
            a = &a + &c;

            assert_eq!(tmp1, a);
        }
    }

    #[test]
    fn test_inverse_is_pow() {
        let q_minus_2 = [
            0x43e1f593efffffff,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ];

        let mut r1 = Fr::from_repr(R).unwrap();
        let mut r2 = r1;

        for _ in 0..1000000 {
            r1 = r1.inverse().unwrap();
            r2 = r2.pow(&q_minus_2);

            assert_eq!(r1, r2);
            // Add R so we check something different next time around
            r1 = &r1 + &Fr::from_repr(R).unwrap();
            r2 = r1;
        }
    }

    #[test]
    fn test_sqrt() {
        {
            assert_eq!(Fr::zero().sqrt().unwrap(), Fr::zero());
        }

        let mut square = Fr(mcl_fr {
            d: [
                0x46cd85a5f273077e,
                0x1d30c47dd68fc735,
                0x77f656f60beca0eb,
                0x301aa01bdf32468d,
            ],
        });

        let mut none_count = 0;

        for _ in 0..100 {
            let square_root = square.sqrt();
            if square_root.is_none() {
                none_count += 1;
            } else {
                assert!(&square_root.unwrap() * &square_root.unwrap() == square);
            }
            square = &square - &Fr::one();
        }

        assert_eq!(51, none_count);
    }

    #[test]
    fn test_double() {
        let a = Fr::from_repr(FrRepr([
            0x1fff3231233ffffd,
            0x4884b7fa00034802,
            0x998c4fefecbc4ff3,
            0x1824b159acc50562,
        ]))
        .unwrap();

        let mut b = a;
        b.double();
        assert_eq!(b, &a + &a);
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_repr_ordering() {
        fn assert_equality(a: FrRepr, b: FrRepr) {
            assert_eq!(a, b);
            assert!(a.cmp(&b) == core::cmp::Ordering::Equal);
        }

        fn assert_lt(a: FrRepr, b: FrRepr) {
            assert!(a < b);
            assert!(b > a);
        }

        assert_equality(
            FrRepr::new([9999, 9999, 9999, 9999]),
            FrRepr::new([9999, 9999, 9999, 9999]),
        );
        assert_equality(
            FrRepr::new([9999, 9998, 9999, 9999]),
            FrRepr::new([9999, 9998, 9999, 9999]),
        );
        assert_equality(
            FrRepr::new([9999, 9999, 9999, 9997]),
            FrRepr::new([9999, 9999, 9999, 9997]),
        );
        assert_lt(
            FrRepr::new([9999, 9997, 9999, 9998]),
            FrRepr::new([9999, 9997, 9999, 9999]),
        );
        assert_lt(
            FrRepr::new([9999, 9997, 9998, 9999]),
            FrRepr::new([9999, 9997, 9999, 9999]),
        );
        assert_lt(
            FrRepr::new([9, 9999, 9999, 9997]),
            FrRepr::new([9999, 9999, 9999, 9997]),
        );
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_repr_from() {
        assert_eq!(FrRepr::from(100), FrRepr::new([100, 0, 0, 0]));
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_repr_is_odd() {
        assert!(!FrRepr::from(0).is_odd());
        assert!(FrRepr::from(0).is_even());
        assert!(FrRepr::from(1).is_odd());
        assert!(!FrRepr::from(1).is_even());
        assert!(!FrRepr::from(324834872).is_odd());
        assert!(FrRepr::from(324834872).is_even());
        assert!(FrRepr::from(324834873).is_odd());
        assert!(!FrRepr::from(324834873).is_even());
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_repr_is_zero() {
        assert!(FrRepr::from(0).is_zero());
        assert!(!FrRepr::from(1).is_zero());
        assert!(!FrRepr::new([0, 0, 1, 0]).is_zero());
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_repr_div2() {
        let mut a = FrRepr::new([
            0xbd2920b19c972321,
            0x174ed0466a3be37e,
            0xd468d5e3b551f0b5,
            0xcb67c072733beefc,
        ]);
        a.div2();
        assert_eq!(
            a,
            FrRepr::new([
                0x5e949058ce4b9190,
                0x8ba76823351df1bf,
                0x6a346af1daa8f85a,
                0x65b3e039399df77e
            ])
        );
        for _ in 0..10 {
            a.div2();
        }
        assert_eq!(
            a,
            FrRepr::new([
                0x6fd7a524163392e4,
                0x16a2e9da08cd477c,
                0xdf9a8d1abc76aa3e,
                0x196cf80e4e677d
            ])
        );
        for _ in 0..200 {
            a.div2();
        }
        assert_eq!(a, FrRepr::new([0x196cf80e4e67, 0x0, 0x0, 0x0]));
        for _ in 0..40 {
            a.div2();
        }
        assert_eq!(a, FrRepr::new([0x19, 0x0, 0x0, 0x0]));
        for _ in 0..4 {
            a.div2();
        }
        assert_eq!(a, FrRepr::new([0x1, 0x0, 0x0, 0x0]));
        a.div2();
        assert!(a.is_zero());
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_repr_shr() {
        let mut a = FrRepr::new([
            0xb33fbaec482a283f,
            0x997de0d3a88cb3df,
            0x9af62d2a9a0e5525,
            0x16003ab08de70da1,
        ]);
        a.shr(0);
        assert_eq!(
            a,
            FrRepr::new([
                0xb33fbaec482a283f,
                0x997de0d3a88cb3df,
                0x9af62d2a9a0e5525,
                0x16003ab08de70da1
            ])
        );
        a.shr(1);
        assert_eq!(
            a,
            FrRepr::new([
                0xd99fdd762415141f,
                0xccbef069d44659ef,
                0xcd7b16954d072a92,
                0xb001d5846f386d0,
            ])
        );
        a.shr(50);
        assert_eq!(
            a,
            FrRepr::new([
                0xbc1a7511967bf667,
                0xc5a55341caa4b32f,
                0x75611bce1b4335e,
                0x2c0
            ])
        );
        a.shr(130);
        assert_eq!(a, FrRepr::new([0x1d5846f386d0cd7, 0xb0, 0x0, 0x0]));
        a.shr(64);
        assert_eq!(a, FrRepr::new([0xb0, 0x0, 0x0, 0x0]));
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_repr_mul2() {
        let mut a = FrRepr::from(23712937547);
        a.mul2();
        assert_eq!(a, FrRepr::new([0xb0acd6c96, 0x0, 0x0, 0x0]));
        for _ in 0..60 {
            a.mul2();
        }
        assert_eq!(a, FrRepr::new([0x6000000000000000, 0xb0acd6c9, 0x0, 0x0]));
        for _ in 0..128 {
            a.mul2();
        }
        assert_eq!(a, FrRepr::new([0x0, 0x0, 0x6000000000000000, 0xb0acd6c9]));
        for _ in 0..60 {
            a.mul2();
        }
        assert_eq!(a, FrRepr::new([0x0, 0x0, 0x0, 0x9600000000000000]));
        for _ in 0..7 {
            a.mul2();
        }
        assert!(a.is_zero());
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_repr_num_bits() {
        let mut a = FrRepr::from(0);
        assert_eq!(0, a.num_bits());
        a = FrRepr::from(1);
        for i in 1..257 {
            assert_eq!(i, a.num_bits());
            a.mul2();
        }
        assert_eq!(0, a.num_bits());
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_repr_sub_noborrow() {
        let mut rng = rand::thread_rng();

        let mut t = FrRepr::new([
            0x8e62a7e85264e2c3,
            0xb23d34c1941d3ca,
            0x5976930b7502dd15,
            0x300f3fb517bf5495,
        ]);
        t.sub_noborrow(&FrRepr::new([
            0xd64f669809cbc6a4,
            0xfa76cb9d90cf7637,
            0xfefb0df9038d43b3,
            0x298a30c744b31acf,
        ]));
        assert_eq!(
            t,
            FrRepr::new([
                0xb813415048991c1f,
                0x10ad07ae88725d92,
                0x5a7b851271759961,
                0x6850eedd30c39c5,
            ])
        );

        for _ in 0..1000000 {
            let mut a = Fr::rand(&mut rng).into_repr();
            a.0[3] >>= 30;
            let mut b = a;
            for _ in 0..10 {
                b.mul2();
            }
            let mut c = b;
            for _ in 0..10 {
                c.mul2();
            }

            assert!(a < b);
            assert!(b < c);

            let mut csub_ba = c;
            csub_ba.sub_noborrow(&b);
            csub_ba.sub_noborrow(&a);

            let mut csub_ab = c;
            csub_ab.sub_noborrow(&a);
            csub_ab.sub_noborrow(&b);

            assert_eq!(csub_ab, csub_ba);
        }

        // Subtracting r+1 from r should produce -1 (mod 2**256)
        let mut r = FrRepr::new([
            0x43e1f593f0000001,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ]);
        r.sub_noborrow(&FrRepr::new([
            0x43e1f593f0000002,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ]));
        assert_eq!(
            r,
            FrRepr::new([
                0xffffffffffffffff,
                0xffffffffffffffff,
                0xffffffffffffffff,
                0xffffffffffffffff,
            ])
        );
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_legendre() {
        use ff::LegendreSymbol::*;
        use ff::SqrtField;

        assert_eq!(QuadraticResidue, Fr::one().legendre());
        assert_eq!(Zero, Fr::zero().legendre());

        let e = FrRepr::new([
            0xfb328134bbf70ea4,
            0xaf808771640890b2,
            0xc9bcf51e89f37aa6,
            0x2b3437ed8887f0a4,
        ]);
        assert_eq!(QuadraticResidue, Fr::from_repr(e).unwrap().legendre());
        let e = FrRepr::new([
            0x96341aefd047c045,
            0x9b5f4254500a4d65,
            0x1ee08223b68ac240,
            0x3019cd545c0ec7c6,
        ]);
        assert_eq!(QuadraticNonResidue, Fr::from_repr(e).unwrap().legendre());
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_repr_add_nocarry() {
        let mut rng = rand::thread_rng();

        let mut t = FrRepr::new([
            0xd64f669809cbc6a4,
            0xfa76cb9d90cf7637,
            0xfefb0df9038d43b3,
            0x298a30c744b31acf,
        ]);
        t.add_nocarry(&FrRepr::new([
            0x8e62a7e85264e2c3,
            0xb23d34c1941d3ca,
            0x5976930b7502dd15,
            0x300f3fb517bf5495,
        ]));
        assert_eq!(
            t,
            FrRepr::new([
                0x64b20e805c30a967,
                0x59a9ee9aa114a02,
                0x5871a104789020c9,
                0x5999707c5c726f65,
            ])
        );

        // Test for the associativity of addition.
        for _ in 0..1000 {
            let mut a = Fr::rand(&mut rng).into_repr();
            let mut b = Fr::rand(&mut rng).into_repr();
            let mut c = Fr::rand(&mut rng).into_repr();

            // Unset the first few bits, so that overflow won't occur.
            a.0[3] >>= 4;
            b.0[3] >>= 4;
            c.0[3] >>= 4;

            let mut abc = a;
            abc.add_nocarry(&b);
            abc.add_nocarry(&c);

            let mut acb = a;
            acb.add_nocarry(&c);
            acb.add_nocarry(&b);

            let mut bac = b;
            bac.add_nocarry(&a);
            bac.add_nocarry(&c);

            let mut bca = b;
            bca.add_nocarry(&c);
            bca.add_nocarry(&a);

            let mut cab = c;
            cab.add_nocarry(&a);
            cab.add_nocarry(&b);

            let mut cba = c;
            cba.add_nocarry(&b);
            cba.add_nocarry(&a);

            assert_eq!(abc, acb);
            assert_eq!(abc, bac);
            assert_eq!(abc, bca);
            assert_eq!(abc, cab);
            assert_eq!(abc, cba);
        }

        // Adding 1 to (2^256 - 1) should produce zero
        let mut x = FrRepr::new([
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
            0xffffffffffffffff,
        ]);
        x.add_nocarry(&FrRepr::from(1));
        assert!(x.is_zero());
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_add_assign() {
        {
            // Random number
            let mut tmp = Fr(mcl_fr {
                d: [
                    0x437ce7616d580765,
                    0xd42d1ccb29d1235b,
                    0xed8f753821bd1423,
                    0x2eede1c9c89528ca,
                ],
            });
            assert!(tmp.is_valid());
            // Test that adding zero has no effect.
            tmp.add_assign(&Fr(mcl_fr { d: [0, 0, 0, 0] }));
            assert_eq!(
                tmp,
                Fr(mcl_fr {
                    d: [
                        0x437ce7616d580765,
                        0xd42d1ccb29d1235b,
                        0xed8f753821bd1423,
                        0x2eede1c9c89528ca
                    ]
                })
            );
            // Add one and test for the result.
            tmp.add_assign(&Fr(mcl_fr { d: [1, 0, 0, 0] }));
            assert_eq!(
                tmp,
                Fr(mcl_fr {
                    d: [
                        0x437ce7616d580766,
                        0xd42d1ccb29d1235b,
                        0xed8f753821bd1423,
                        0x2eede1c9c89528ca
                    ]
                })
            );
            // Add another random number that exercises the reduction.
            tmp.add_assign(&Fr(mcl_fr {
                d: [
                    0x946f435944f7dc79,
                    0xb55e7ee6533a9b9b,
                    0x1e43b84c2f6194ca,
                    0x28717ab525463496,
                ],
            }));
            assert_eq!(
                tmp,
                Fr(mcl_fr {
                    d: [
                        0x940a3526c24fe3de,
                        0x6157b36903524e65,
                        0x5382e7cdcf9d5091,
                        0x26fb0e0c0ca9bd37,
                    ]
                })
            );
            // Add one to (r - 1) and test for the result.
            tmp = Fr(mcl_fr {
                d: [
                    0x43e1f593f0000000,
                    0x2833e84879b97091,
                    0xb85045b68181585d,
                    0x30644e72e131a029,
                ],
            });
            tmp.add_assign(&Fr(mcl_fr { d: [1, 0, 0, 0] }));
            assert!(tmp.into_repr().is_zero());
            // Add a random number to another one such that the result is r - 1
            tmp = Fr(mcl_fr {
                d: [
                    0xf1c7a341cccb6190,
                    0x7e983254a196515f,
                    0xaa67621ec2c310de,
                    0x1593c0229f59dd08,
                ],
            });
            tmp.add_assign(&Fr(mcl_fr {
                d: [
                    0x521a525223349e70,
                    0xa99bb5f3d8231f31,
                    0xde8e397bebe477e,
                    0x1ad08e5041d7c321,
                ],
            }));
            assert_eq!(
                tmp,
                Fr(mcl_fr {
                    d: [
                        0x43e1f593f0000000,
                        0x2833e84879b97091,
                        0xb85045b68181585d,
                        0x30644e72e131a029,
                    ]
                })
            );
            // Add one to the result and test for it.
            tmp.add_assign(&Fr(mcl_fr { d: [1, 0, 0, 0] }));
            assert!(tmp.into_repr().is_zero());
        }

        // Test associativity

        let mut rng = rand::thread_rng();

        for i in 0..1000000 {
            // Generate a, b, c and ensure (a + b) + c == a + (b + c).
            let a = Fr::rand(&mut rng);
            let b = Fr::rand(&mut rng);
            let c = Fr::rand(&mut rng);

            let mut tmp1 = a;
            tmp1.add_assign(&b);
            tmp1.add_assign(&c);

            let mut tmp2 = b;
            tmp2.add_assign(&c);
            tmp2.add_assign(&a);

            assert!(tmp1.is_valid());
            assert!(tmp2.is_valid());
            assert_eq!(tmp1, tmp2, "round {}", i);
        }
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_sub_assign() {
        {
            // Test arbitrary subtraction that tests reduction.
            let mut tmp = Fr(mcl_fr {
                d: [
                    0x6a68c64b6f735a2b,
                    0xd5f4d143fe0a1972,
                    0x37c17f3829267c62,
                    0x29f37391f30915c,
                ],
            });
            tmp.sub_assign(&Fr(mcl_fr {
                d: [
                    0xade5adacdccb6190,
                    0xaa21ee0f27db3ccd,
                    0x2550f4704ae39086,
                    0x301d1902e7c5ba27,
                ],
            }));
            assert_eq!(
                tmp,
                Fr(mcl_fr {
                    d: [
                        0x650e3282a7f89c,
                        0x5406cb7d4fe84d36,
                        0xcac0d07e5fc44439,
                        0x2e66ca9189c775e,
                    ]
                })
            );

            // Test the opposite subtraction which doesn't test reduction.
            tmp = Fr(mcl_fr {
                d: [
                    0xade5adacdccb6190,
                    0xaa21ee0f27db3ccd,
                    0x2550f4704ae39086,
                    0x301d1902e7c5ba27,
                ],
            });
            tmp.sub_assign(&Fr(mcl_fr {
                d: [
                    0x6a68c64b6f735a2b,
                    0xd5f4d143fe0a1972,
                    0x37c17f3829267c62,
                    0x29f37391f30915c,
                ],
            }));
            assert_eq!(
                tmp,
                Fr(mcl_fr {
                    d: [
                        0x437ce7616d580765,
                        0xd42d1ccb29d1235b,
                        0xed8f753821bd1423,
                        0x2d7de1c9c89528ca,
                    ]
                })
            );

            // Test for sensible results with zero
            tmp = Fr(mcl_fr { d: [0, 0, 0, 0] });
            tmp.sub_assign(&Fr(mcl_fr { d: [0, 0, 0, 0] }));
            assert!(tmp.is_zero());

            tmp = Fr(mcl_fr {
                d: [
                    0x437ce7616d580765,
                    0xd42d1ccb29d1235b,
                    0xed8f753821bd1423,
                    0x301de1c9c89528ca,
                ],
            });
            tmp.sub_assign(&Fr(mcl_fr { d: [0, 0, 0, 0] }));
            assert_eq!(
                tmp,
                Fr(mcl_fr {
                    d: [
                        0x437ce7616d580765,
                        0xd42d1ccb29d1235b,
                        0xed8f753821bd1423,
                        0x301de1c9c89528ca,
                    ]
                })
            );
        }

        let mut rng = rand::thread_rng();

        for _ in 0..1000000 {
            // Ensure that (a - b) + (b - a) = 0.
            let a = Fr::rand(&mut rng);
            let b = Fr::rand(&mut rng);

            let mut tmp1 = a;
            tmp1.sub_assign(&b);

            let mut tmp2 = b;
            tmp2.sub_assign(&a);

            tmp1.add_assign(&tmp2);
            assert!(tmp1.is_zero());
        }
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_mul_assign() {
        let mut tmp = Fr(mcl_fr {
            d: [
                0x6b7e9b8faeefc81a,
                0xe30a8463f348ba42,
                0xeff3cb67a8279c9c,
                0x30303651bd7c774d,
            ],
        });
        tmp.mul_assign(&Fr(mcl_fr {
            d: [
                0x13ae28e3bc35ebeb,
                0xa10f4488075cae2c,
                0x8160e95a853c3b5d,
                0x1fe3f03b561a841d,
            ],
        }));
        assert_eq!(
            tmp,
            Fr(mcl_fr {
                d: [
                    0xfbf375fa38116eeb,
                    0x1fb40ee0a5a7520c,
                    0x12be06c67960494e,
                    0x1e49785c12f55735,
                ]
            })
        );

        let mut rng = rand::thread_rng();

        for _ in 0..1000000 {
            // Ensure that (a * b) * c = a * (b * c)
            let a = Fr::rand(&mut rng);
            let b = Fr::rand(&mut rng);
            let c = Fr::rand(&mut rng);

            let mut tmp1 = a;
            tmp1.mul_assign(&b);
            tmp1.mul_assign(&c);

            let mut tmp2 = b;
            tmp2.mul_assign(&c);
            tmp2.mul_assign(&a);

            assert_eq!(tmp1, tmp2);
        }

        for _ in 0..1000000 {
            // Ensure that r * (a + b + c) = r*a + r*b + r*c

            let r = Fr::rand(&mut rng);
            let mut a = Fr::rand(&mut rng);
            let mut b = Fr::rand(&mut rng);
            let mut c = Fr::rand(&mut rng);

            let mut tmp1 = a;
            tmp1.add_assign(&b);
            tmp1.add_assign(&c);
            tmp1.mul_assign(&r);

            a.mul_assign(&r);
            b.mul_assign(&r);
            c.mul_assign(&r);

            a.add_assign(&b);
            a.add_assign(&c);

            assert_eq!(tmp1, a);
        }
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_squaring() {
        let mut a = Fr(mcl_fr {
            d: [
                0xffffffffffffffff,
                0xffffffffffffffff,
                0xffffffffffffffff,
                0x30644e72e131a028,
            ],
        });
        assert!(a.is_valid());
        a.square();
        assert_eq!(
            a,
            Fr::from_repr(FrRepr::new([
                0x3840a680c128acd0,
                0x9818fcf18b4fedf7,
                0x47478f26eb7c5d3c,
                0x2ec0386019410dc9
            ]))
            .unwrap()
        );

        let mut rng = rand::thread_rng();

        for _ in 0..1000000 {
            // Ensure that (a * a) = a^2
            let a = Fr::rand(&mut rng);

            let mut tmp = a;
            tmp.square();

            let mut tmp2 = a;
            tmp2.mul_assign(&a);

            assert_eq!(tmp, tmp2);
        }
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_inverse() {
        assert!(Fr::zero().inverse().is_none());

        let mut rng = rand::thread_rng();

        let one = Fr::one();

        for i in 0..1000 {
            // Ensure that a * a^-1 = 1
            let mut a = Fr::rand(&mut rng);
            let ainv = a.inverse().unwrap();
            a.mul_assign(&ainv);
            assert_eq!(a, one, "round {}", i);
        }
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_double() {
        let mut rng = rand::thread_rng();

        for _ in 0..1000 {
            // Ensure doubling a is equivalent to adding a to itself.
            let mut a = Fr::rand(&mut rng);
            let mut b = a;
            b.add_assign(&a);
            a.double();
            assert_eq!(a, b);
        }
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_negate() {
        {
            let mut a = Fr::zero();
            a.negate();

            assert!(a.is_zero());
        }

        let mut rng = rand::thread_rng();

        for _ in 0..1000 {
            // Ensure (a - (-a)) = 0.
            let mut a = Fr::rand(&mut rng);
            let mut b = a;
            b.negate();
            a.add_assign(&b);

            assert!(a.is_zero());
        }
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_pow() {
        let mut rng = rand::thread_rng();

        for i in 0..1000 {
            // Exponentiate by various small numbers and ensure it consists with repeated
            // multiplication.
            let a = Fr::rand(&mut rng);
            let target = a.pow(&[i]);
            let mut c = Fr::one();
            for _ in 0..i {
                c.mul_assign(&a);
            }
            assert_eq!(c, target);
        }

        for _ in 0..1000 {
            // Exponentiating by the modulus should have no effect in a prime field.
            let a = Fr::rand(&mut rng);

            assert_eq!(a, a.pow(Fr::char()));
        }
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_sqrt() {
        use ff::SqrtField;

        let mut rng = rand::thread_rng();

        assert_eq!(Fr::zero().sqrt().unwrap(), Fr::zero());

        for _ in 0..1000 {
            // Ensure sqrt(a^2) = a or -a
            let a = Fr::rand(&mut rng);
            let mut nega = a;
            nega.negate();
            let mut b = a;
            b.square();

            let b = b.sqrt().unwrap();

            assert!(a == b || nega == b);
        }

        for _ in 0..1000 {
            // Ensure sqrt(a)^2 = a for random a
            let a = Fr::rand(&mut rng);

            if let Some(mut tmp) = a.sqrt() {
                tmp.square();

                assert_eq!(a, tmp);
            }
        }
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_from_into_repr() {
        // r + 1 should not be in the field
        assert!(Fr::from_repr(FrRepr::new([
            0x43e1f593f0000002,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ]))
        .is_err());

        // r should not be in the field
        assert!(Fr::from_repr(Fr::char()).is_err());

        // Multiply some arbitrary representations to see if the result is as expected.
        let a = FrRepr::new([
            0x25ebe3a3ad3c0c6a,
            0x6990e39d092e817c,
            0x941f900d42f5658e,
            0x29f8a103b38a71e0,
        ]);
        let mut a_fr = Fr::from_repr(a).unwrap();
        let b = FrRepr::new([
            0x264e9454885e2475,
            0x46f7746bb0308370,
            0x4683ef5347411f9,
            0x29838d7f208d4492,
        ]);
        let b_fr = Fr::from_repr(b).unwrap();
        let c = FrRepr::new([
            0x67586d63d7afcabf,
            0x845f611e21bbf755,
            0xda73cb797ec22b36,
            0x2678c380607b7a34,
        ]);
        a_fr.mul_assign(&b_fr);
        assert_eq!(a_fr.into_repr(), c);

        // Zero should be in the field.
        assert!(Fr::from_repr(FrRepr::from(0)).unwrap().is_zero());

        let mut rng = rand::thread_rng();

        for i in 0..1000 {
            // Try to turn Fr elements into representations and back again, and compare.
            let a = Fr::rand(&mut rng);
            let a_repr = a.into_repr();
            let b_repr = FrRepr::from(a);
            assert_eq!(a_repr, b_repr);
            let a_again = Fr::from_repr(a_repr).unwrap();

            assert_eq!(a, a_again, "{}", i);
        }
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_repr_display() {
        assert_eq!(
            format!(
                "{}",
                FrRepr::new([
                    0x2829c242fa826143,
                    0x1f32cf4dd4330917,
                    0x932e4e479d168cd9,
                    0x513c77587f563f64
                ])
            ),
            "0x513c77587f563f64932e4e479d168cd91f32cf4dd43309172829c242fa826143".to_string()
        );
        assert_eq!(
            format!(
                "{}",
                FrRepr::new([
                    0x25ebe3a3ad3c0c6a,
                    0x6990e39d092e817c,
                    0x941f900d42f5658e,
                    0x44f8a103b38a71e0
                ])
            ),
            "0x44f8a103b38a71e0941f900d42f5658e6990e39d092e817c25ebe3a3ad3c0c6a".to_string()
        );
        assert_eq!(
            format!(
                "{}",
                FrRepr::new([
                    0xffffffffffffffff,
                    0xffffffffffffffff,
                    0xffffffffffffffff,
                    0xffffffffffffffff
                ])
            ),
            "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff".to_string()
        );
        assert_eq!(
            format!("{}", FrRepr::new([0, 0, 0, 0])),
            "0x0000000000000000000000000000000000000000000000000000000000000000".to_string()
        );
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_display() {
        assert_eq!(
            format!(
                "{}",
                Fr::from_repr(FrRepr::new([
                    0xc3cae746a3b5ecc7,
                    0x185ec8eb3f5b5aee,
                    0x684499ffe4b9dd99,
                    0x7c9bba7afb68faa
                ]))
                .unwrap()
            ),
            "Fr(0x07c9bba7afb68faa684499ffe4b9dd99185ec8eb3f5b5aeec3cae746a3b5ecc7)".to_string()
        );
        assert_eq!(
            format!(
                "{}",
                Fr::from_repr(FrRepr::new([
                    0x44c71298ff198106,
                    0xb0ad10817df79b6a,
                    0xd034a80a2b74132b,
                    0x305f9a1336f50719
                ]))
                .unwrap()
            ),
            "Fr(0x305f9a1336f50719d034a80a2b74132bb0ad10817df79b6a44c71298ff198106)".to_string()
        );
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_num_bits() {
        assert_eq!(Fr::NUM_BITS, 254);
        assert_eq!(Fr::CAPACITY, 253);
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_root_of_unity() {
        use ff::SqrtField;

        assert_eq!(Fr::S, 28);
        assert_eq!(
            Fr::multiplicative_generator(),
            Fr::from_repr(FrRepr::from(7)).unwrap()
        );
        assert_eq!(
            Fr::multiplicative_generator().pow([
                0x9b9709143e1f593f,
                0x181585d2833e8487,
                0x131a029b85045b68,
                0x30644e72e
            ]),
            Fr::root_of_unity()
        );
        assert_eq!(Fr::root_of_unity().pow([1 << Fr::S]), Fr::one());
        assert!(Fr::multiplicative_generator().sqrt().is_none());
    }

    #[test]
    #[allow(non_snake_case)]
    fn Fr_field_tests() {
        crate::tests::field::random_field_tests::<Fr>();
        crate::tests::field::random_sqrt_tests::<Fr>();
        crate::tests::field::random_frobenius_tests::<Fr, _>(Fr::char(), 13);
        crate::tests::field::from_str_tests::<Fr>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn Fr_repr_tests() {
        crate::tests::repr::random_repr_tests::<FrRepr>();
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_modulus() {
        assert_eq!(
            format!("{:?}", Fr::char()),
            "0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001"
        );
    }

    #[test]
    #[allow(non_snake_case)]
    fn test_Fr_repr_conversion() {
        let a = FrRepr::from(1);
        let b = FrRepr([1, 0, 0, 0]);
        assert_eq!(a, b);

        let a = Fr::from(1);
        let b = Fr::from_repr(FrRepr::from(1)).unwrap();
        assert_eq!(a, b);
        assert_eq!(Fr::from(1).into_repr(), FrRepr::from(1));

        let a = Fr::from(12);
        assert_eq!(a, Fr::from_repr(a.into_repr()).unwrap());

        let a = FrRepr::from(12);
        assert_eq!(Fr::from_repr(a).unwrap().into_repr(), a);
    }
}
