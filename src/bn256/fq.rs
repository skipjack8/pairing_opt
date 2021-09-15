use super::fq2::Fq2;
use crate::bn256::check_curve_init;
use crate::mcl::Fp as MclFq;
use crate::mcl::*;
use core::{
    cmp, fmt, mem,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use ff::{Field, PrimeField, PrimeFieldDecodingError, PrimeFieldRepr};
use std::hash::{Hash, Hasher};

/// `q = 21888242871839275222246405745257275088696311157297823662689037894645226208583`
/// `generator = 2`
/// `Fq` values are always in
/// Montgomery form; i.e., Fq(a) = aR mod q, with R = 2^256.
#[derive(Copy, Clone)]
pub struct Fq(pub(crate) MclFq);

/// Representation of a `Fq`, in regular coordinates.
#[derive(Default, Clone, Copy)]
pub struct FqRepr(pub [u64; 4]);

// B coefficient of BN256 curve, B = 3
pub const B_COEFF: Fq = Fq(MclFq {
    d: [
        0x7a17caa950ad28d7,
        0x1f6ac17ae15521b9,
        0x334bea4e696bd284,
        0x2a1f6744ce179d8e,
    ],
});

pub const B_COEFF_FQ2: Fq2 = Fq2 {
    c0: Fq(MclFq {
        d: [
            0x3bf938e377b802a8,
            0x020b1b273633535d,
            0x26b7edf049755260,
            0x2514c6324384a86d,
        ],
    }),
    c1: Fq(MclFq {
        d: [
            0x38e7ecccd1dcff67,
            0x65f0b37d93ce0d3e,
            0xd749d0dd22ac00aa,
            0x0141b9ce4a688d4d,
        ],
    }),
};

// The generators of G1/G2

// Generator of G1
// x = 1
// y = 2
pub const G1_GENERATOR_X: Fq = Fq(MclFq {
    d: [
        0xd35d438dc58f0d9d,
        0x0a78eb28f5c70b3d,
        0x666ea36f7879462c,
        0x0e0a77c19a07df2f,
    ],
});
pub const G1_GENERATOR_Y: Fq = Fq(MclFq {
    d: [
        0xa6ba871b8b1e1b3a,
        0x14f1d651eb8e167b,
        0xccdd46def0f28c58,
        0x1c14ef83340fbe5e,
    ],
});

// Generator of G2
//
// x = 11559732032986387107991004021392285783925812861821192530917403151452391805634*u
//     + 10857046999023057135944570762232829481370756359578518086990519993285655852781
//
// y = 4082367875863433681332203403145435568316851327593401208105741076214120093531*u
//     + 8495653923123431417604973247489272438418190587263600148770280649306958101930

pub const G2_GENERATOR_X_C0: Fq = Fq(MclFq {
    d: [
        0x8e83b5d102bc2026,
        0xdceb1935497b0172,
        0xfbb8264797811adf,
        0x19573841af96503b,
    ],
});
pub const G2_GENERATOR_X_C1: Fq = Fq(MclFq {
    d: [
        0xafb4737da84c6140,
        0x6043dd5a5802d8c4,
        0x09e950fc52a02f86,
        0x14fef0833aea7b6b,
    ],
});
pub const G2_GENERATOR_Y_C0: Fq = Fq(MclFq {
    d: [
        0x619dfa9d886be9f6,
        0xfe7fd297f59e9b78,
        0xff9e1a62231b7dfe,
        0x28fd7eebae9e4206,
    ],
});
pub const G2_GENERATOR_Y_C1: Fq = Fq(MclFq {
    d: [
        0x64095b56c71856ee,
        0xdc57f922327d3cbb,
        0x55f935be33351076,
        0x0da4a0e693fd6482,
    ],
});

// Coefficients for the Frobenius automorphism.
pub const FROBENIUS_COEFF_FQ2_C1: [Fq; 2] = [
    // Fq(-1)**(((q^0) - 1) / 2)
    // it's 1 in Montgommery form
    Fq(MclFq {
        d: [
            0xd35d438dc58f0d9d,
            0x0a78eb28f5c70b3d,
            0x666ea36f7879462c,
            0x0e0a77c19a07df2f,
        ],
    }),
    // Fq(-1)**(((q^1) - 1) / 2)
    Fq(MclFq {
        d: [
            0x68c3488912edefaa,
            0x8d087f6872aabf4f,
            0x51e1a24709081231,
            0x2259d6b14729c0fa,
        ],
    }),
];

// Fq2(u + 9)**(((q^1) - 1) / 2)
pub const XI_TO_Q_MINUS_1_OVER_2: Fq2 = Fq2 {
    c0: Fq(MclFq {
        d: [
            0xe4bbdd0c2936b629,
            0xbb30f162e133bacb,
            0x31a9d1b6f9645366,
            0x253570bea500f8dd,
        ],
    }),
    c1: Fq(MclFq {
        d: [
            0xa1d77ce45ffe77c7,
            0x07affd117826d1db,
            0x6d16bd27bb7edc6b,
            0x2c87200285defecc,
        ],
    }),
};

pub const FROBENIUS_COEFF_FQ6_C1: [Fq2; 6] = [
    // Fq2(u + 9)**(((q^0) - 1) / 3)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0xd35d438dc58f0d9d,
                0x0a78eb28f5c70b3d,
                0x666ea36f7879462c,
                0x0e0a77c19a07df2f,
            ],
        }),
        c1: Fq(MclFq {
            d: [0x0, 0x0, 0x0, 0x0],
        }),
    },
    // Fq2(u + 9)**(((q^1) - 1) / 3)
    // taken from go-ethereum and also re-calculated manually
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0xb5773b104563ab30,
                0x347f91c8a9aa6454,
                0x7a007127242e0991,
                0x1956bcd8118214ec,
            ],
        }),
        c1: Fq(MclFq {
            d: [
                0x6e849f1ea0aa4757,
                0xaa1c7b6d89f89141,
                0xb6e713cdfae0ca3a,
                0x26694fbb4e82ebc3,
            ],
        }),
    },
    // Fq2(u + 9)**(((q^2) - 1) / 3)
    // this one and other below are recalculated manually
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x3350c88e13e80b9c,
                0x7dce557cdb5e56b9,
                0x6001b4b8b615564a,
                0x2682e617020217e0,
            ],
        }),
        c1: Fq(MclFq {
            d: [0x0, 0x0, 0x0, 0x0],
        }),
    },
    // Fq2(u + 9)**(((q^3) - 1) / 3)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0xc9af22f716ad6bad,
                0xb311782a4aa662b2,
                0x19eeaf64e248c7f4,
                0x20273e77e3439f82,
            ],
        }),
        c1: Fq(MclFq {
            d: [
                0xacc02860f7ce93ac,
                0x3933d5817ba76b4c,
                0x69e6188b446c8467,
                0x0a46036d4417cc55,
            ],
        }),
    },
    // Fq2(u + 9)**(((q^4) - 1) / 3)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x71930c11d782e155,
                0xa6bb947cffbe3323,
                0xaa303344d4741444,
                0x2c3b3f0d26594943,
            ],
        }),
        c1: Fq(MclFq {
            d: [0x0, 0x0, 0x0, 0x0],
        }),
    },
    // Fq2(u + 9)**(((q^5) - 1) / 3)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0xf91aba2654e8e3b1,
                0x4771cb2fdc92ce12,
                0xdcb16ae0fc8bdf35,
                0x274aa195cd9d8be4,
            ],
        }),
        c1: Fq(MclFq {
            d: [
                0x5cfc50ae18811f8b,
                0x4bb28433cb43988c,
                0x4fd35f13c3b56219,
                0x301949bd2fc8883a,
            ],
        }),
    },
];

pub const FROBENIUS_COEFF_FQ6_C2: [Fq2; 6] = [
    // Fq2(u + 1)**(((2q^0) - 2) / 3)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0xd35d438dc58f0d9d,
                0x0a78eb28f5c70b3d,
                0x666ea36f7879462c,
                0x0e0a77c19a07df2f,
            ],
        }),
        c1: Fq(MclFq {
            d: [0x0, 0x0, 0x0, 0x0],
        }),
    },
    // Fq2(u + 1)**(((2q^1) - 2) / 3)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x7361d77f843abe92,
                0xa5bb2bd3273411fb,
                0x9c941f314b3e2399,
                0x15df9cddbb9fd3ec,
            ],
        }),
        c1: Fq(MclFq {
            d: [
                0x5dddfd154bd8c949,
                0x62cb29a5a4445b60,
                0x37bc870a0c7dd2b9,
                0x24830a9d3171f0fd,
            ],
        }),
    },
    // Fq2(u + 1)**(((2q^2) - 2) / 3)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x71930c11d782e155,
                0xa6bb947cffbe3323,
                0xaa303344d4741444,
                0x2c3b3f0d26594943,
            ],
        }),
        c1: Fq(MclFq {
            d: [0x0, 0x0, 0x0, 0x0],
        }),
    },
    // Fq2(u + 1)**(((2q^3) - 2) / 3)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x448a93a57b6762df,
                0xbfd62df528fdeadf,
                0xd858f5d00e9bd47a,
                0x06b03d4d3476ec58,
            ],
        }),
        c1: Fq(MclFq {
            d: [
                0x2b19daf4bcc936d1,
                0xa1a54e7a56f4299f,
                0xb533eee05adeaef1,
                0x170c812b84dda0b2,
            ],
        }),
    },
    // Fq2(u + 1)**(((2q^4) - 2) / 3)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x3350c88e13e80b9c,
                0x7dce557cdb5e56b9,
                0x6001b4b8b615564a,
                0x2682e617020217e0,
            ],
        }),
        c1: Fq(MclFq {
            d: [0x0, 0x0, 0x0, 0x0],
        }),
    },
    // Fq2(u + 1)**(((2q^5) - 2) / 3)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x843420f1d8dadbd6,
                0x31f010c9183fcdb2,
                0x436330b527a76049,
                0x13d47447f11adfe4,
            ],
        }),
        c1: Fq(MclFq {
            d: [
                0xef494023a857fa74,
                0x2a925d02d5ab101a,
                0x83b015829ba62f10,
                0x2539111d0c13aea3,
            ],
        }),
    },
];

// non_residue^((modulus^i-1)/6) for i=0,...,11
pub const FROBENIUS_COEFF_FQ12_C1: [Fq2; 12] = [
    // Fq2(u + 1)**(((q^0) - 1) / 6)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0xd35d438dc58f0d9d,
                0x0a78eb28f5c70b3d,
                0x666ea36f7879462c,
                0x0e0a77c19a07df2f,
            ],
        }),
        c1: Fq(MclFq {
            d: [0x0, 0x0, 0x0, 0x0],
        }),
    },
    // Fq2(u + 1)**(((q^1) - 1) / 6)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0xaf9ba69633144907,
                0xca6b1d7387afb78a,
                0x11bded5ef08a2087,
                0x02f34d751a1f3a7c,
            ],
        }),
        c1: Fq(MclFq {
            d: [
                0xa222ae234c492d72,
                0xd00f02a4565de15b,
                0xdc2ff3a253dfc926,
                0x10a75716b3899551,
            ],
        }),
    },
    // Fq2(u + 1)**(((q^2) - 1) / 6)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0xca8d800500fa1bf2,
                0xf0c5d61468b39769,
                0x0e201271ad0d4418,
                0x04290f65bad856e6,
            ],
        }),
        c1: Fq(MclFq {
            d: [0x0, 0x0, 0x0, 0x0],
        }),
    },
    // Fq2(u + 1)**(((q^3) - 1) / 6)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x365316184e46d97d,
                0x0af7129ed4c96d9f,
                0x659da72fca1009b5,
                0x08116d8983a20d23,
            ],
        }),
        c1: Fq(MclFq {
            d: [
                0xb1df4af7c39c1939,
                0x3d9f02878a73bf7f,
                0x9b2220928caf0ae0,
                0x26684515eff054a6,
            ],
        }),
    },
    // Fq2(u + 1)**(((q^4) - 1) / 6)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x3350c88e13e80b9c,
                0x7dce557cdb5e56b9,
                0x6001b4b8b615564a,
                0x2682e617020217e0,
            ],
        }),
        c1: Fq(MclFq {
            d: [0x0, 0x0, 0x0, 0x0],
        }),
    },
    // Fq2(u + 1)**(((q^5) - 1) / 6)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x86b76f821b329076,
                0x408bf52b4d19b614,
                0x53dfb9d0d985e92d,
                0x051e20146982d2a7,
            ],
        }),
        c1: Fq(MclFq {
            d: [
                0x0fbc9cd47752ebc7,
                0x6d8fffe33415de24,
                0xbef22cf038cf41b9,
                0x15c0edff3c66bf54,
            ],
        }),
    },
    // Fq2(u + 1)**(((q^6) - 1) / 6)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x68c3488912edefaa,
                0x8d087f6872aabf4f,
                0x51e1a24709081231,
                0x2259d6b14729c0fa,
            ],
        }),
        c1: Fq(MclFq {
            d: [0x0, 0x0, 0x0, 0x0],
        }),
    },
    // Fq2(u + 1)**(((q^7) - 1) / 6)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x8c84e580a568b440,
                0xcd164d1de0c21302,
                0xa692585790f737d5,
                0x2d7100fdc71265ad,
            ],
        }),
        c1: Fq(MclFq {
            d: [
                0x99fdddf38c33cfd5,
                0xc77267ed1213e931,
                0xdc2052142da18f36,
                0x1fbcf75c2da80ad7,
            ],
        }),
    },
    // Fq2(u + 1)**(((q^8) - 1) / 6)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x71930c11d782e155,
                0xa6bb947cffbe3323,
                0xaa303344d4741444,
                0x2c3b3f0d26594943,
            ],
        }),
        c1: Fq(MclFq {
            d: [0x0, 0x0, 0x0, 0x0],
        }),
    },
    // Fq2(u + 1)**(((q^9) - 1) / 6)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x05cd75fe8a3623ca,
                0x8c8a57f293a85cee,
                0x52b29e86b7714ea8,
                0x2852e0e95d8f9306,
            ],
        }),
        c1: Fq(MclFq {
            d: [
                0x8a41411f14e0e40e,
                0x59e26809ddfe0b0d,
                0x1d2e2523f4d24d7d,
                0x09fc095cf1414b83,
            ],
        }),
    },
    // Fq2(u + 1)**(((q^10) - 1) / 6)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0x08cfc388c494f1ab,
                0x19b315148d1373d4,
                0x584e90fdcb6c0213,
                0x09e1685bdf2f8849,
            ],
        }),
        c1: Fq(MclFq {
            d: [0x0, 0x0, 0x0, 0x0],
        }),
    },
    // Fq2(u + 1)**(((q^11) - 1) / 6)
    Fq2 {
        c0: Fq(MclFq {
            d: [
                0xb5691c94bd4a6cd1,
                0x56f575661b581478,
                0x64708be5a7fb6f30,
                0x2b462e5e77aecd82,
            ],
        }),
        c1: Fq(MclFq {
            d: [
                0x2c63ef42612a1180,
                0x29f16aae345bec69,
                0xf95e18c648b216a4,
                0x1aa36073a4cae0d4,
            ],
        }),
    },
];

// -((2**256) mod q) mod q
pub const NEGATIVE_ONE: Fq = Fq(MclFq {
    d: [
        0x974bc177a0000006,
        0xf13771b2da58a367,
        0x51e1a2470908122e,
        0x2259d6b14729c0fa,
    ],
});

/// R = 2^256 mod q
const R: FqRepr = FqRepr([1, 0, 0, 0]);

impl AsRef<[u64]> for FqRepr {
    fn as_ref(&self) -> &[u64] {
        &self.0
    }
}

impl AsMut<[u64]> for FqRepr {
    fn as_mut(&mut self) -> &mut [u64] {
        &mut self.0
    }
}

impl AsRef<MclFq> for Fq {
    fn as_ref(&self) -> &MclFq {
        &self.0
    }
}

impl AsMut<MclFq> for Fq {
    fn as_mut(&mut self) -> &mut MclFq {
        &mut self.0
    }
}

const LIMBS: usize = 4;
const LIMB_BITS: usize = 64;

impl fmt::Debug for FqRepr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "0x")?;
        for &b in self.0.iter().rev() {
            write!(f, "{:016x}", b)?;
        }
        Ok(())
    }
}

impl fmt::Display for FqRepr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "0x")?;
        for &b in self.0.iter().rev() {
            write!(f, "{:016x}", b)?;
        }
        Ok(())
    }
}

impl From<u64> for FqRepr {
    fn from(val: u64) -> FqRepr {
        FqRepr([val, 0, 0, 0])
    }
}

impl From<u64> for Fq {
    fn from(val: u64) -> Fq {
        Fq::from_repr(FqRepr::from(val)).expect("single u64 is always less than the modulus")
    }
}

impl Ord for FqRepr {
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

impl PartialOrd for FqRepr {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for FqRepr {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl Eq for FqRepr {}

impl Hash for FqRepr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for limb in self.as_ref().iter() {
            limb.hash(state);
        }
    }
}

impl ::rand::Rand for FqRepr {
    #[inline(always)]
    fn rand<R: ::rand::Rng>(rng: &mut R) -> Self {
        FqRepr(rng.gen())
    }
}

impl PrimeFieldRepr for FqRepr {
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

/// Elements are ordered lexicographically.
impl Ord for Fq {
    #[inline(always)]
    fn cmp(&self, other: &Fq) -> cmp::Ordering {
        self.into_repr().cmp(&other.into_repr())
    }
}

impl PartialOrd for Fq {
    #[inline(always)]
    fn partial_cmp(&self, other: &Fq) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for Fq {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tmp = self.to_bytes_le();
        write!(f, "Fq(0x")?;
        for &b in tmp.iter().rev() {
            write!(f, "{:02x}", b)?;
        }
        write!(f, ")")?;
        Ok(())
    }
}

impl fmt::Display for Fq {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tmp = self.to_bytes_le();
        write!(f, "Fq(0x")?;
        for &b in tmp.iter().rev() {
            write!(f, "{:02x}", b)?;
        }
        write!(f, ")")?;
        Ok(())
    }
}

impl From<Fq> for FqRepr {
    fn from(val: Fq) -> Self {
        val.into_repr()
    }
}

impl From<Fq> for MclFq {
    fn from(val: Fq) -> MclFq {
        val.0
    }
}

impl From<MclFq> for Fq {
    fn from(val: MclFq) -> Fq {
        Fq(val)
    }
}

impl Default for Fq {
    fn default() -> Self {
        Fq::zero()
    }
}

impl Eq for Fq {}

impl PartialEq for Fq {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0.d[0] == other.0.d[0]
            && self.0.d[1] == other.0.d[1]
            && self.0.d[2] == other.0.d[2]
            && self.0.d[3] == other.0.d[3]
    }
}

impl<'a> Neg for &'a Fq {
    type Output = Fq;

    #[inline]
    fn neg(self) -> Fq {
        self.neg()
    }
}

impl Neg for Fq {
    type Output = Fq;

    #[inline]
    fn neg(self) -> Fq {
        -&self
    }
}

impl<'a, 'b> Sub<&'b Fq> for &'a Fq {
    type Output = Fq;

    #[inline]
    fn sub(self, rhs: &'b Fq) -> Fq {
        self.sub(rhs)
    }
}

impl<'a, 'b> Add<&'b Fq> for &'a Fq {
    type Output = Fq;

    #[inline]
    fn add(self, rhs: &'b Fq) -> Fq {
        self.add(rhs)
    }
}

impl<'a, 'b> Mul<&'b Fq> for &'a Fq {
    type Output = Fq;

    #[inline]
    fn mul(self, rhs: &'b Fq) -> Fq {
        self.mul(rhs)
    }
}

// impl_binops_additive!(Fq, Fq, Field);
// impl_binops_multiplicative!(Fq, Fq, Field);

impl Field for Fq {
    fn zero() -> Self {
        Fq(MclFq { d: [0, 0, 0, 0] })
    }

    fn one() -> Self {
        Fq(MclFq {
            d: [
                0xd35d438dc58f0d9d,
                0xa78eb28f5c70b3d,
                0x666ea36f7879462c,
                0xe0a77c19a07df2f,
            ],
        })
    }

    fn is_zero(&self) -> bool {
        self == &Self::zero()
    }

    fn square(&mut self) {
        check_curve_init();
        unsafe { mclBnFp_sqr(&mut self.0, &self.0) }
    }

    fn double(&mut self) {
        check_curve_init();
        unsafe { mclBnFp_add(self.as_mut(), self.as_ref(), self.as_ref()) }
    }

    fn negate(&mut self) {
        check_curve_init();
        unsafe { mclBnFp_neg(self.as_mut(), self.as_ref()) };
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

        let mut x = unsafe { MclFq::uninit() };
        MclFq::inv(&mut x, self.as_ref());

        Some(Fq(x))
    }

    fn frobenius_map(&mut self, _: usize) {
        // This has no effect in a prime field.
    }
}

impl Hash for Fq {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for limb in self.as_ref().d.iter() {
            limb.hash(state);
        }
    }
}

impl ::rand::Rand for Fq {
    /// Computes a uniformly random element using rejection sampling.
    /// `_rng` is for compatible with old call
    fn rand<R: ::rand::Rng>(_rng: &mut R) -> Self {
        check_curve_init();
        let mut x = MclFq::default();
        x.set_by_csprng();
        Fq(x)
    }
}

const MODULUS: FqRepr = FqRepr([
    0x3c208c16d87cfd47,
    0x97816a916871ca8d,
    0xb85045b68181585d,
    0x30644e72e131a029,
]);

impl FqRepr {
    pub const fn new(raw: [u64; 4]) -> Self {
        FqRepr(raw)
    }
}

const R2: Fq = Fq(MclFq {
    d: [
        0xf32cfc5b538afa89,
        0xb5e71911d44501fb,
        0x47ab1eff0a417ff6,
        0x06d89f71cab8351f,
    ],
});

impl PrimeField for Fq {
    type Repr = FqRepr;

    fn from_repr(repr: Self::Repr) -> Result<Self, PrimeFieldDecodingError> {
        if FqRepr(repr.0) < MODULUS {
            let mut out = Fq(MclFq { d: repr.0 });
            out.mul_assign(&R2);

            Ok(out)
        } else {
            Err(PrimeFieldDecodingError::NotInField(
                "not in field".to_string(),
            ))
        }
    }
    fn from_raw_repr(repr: Self::Repr) -> Result<Self, PrimeFieldDecodingError> {
        if FqRepr(repr.0) < MODULUS {
            Ok(Fq(MclFq { d: repr.0 }))
        } else {
            Err(PrimeFieldDecodingError::NotInField(
                "not in field".to_string(),
            ))
        }
    }
    /// Convert a biginteger representation into a prime field element, if
    /// the number is an element of the field.
    fn into_repr(&self) -> Self::Repr {
        check_curve_init();
        let mut out = unsafe { MclFq::uninit() };
        MclFq::mul(&mut out, self.as_ref(), &MclFq { d: R.0 });
        FqRepr(out.d)
    }

    fn into_raw_repr(&self) -> Self::Repr {
        FqRepr(self.0.d)
    }

    fn char() -> Self::Repr {
        MODULUS
    }

    const NUM_BITS: u32 = 254;

    const CAPACITY: u32 = 253;

    fn multiplicative_generator() -> Self {
        Fq::from_repr(FqRepr([2, 0, 0, 0])).unwrap()
    }

    const S: u32 = 1;

    fn root_of_unity() -> Self {
        Fq::from_repr(FqRepr([1, 0, 0, 0])).unwrap()
    }
}

impl ff::SqrtField for Fq {
    fn legendre(&self) -> ff::LegendreSymbol {
        const MOD_MINUS_1_OVER_2: [u64; 4] = [
            0x9e10460b6c3e7ea3,
            0xcbc0b548b438e546,
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
        // Shank's algorithm for q mod 4 = 3
        // https://eprint.iacr.org/2012/685.pdf (page 9, algorithm 2)
        // power = (modulus - 3) / 4
        let mut a1 = self.pow(&[
            0x4f082305b61f3f51,
            0x65e05aa45a1c72a3,
            0x6e14116da0605617,
            0xc19139cb84c680a,
        ]);

        let mut a0 = a1;
        a0.square();
        a0 = &a0 * &self;
        // modulus - (2**256 % modulus)
        const RNEG: [u64; 4] = [
            0x68c3488912edefaa,
            0x8d087f6872aabf4f,
            0x51e1a24709081231,
            0x2259d6b14729c0fa,
        ];

        if a0.0.d == RNEG {
            None
        } else {
            a1 = &a1 * &self;
            Some(a1)
        }
    }
}

impl Fq {
    /// Attempts to convert a little-endian byte representation of
    /// a scalar into an `Fq`, failing if the input is not canonical.
    pub fn from_bytes_le(bytes: &[u8; 32]) -> Option<Fq> {
        check_curve_init();
        let mut raw = unsafe { MclFq::uninit() };

        let l = raw.deserialize(bytes);

        if l {
            Some(Fq(raw))
        } else {
            None
        }
    }

    /// Attempts to convert a big-endian byte representation of
    /// a scalar into an `Fq`, failing if the input is not canonical.
    pub fn from_bytes_be(bytes: &[u8; 32]) -> Option<Fq> {
        let mut bytes = bytes.clone();
        bytes.reverse();

        Fq::from_bytes_le(&bytes)
    }

    /// Converts an element of `Fq` into a byte representation in
    /// little-endian byte order.
    pub fn to_bytes_le(&self) -> [u8; 32] {
        check_curve_init();

        let mut out = [0u8; 32];
        out.copy_from_slice(&self.0.serialize());

        out
    }

    /// Converts an element of `Fq` into a byte representation in
    /// big-endian byte order.
    pub fn to_bytes_be(&self) -> [u8; 32] {
        let mut out = self.to_bytes_le();
        out.reverse();

        out
    }

    #[inline]
    pub fn add(&self, rhs: &Fq) -> Fq {
        check_curve_init();

        let mut out = unsafe { MclFq::uninit() };
        MclFq::add(&mut out, self.as_ref(), rhs.as_ref());

        Fq(out)
    }

    #[inline]
    pub fn neg(&self) -> Fq {
        let mut out = *self;
        out.negate();

        out
    }

    #[inline]
    pub fn sub(&self, rhs: &Fq) -> Fq {
        check_curve_init();

        let mut out = unsafe { MclFq::uninit() };
        MclFq::sub(&mut out, self.as_ref(), rhs.as_ref());

        Fq(out)
    }

    #[inline]
    pub fn mul(&self, rhs: &Fq) -> Fq {
        check_curve_init();

        let mut out = unsafe { MclFq::uninit() };
        MclFq::mul(&mut out, self.as_ref(), rhs.as_ref());

        Fq(out)
    }

    #[inline(always)]
    fn is_valid(&self) -> bool {
        self.0.is_valid()
    }
}

#[cfg(test)]
mod tests {
    use super::{Fq, FqRepr, MODULUS};
    use crate::bn256::check_curve_init;
    use crate::mcl::Fp as MclFq;
    use ff::{Field, PrimeField, PrimeFieldRepr, SqrtField};
    use rand::Rand;

    #[test]
    fn test_fq_repr_from() {
        assert_eq!(FqRepr::from(100), FqRepr([100, 0, 0, 0]));
        assert_eq!(FqRepr::from(3), FqRepr([3, 0, 0, 0]));
    }

    #[test]
    fn test_fq_repr_is_odd() {
        assert!(!FqRepr::from(0).is_odd());
        assert!(FqRepr::from(0).is_even());
        assert!(FqRepr::from(1).is_odd());
        assert!(!FqRepr::from(1).is_even());
        assert!(!FqRepr::from(324834872).is_odd());
        assert!(FqRepr::from(324834872).is_even());
        assert!(FqRepr::from(324834873).is_odd());
        assert!(!FqRepr::from(324834873).is_even());
    }

    #[test]
    fn test_fq_repr_num_bits() {
        let mut a = FqRepr::from(0);
        assert_eq!(0, a.num_bits());
        a = FqRepr::from(1);
        for i in 1..257 {
            assert_eq!(i, a.num_bits());
            a.mul2();
        }
        assert_eq!(0, a.num_bits());
    }

    #[test]
    fn test_fq_is_valid() {
        check_curve_init();
        let mut a = Fq(MclFq { d: MODULUS.0 });
        assert!(!a.is_valid());
        a = &a - &Fq(MclFq { d: [1, 0, 0, 0] });
        assert!(a.is_valid());
        assert!(Fq::from(0u64).is_valid());
        assert!(Fq(MclFq {
            d: [
                0xdf4671abd14dab3e,
                0xe2dc0c9f534fbd33,
                0x31ca6c880cc444a6,
                0x257a67e70ef33359
            ]
        })
        .is_valid());
        assert!(!Fq(MclFq {
            d: [
                0xffffffffffffffff,
                0xffffffffffffffff,
                0xffffffffffffffff,
                0xffffffffffffffff,
            ]
        })
        .is_valid());

        let mut rng = rand::thread_rng();

        for _ in 0..1000 {
            let a = Fq::rand(&mut rng);
            assert!(a.is_valid());
        }
    }

    #[test]
    fn test_fq_repr_display() {
        assert_eq!(
            format!("{}", Fq::into_repr(&Fq::one())),
            "0x0000000000000000000000000000000000000000000000000000000000000001".to_string()
        );
        assert_eq!(
            format!("{}", FqRepr([0, 0, 0, 0])),
            "0x0000000000000000000000000000000000000000000000000000000000000000".to_string()
        );
    }

    #[test]
    fn test_fq_num_bits() {
        assert_eq!(Fq::NUM_BITS, 254);
        assert_eq!(Fq::CAPACITY, 253);
    }

    #[test]
    fn test_fq_sqrt() {
        let mut rng = rand::thread_rng();
        assert_eq!(Fq::zero().sqrt().unwrap(), Fq::zero());

        for _ in 0..1000 {
            // Ensure sqrt(a^2) = a or -a
            let a = Fq::rand(&mut rng);
            let mut nega = a;
            nega.negate();
            let mut b = a;
            b.square();

            let b = b.sqrt().unwrap();

            assert!(a == b || nega == b);
        }

        for _ in 0..1000 {
            // Ensure sqrt(a)^2 = a for random a
            let a = Fq::rand(&mut rng);

            if let Some(mut tmp) = a.sqrt() {
                tmp.square();

                assert_eq!(a, tmp);
            }
        }
    }

    #[test]
    fn test_fq_sqrt_2() {
        let x = Fq::from_str("4").unwrap();
        print!("x = {}\n", x);
        if let Some(y) = x.sqrt() {
            print!("y = {}\n", y);
            let mut y_other = y;
            y_other.negate();
            print!("y' = {}\n", y_other);
        }
    }

    #[test]
    fn fq_field_tests() {
        crate::tests::field::random_field_tests::<Fq>();
        crate::tests::field::random_sqrt_tests::<Fq>();
        crate::tests::field::random_frobenius_tests::<Fq, _>(Fq::char(), 13);
        crate::tests::field::from_str_tests::<Fq>();
    }
}
