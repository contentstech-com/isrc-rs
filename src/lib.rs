use std::fmt::{self, Display, Formatter};
use std::str::{from_utf8_unchecked, FromStr};

use bitcode::{Decode, Encode};
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// International Standard Recording Code (ISRC)
///
/// ###### References
/// - <https://isrc.ifpi.org/en/isrc-standard/structure>
/// - <https://www.ifpi.org/wp-content/uploads/2021/02/ISRC_Handbook.pdf>
/// - <https://isrc.ifpi.org/downloads/Valid_Characters.pdf>
/// - <https://isrc.ifpi.org/downloads/ISRC_Bulletin-2015-01.pdf>
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Encode, Decode)]
pub struct Isrc {
    /// First two characters of prefix codes. For example, "AA" in "ISRC AA-6Q7-20-00047". It'll be
    /// stored as-is.
    agency_prefix: [u8; 2],
    /// Last three characters of prefix codes. For example, "6Q7" in "ISRC AA-6Q7-20-00047". It'll
    /// be interpreted as a base-36 number, and stored as a u16 number.
    registrant_prefix: u16,
    /// Year of reference and designation code. For example, "2000047" in "ISRC AA-6Q7-20-00047".
    /// It'll be interpreted as a base-10 number, and stored as a u32 number. Only LSB 24 bits are
    /// used.
    rest: u32,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Error, Encode, Decode)]
pub enum IsrcParseError {
    #[error("Invalid length (expected 12B input, found {found}B)")]
    InvalidLength { found: usize },
    #[error(r"Invalid agency prefix (expected [a-zA-Z], found '\x{found:x}' at {pos})")]
    InvalidAgencyPrefix { found: u8, pos: u8 },
    #[error(r"Invalid registrant prefix (expected [a-zA-Z0-9], found '\x{found:x}' at {pos})")]
    InvalidRegistrantPrefix { found: u8, pos: u8 },
    #[error(r"Registrant prefix out of range (expected 0 <= value < 36*36*36, found {value})")]
    RegistrantPrefixOutOfRange { value: u16 },
    #[error(r"Invalid digit (expected [0-9], found '\x{found:x}' at {pos})")]
    InvalidDigit { found: u8, pos: u8 },
    #[error(r"Rest value out of range (expected 0 <= value < 10000000, found {value})")]
    ValueOutOfRange { value: u32 },
}

impl Isrc {
    pub const fn from_code(code: &str) -> Result<Self, IsrcParseError> {
        let code = code.as_bytes();
        if code.len() != 12 {
            return Err(IsrcParseError::InvalidLength { found: code.len() });
        }

        macro_rules! agency {
            ($pos:expr) => {
                match code[$pos] {
                    b'a'..=b'z' => code[$pos] ^ 0b0010_0000, // to_ascii_uppercase
                    b'A'..=b'Z' => code[$pos],
                    _ => {
                        return Err(IsrcParseError::InvalidAgencyPrefix {
                            found: code[$pos],
                            pos: $pos,
                        })
                    }
                }
            };
        }
        macro_rules! registrant {
            ($pos:expr) => {
                match code[$pos] {
                    b'0'..=b'9' => code[$pos] - b'0',
                    b'a'..=b'z' => code[$pos] - b'a' + 10,
                    b'A'..=b'Z' => code[$pos] - b'A' + 10,
                    _ => return Err(IsrcParseError::InvalidRegistrantPrefix { found: code[$pos], pos: $pos }),
                } as u16
            };
        }

        macro_rules! d {
            ($pos:expr) => {
                match code[$pos] {
                    b'0'..=b'9' => code[$pos] - b'0',
                    _ => return Err(IsrcParseError::InvalidDigit { found: code[$pos], pos: $pos }),
                } as u32
            };
        }

        Ok(Isrc {
            agency_prefix: [agency!(0), agency!(1)],
            registrant_prefix: registrant!(2) * 36 * 36 + registrant!(3) * 36 + registrant!(4),
            rest: d!(5) * 1_000_000
                + d!(6) * 100_000
                + d!(7) * 10_000
                + d!(8) * 1_000
                + d!(9) * 100
                + d!(10) * 10
                + d!(11),
        })
    }

    pub fn to_code(self) -> String {
        let mut n = self.registrant_prefix;

        let d2 = ascii_uppercase_from_digit_base36(n);
        n /= 36;

        let d1 = ascii_uppercase_from_digit_base36(n);
        n /= 36;

        let d0 = ascii_uppercase_from_digit_base36(n);

        format!(
            "{}{}{}{}{:07}",
            unsafe { from_utf8_unchecked(&self.agency_prefix) },
            d0,
            d1,
            d2,
            self.rest,
        )
    }

    pub const fn from_bytes(bytes: &[u8; 8]) -> Result<Self, IsrcParseError> {
        // Stored according to the default Rust struct layout.
        let rest = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        let agency_prefix = [bytes[4], bytes[5]];
        let registrant_prefix = u16::from_le_bytes([bytes[6], bytes[7]]);

        if !agency_prefix[0].is_ascii_uppercase() {
            return Err(IsrcParseError::InvalidAgencyPrefix {
                found: agency_prefix[0],
                pos: 4,
            });
        }
        if !agency_prefix[1].is_ascii_uppercase() {
            return Err(IsrcParseError::InvalidAgencyPrefix {
                found: agency_prefix[1],
                pos: 5,
            });
        }
        if registrant_prefix >= 36 * 36 * 36 {
            return Err(IsrcParseError::RegistrantPrefixOutOfRange {
                value: registrant_prefix,
            });
        }
        if rest >= 10_000_000 {
            return Err(IsrcParseError::ValueOutOfRange { value: rest });
        }

        Ok(Isrc {
            agency_prefix,
            registrant_prefix,
            rest,
        })
    }

    pub const fn to_bytes(self) -> [u8; 8] {
        [
            self.rest as u8,
            (self.rest >> 8) as u8,
            (self.rest >> 16) as u8,
            (self.rest >> 24) as u8,
            self.agency_prefix[0],
            self.agency_prefix[1],
            self.registrant_prefix as u8,
            (self.registrant_prefix >> 8) as u8,
        ]
    }
}

#[test]
fn test_isrc() -> Result<(), IsrcParseError> {
    let isrc = Isrc::from_code("AA6Q72000047")?;
    assert_eq!(
        isrc,
        Isrc {
            agency_prefix: [b'A', b'A'],
            registrant_prefix: 8719,
            rest: 20_00047,
        }
    );
    assert_eq!(isrc.to_code(), "AA6Q72000047");

    // Lowercase
    let isrc = Isrc::from_code("aa6q72000047")?;
    assert_eq!(
        isrc,
        Isrc {
            agency_prefix: [b'A', b'A'],
            registrant_prefix: 8719,
            rest: 20_00047,
        }
    );
    assert_eq!(isrc.to_code(), "AA6Q72000047");

    // Invalid inputs
    assert_matches::assert_matches!(
        Isrc::from_code("00A6Q7200047"),
        Err(IsrcParseError::InvalidAgencyPrefix {
            found: b'0',
            pos: 0
        })
    );

    assert_matches::assert_matches!(
        Isrc::from_code("AA-6Q7200047"),
        Err(IsrcParseError::InvalidRegistrantPrefix {
            found: b'-',
            pos: 2
        })
    );

    assert_matches::assert_matches!(
        Isrc::from_code("aa6q7200047\n"),
        Err(IsrcParseError::InvalidDigit {
            found: b'\n',
            pos: 11
        })
    );

    Ok(())
}

#[test]
fn test_isrc_from_bytes() -> Result<(), IsrcParseError> {
    let isrc = Isrc::from_bytes(&[0xB1, 0xCB, 0x74, 0x00, 0x5A, 0x5A, 0x0F, 0x22])?;
    assert_eq!(
        isrc,
        Isrc {
            agency_prefix: [b'Z', b'Z'],
            registrant_prefix: 8719,
            rest: 76_54321,
        }
    );
    assert_eq!(isrc.to_code(), "ZZ6Q77654321");

    // Invalid inputs
    let fail = Isrc::from_bytes(&[0xB1, 0xCB, 0x74, 0x00, 0x5A, 0x00, 0x0F, 0x22]);
    assert_matches::assert_matches!(
        fail,
        Err(IsrcParseError::InvalidAgencyPrefix {
            found: 0x00,
            pos: 5
        })
    );

    let fail = Isrc::from_bytes(&[0xB1, 0xCB, 0x74, 0x00, 0x5A, 0x5A, 0xFF, 0xFF]);
    assert_matches::assert_matches!(
        fail,
        Err(IsrcParseError::RegistrantPrefixOutOfRange { value: 0xFFFF })
    );

    let fail = Isrc::from_bytes(&[0xFF, 0xFF, 0xFF, 0xFF, 0x5A, 0x5A, 0x0F, 0x22]);
    assert_matches::assert_matches!(
        fail,
        Err(IsrcParseError::ValueOutOfRange { value: 0xFFFFFFFF })
    );

    Ok(())
}

#[test]
fn test_isrc_to_bytes() {
    assert_eq!(
        Isrc {
            agency_prefix: [b'A', b'Z'],
            registrant_prefix: 8719,
            rest: 76_54321,
        }
        .to_bytes(),
        [0xB1, 0xCB, 0x74, 0x00, b'A', b'Z', 0x0F, 0x22]
    );
}

impl FromStr for Isrc {
    type Err = IsrcParseError;

    fn from_str(code: &str) -> Result<Self, IsrcParseError> {
        Isrc::from_code(code)
    }
}

#[test]
fn test_isrc_from_str() -> Result<(), IsrcParseError> {
    let isrc: Isrc = "AA6Q72000047".parse()?;
    assert_eq!(
        isrc,
        Isrc {
            agency_prefix: [b'A', b'A'],
            registrant_prefix: 8719,
            rest: 20_00047,
        }
    );
    assert_eq!(isrc.to_code(), "AA6Q72000047");

    // Lowercase
    let isrc: Isrc = "aa6q72000047".parse()?;
    assert_eq!(
        isrc,
        Isrc {
            agency_prefix: [b'A', b'A'],
            registrant_prefix: 8719,
            rest: 20_00047,
        }
    );
    assert_eq!(isrc.to_code(), "AA6Q72000047");

    // Invalid inputs
    assert_matches::assert_matches!(
        "00A6Q7200047".parse::<Isrc>(),
        Err(IsrcParseError::InvalidAgencyPrefix {
            found: b'0',
            pos: 0
        })
    );

    assert_matches::assert_matches!(
        "AA6Q7200047".parse::<Isrc>(),
        Err(IsrcParseError::InvalidLength { found: 11 })
    );

    assert_matches::assert_matches!(
        "AA6Q7200047910".parse::<Isrc>(),
        Err(IsrcParseError::InvalidLength { found: 14 })
    );

    Ok(())
}

impl Display for Isrc {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut n = self.registrant_prefix;

        let d2 = ascii_uppercase_from_digit_base36(n % 36);
        n /= 36;

        let d1 = ascii_uppercase_from_digit_base36(n % 36);
        n /= 36;

        let d0 = ascii_uppercase_from_digit_base36(n % 36);

        write!(
            f,
            "ISRC {}-{}{}{}-{:02}-{:05}",
            unsafe { from_utf8_unchecked(&self.agency_prefix) },
            d0,
            d1,
            d2,
            self.rest / 100_000,
            self.rest % 100_000,
        )
    }
}

#[test]
fn test_isrc_display() -> Result<(), IsrcParseError> {
    assert_eq!(
        Isrc::from_code("AA6Q72000047")?.to_string(),
        "ISRC AA-6Q7-20-00047"
    );
    assert_eq!(
        Isrc::from_code("Zz6q72412345")?.to_string(),
        "ISRC ZZ-6Q7-24-12345"
    );

    Ok(())
}

impl Serialize for Isrc {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        if serializer.is_human_readable() {
            self.to_code().serialize(serializer)
        } else {
            self.to_bytes().serialize(serializer)
        }
    }
}

#[test]
fn test_isrc_serialize() -> Result<(), Box<dyn std::error::Error>> {
    use std::collections::HashMap;

    let isrc = Isrc::from_code("AA6Q72000047")?;

    // JSON (human readable)
    assert_eq!(serde_json::to_string(&isrc)?, r#""AA6Q72000047""#);
    // TOML (human readable)
    let table: HashMap<&str, Isrc> = HashMap::from_iter([("isrc", isrc)]);
    assert_eq!(
        toml::to_string(&table)?,
        r#"isrc = "AA6Q72000047"
"#
    );
    // Bincode (binary)
    assert_eq!(
        bincode::serialize(&isrc)?,
        b"\xAF\x84\x1E\x00\x41\x41\x0f\x22"
    );

    Ok(())
}

impl<'de> Deserialize<'de> for Isrc {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        if deserializer.is_human_readable() {
            Isrc::from_code(&String::deserialize(deserializer)?)
        } else {
            Isrc::from_bytes(&<[u8; 8]>::deserialize(deserializer)?)
        }
        .map_err(serde::de::Error::custom)
    }
}

#[test]
fn test_isrc_deserialize() -> Result<(), Box<dyn std::error::Error>> {
    #[derive(Deserialize)]
    struct TestInput {
        isrc: Isrc,
    }

    // JSON (human readable)
    let v: TestInput = serde_json::from_str(r#"{"isrc":"AA6Q72000047"}"#)?;
    assert_eq!(
        v.isrc,
        Isrc {
            agency_prefix: [b'A', b'A'],
            registrant_prefix: 8719,
            rest: 20_00047,
        }
    );
    // TOML (human readable)
    let v: TestInput = toml::from_str(r#"isrc = "AA6Q72000047""#)?;
    assert_eq!(
        v.isrc,
        Isrc {
            agency_prefix: [b'A', b'A'],
            registrant_prefix: 8719,
            rest: 20_00047,
        }
    );
    // Bincode (binary)
    let v: TestInput = bincode::deserialize(b"\xAF\x84\x1E\x00\x41\x41\x0f\x22")?;
    assert_eq!(
        v.isrc,
        Isrc {
            agency_prefix: [b'A', b'A'],
            registrant_prefix: 8719,
            rest: 20_00047,
        }
    );

    Ok(())
}

const fn ascii_uppercase_from_digit_base36(d: u16) -> char {
    let d = (d % 36) as u8;
    (match d {
        0..=9 => d + b'0',
        10..=35 => d + b'A' - 10,
        _ => unreachable!(),
    }) as char
}
