//! Module provide mock type which will simulate
//! decentralized repo for tokens metadata.

pub struct TokenMetadata {
    pub name: String,
    pub symbol: String,
    pub image: String,
    pub props: Option<Vec<String>>,
}
