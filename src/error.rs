use thiserror::Error;

#[derive(Error, Debug, PartialEq, Eq)]
pub enum Error {
    #[error("Math overflow error.")]
    MathOverflow,

    #[error("Token not found error.")]
    TokenNotFound,

    #[error("Insufficient funds error.")]
    InsufficientFunds,

    #[error("Invalid transaction context error.")]
    InvalidTransactionContext,

    #[error("Invalid signer error.")]
    InvalidSigner,

    #[error("Exceed max supply error.")]
    ExceededMaxSupply,

    #[error("Invalid address error.")]
    InvalidAddress,
}
