use super::Address;

#[derive(Debug, Clone, Default)]
pub struct TransactionContext {
    pub signer: Address,
}
