//! Module provide interface for standardized multi token contract.

use crate::Error;

pub trait MultiToken {
    type Id: Copy;
    type Address: Clone;

    /// Transfers `value` amount of `id` tokens `from` -> `to` address.
    ///
    /// Transaction signer must be permitted to `transfer` `id` tokens.
    fn transfer(
        &mut self,
        from: &Self::Address,
        to: &Self::Address,
        id: Self::Id,
        value: u128,
    ) -> Result<(), Error>;

    /// Batches multiple `Self::transfer` operations into single.
    ///
    /// `ids` must match `values`.
    fn transfer_batch(
        &mut self,
        from: &Self::Address,
        to: &Self::Address,
        ids: &[Self::Id],
        values: &[u128],
    ) -> Result<(), Error> {
        for (id, value) in ids.iter().zip(values) {
            self.transfer(from, to, *id, *value)?;
        }

        Ok(())
    }

    /// Mints `value` of tokens by `id` for `to` address.
    ///
    /// Transaction signer must be permitted to `mint` new `id` tokens.
    fn mint(&mut self, to: &Self::Address, id: Self::Id, value: u128) -> Result<(), Error>;

    /// Batches multiple `Self::mint` operations into single.
    ///
    /// `ids` must match `values`.
    fn mint_batch(
        &mut self,
        to: &Self::Address,
        ids: &[Self::Id],
        values: &[u128],
    ) -> Result<(), Error> {
        for (id, value) in ids.iter().zip(values) {
            self.mint(to, *id, *value)?;
        }

        Ok(())
    }

    /// Burns `value` of token `id` for `from`.
    ///
    /// If `value` is `None` then remaining amount will be burned.
    ///
    /// Transaction signer must be permitted to `burn` `id` tokens.
    fn burn(
        &mut self,
        from: &Self::Address,
        id: Self::Id,
        value: Option<u128>,
    ) -> Result<(), Error>;

    /// Batches multiple `Self::burn` operations into single.
    ///
    /// `ids` must match `values`.
    fn burn_batch(
        &mut self,
        from: &Self::Address,
        ids: &[Self::Id],
        values: &[Option<u128>],
    ) -> Result<(), Error> {
        for (id, value) in ids.iter().zip(values) {
            self.burn(from, *id, *value)?;
        }

        Ok(())
    }

    /// Sets approve for all tokens for `operator`.
    ///
    /// Transaction signer must be permitted to `approve` tokens.
    fn set_approve(&mut self, operator: &Self::Address, approved: bool) -> Result<(), Error>;

    /// Returns balance of `owner` for specific token `id`.
    fn balance_of(&self, owner: &Self::Address, id: Self::Id) -> Result<u128, Error>;

    /// Returns token metadata URI string.
    fn uri(&self, id: Self::Id) -> Result<String, Error>;
}
