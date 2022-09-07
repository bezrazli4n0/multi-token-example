//! Module provide example implementation of `MultiToken` interface.

use super::{Address, MultiToken, TokenType, TransactionContext};
use crate::Error;
use std::collections::HashMap;

/// Highest part(u64) - token id(tracked by nonce).
/// Lowest part(u64)  - used as index for non-fungible tokens(ignored in other cases).
pub type Id = u128;

#[derive(Debug, Clone, Default)]
pub struct MultiTokenContract {
    /// Simulate current transaction context.
    pub context: Option<TransactionContext>,

    /// Represent tokens balances.
    /// Layout: id(token) -> address -> balance.
    pub balances: HashMap<Id, HashMap<Address, u128>>,

    /// Represent token approvals.
    /// Layout: address(owner) -> address(operator) -> bool(is_approved).
    pub approvals: HashMap<Address, HashMap<Address, bool>>,

    /// Represent token creators.
    /// Layout: id(token) -> address(creator).
    pub creators: HashMap<Id, Address>,

    /// Represent token metadata.
    /// Layout: id(token) -> URI(metadata).
    pub metadata: HashMap<Id, String>,

    /// Global nonce for token id calculation.
    pub nonce: u64,
}

impl MultiTokenContract {
    pub fn get_current_context(&self) -> Result<&TransactionContext, Error> {
        if let Some(context) = &self.context {
            return Ok(context);
        } else {
            return Err(Error::InvalidTransactionContext);
        }
    }

    pub fn pack_id(high_part: u64, low_part: u64) -> Result<Id, Error> {
        Ok((high_part as u128) << 64 | low_part as u128)
    }

    pub fn unpack_id(id: Id) -> Result<(u64, u64), Error> {
        let high_part = (id >> 64) as u64;
        let low_part = id as u64 & u64::MAX;

        Ok((high_part, low_part))
    }

    pub fn assert_approved(&self, signer: &Address, from: &Address) -> Result<(), Error> {
        if signer != from {
            if let Some(operators) = self.approvals.get(from) {
                if let Some(is_approved) = operators.get(signer) {
                    if !is_approved {
                        return Err(Error::InvalidSigner);
                    }
                } else {
                    return Err(Error::InvalidSigner);
                }
            } else {
                return Err(Error::InvalidSigner);
            }
        }

        Ok(())
    }

    pub fn send_transaction(&mut self, signer: &Address) {
        self.context = Some(TransactionContext {
            signer: signer.clone(),
        });
    }

    pub fn process_transaction(&mut self) {
        self.context = None;
    }

    pub fn create_token(&mut self, token_type: TokenType, uri: String) -> Result<Id, Error> {
        let ctx = self.get_current_context()?;
        let signer = ctx.signer.clone();

        self.nonce = self.nonce.checked_add(1).ok_or(Error::MathOverflow)?;

        let index = if token_type == TokenType::NonFungible {
            1
        } else {
            0
        };

        let id = Self::pack_id(self.nonce, index)?;

        self.balances.insert(id, HashMap::new());
        self.approvals.insert(signer.clone(), HashMap::new());
        self.creators.insert(id, signer);
        self.metadata.insert(id, uri);

        Ok(id)
    }
}

impl MultiToken for MultiTokenContract {
    type Id = Id;
    type Address = Address;

    fn transfer(
        &mut self,
        from: &Address,
        to: &Address,
        id: Self::Id,
        value: u128,
    ) -> Result<(), Error> {
        let ctx = self.get_current_context()?;
        let signer = ctx.signer.clone();

        // Check that tx `signer` is permitted to transfer funds
        self.assert_approved(&signer, from)?;

        // Check that passed addresses is valid
        // ~Only simple cases for simulation~
        if to.is_empty() || from.is_empty() || signer.is_empty() {
            return Err(Error::InvalidAddress);
        }

        if let Some(token_balances) = self.balances.get_mut(&id) {
            let from_balance = token_balances
                .get_mut(from)
                .ok_or(Error::InsufficientFunds)?;

            if *from_balance < value {
                return Err(Error::InsufficientFunds);
            }

            *from_balance = from_balance.checked_sub(value).ok_or(Error::MathOverflow)?;

            if let Some(to_balance) = token_balances.get_mut(to) {
                *to_balance = to_balance.checked_add(value).ok_or(Error::MathOverflow)?;
            } else {
                token_balances.insert(to.clone(), value);
            }
        } else {
            return Err(Error::TokenNotFound);
        }

        Ok(())
    }

    fn mint(&mut self, to: &Address, id: Self::Id, value: u128) -> Result<(), Error> {
        let ctx = self.get_current_context()?;
        let signer = ctx.signer.clone();

        // Check that passed addresses is valid
        // ~Only simple cases for simulation~
        if to.is_empty() || signer.is_empty() {
            return Err(Error::InvalidAddress);
        }

        // Check that `signer` is token creator
        if let Some(creator) = self.creators.get(&id) {
            if &signer != creator {
                return Err(Error::InvalidSigner);
            }

            let (token_id, token_index) = Self::unpack_id(id)?;
            let (actual_id, actual_value) = if token_index == 1 {
                let base_uri = self.metadata.get(&id).unwrap();

                let next_token_index = token_index.checked_add(1).ok_or(Error::MathOverflow)?;
                let next_id = Self::pack_id(token_id, next_token_index)?;

                self.balances.insert(next_id, HashMap::new());
                self.approvals.insert(to.clone(), HashMap::new());
                self.creators.insert(next_id, to.clone());
                self.metadata
                    .insert(next_id, format!("{}-{}", base_uri, next_token_index));

                (next_id, 1)
            } else if token_index > 1 {
                return Err(Error::ExceededMaxSupply);
            } else {
                (id, value)
            };

            let token_balances = self
                .balances
                .get_mut(&actual_id)
                .ok_or(Error::TokenNotFound)?;
            if let Some(to_balance) = token_balances.get_mut(to) {
                *to_balance = to_balance
                    .checked_add(actual_value)
                    .ok_or(Error::MathOverflow)?;
            } else {
                token_balances.insert(to.clone(), actual_value);
            }
        } else {
            return Err(Error::TokenNotFound);
        }

        Ok(())
    }

    fn burn(&mut self, from: &Address, id: Self::Id, value: Option<u128>) -> Result<(), Error> {
        let ctx = self.get_current_context()?;
        let signer = ctx.signer.clone();

        // Check that passed addresses is valid
        // ~Only simple cases for simulation~
        if from.is_empty() || signer.is_empty() {
            return Err(Error::InvalidAddress);
        }

        // Check that tx `signer` is permitted to burn funds
        self.assert_approved(&signer, from)?;

        let token_balances = self.balances.get_mut(&id).ok_or(Error::TokenNotFound)?;
        let balance = token_balances
            .get_mut(from)
            .ok_or(Error::InsufficientFunds)?;
        *balance = if let Some(value) = value {
            let (_, token_index) = Self::unpack_id(id)?;
            if token_index != 0 {
                0
            } else {
                balance.checked_sub(value).ok_or(Error::MathOverflow)?
            }
        } else {
            0
        };

        Ok(())
    }

    fn set_approve(&mut self, operator: &Address, approved: bool) -> Result<(), Error> {
        let ctx = self.get_current_context()?;
        let signer = ctx.signer.clone();

        // Check that passed addresses is valid
        // ~Only simple cases for simulation~
        if operator.is_empty() || signer.is_empty() {
            return Err(Error::InvalidAddress);
        }

        if !self.approvals.contains_key(&signer) {
            self.approvals.insert(signer.clone(), HashMap::new());
        }

        let signer_approvals = self
            .approvals
            .get_mut(&signer)
            .ok_or(Error::InvalidSigner)?;

        if let Some(is_approved) = signer_approvals.get_mut(operator) {
            *is_approved = approved;
        } else {
            signer_approvals.insert(operator.clone(), approved);
        }

        Ok(())
    }

    fn balance_of(&self, owner: &Address, id: Self::Id) -> Result<u128, Error> {
        let token_balances = self.balances.get(&id).ok_or(Error::TokenNotFound)?;
        let balance = *token_balances.get(owner).unwrap_or(&0);

        Ok(balance)
    }

    fn uri(&self, id: Self::Id) -> Result<String, Error> {
        Ok(self.metadata.get(&id).ok_or(Error::TokenNotFound)?.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::TokenMetadata;

    #[test]
    fn success_pack_unpack_id_fungible() {
        let high_part = 1337;
        let low_part = 0;

        let id = MultiTokenContract::pack_id(high_part, low_part).unwrap();
        assert_eq!(id, 24663296826549670510592);

        let (token_id, token_index) = MultiTokenContract::unpack_id(id).unwrap();
        assert_eq!(token_id, 1337);
        assert_eq!(token_index, 0);
    }

    #[test]
    fn success_pack_unpack_id_non_fungible() {
        let high_part = 1337;
        let low_part = 1234;

        let id = MultiTokenContract::pack_id(high_part, low_part).unwrap();
        assert_eq!(id, 24663296826549670511826);

        let (token_id, token_index) = MultiTokenContract::unpack_id(id).unwrap();
        assert_eq!(token_id, 1337);
        assert_eq!(token_index, 1234);
    }

    #[test]
    fn success_metadata_mock() {
        // Simulate external registry
        // Technically this can be ipfs, arweave, etc..
        let mut registry: HashMap<String, TokenMetadata> = HashMap::new();
        registry.insert(
            String::from("hello-world-token"),
            TokenMetadata {
                name: String::from("Hello World Token!"),
                symbol: String::from("HWT"),
                image: String::from("https://google.com"),
                props: None,
            },
        );

        let mut contract = MultiTokenContract::default();
        let user = String::from("1");

        // 1. Create token
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::Fungible, String::from("hello-world-token"))
            .unwrap();
        contract.process_transaction();

        let uri = contract.uri(id).unwrap();
        assert!(registry.contains_key(&uri));
    }

    #[test]
    fn success_mint_batch() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");
        let user_2 = String::from("2");

        let first_id = {
            // 1. Create token
            contract.send_transaction(&user);
            let id = contract
                .create_token(TokenType::Fungible, String::from("hello-world-token"))
                .unwrap();
            contract.process_transaction();

            id
        };

        let second_id = {
            // 1. Create token
            contract.send_transaction(&user);
            let id = contract
                .create_token(TokenType::Fungible, String::from("hello-world-token"))
                .unwrap();
            contract.process_transaction();

            id
        };

        let third_id = {
            // 1. Create NFT
            contract.send_transaction(&user);
            let id = contract
                .create_token(TokenType::NonFungible, String::from("hello-world-nft"))
                .unwrap();
            contract.process_transaction();

            id
        };

        contract.send_transaction(&user);
        contract
            .mint_batch(
                &user_2,
                &[first_id, second_id, third_id],
                &[10000, 20000, 1],
            )
            .unwrap();
        contract.process_transaction();

        let nft_id = MultiTokenContract::pack_id(contract.nonce, 2).unwrap();

        assert_eq!(contract.balance_of(&user_2, first_id).unwrap(), 10000);
        assert_eq!(contract.balance_of(&user_2, second_id).unwrap(), 20000);
        assert_eq!(contract.balance_of(&user_2, third_id).unwrap(), 0);
        assert_eq!(contract.balance_of(&user_2, nft_id).unwrap(), 1);
    }

    #[test]
    fn success_mint_fungible() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");

        // 1. Create token
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::Fungible, String::from("hello-world-token"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint token
        contract.send_transaction(&user);
        contract.mint(&user, id, 10000).unwrap();
        contract.process_transaction();

        assert_eq!(contract.balance_of(&user, id).unwrap(), 10000);
    }

    #[test]
    fn success_mint_non_fungible() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");

        // 1. Create NFT
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::NonFungible, String::from("hello-world-nft"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint NFT
        contract.send_transaction(&user);
        contract.mint(&user, id, 1).unwrap();
        let nft_id = MultiTokenContract::pack_id(contract.nonce, 2).unwrap();
        contract.process_transaction();

        assert_eq!(contract.balance_of(&user, id).unwrap(), 0);
        assert_eq!(contract.balance_of(&user, nft_id).unwrap(), 1);
    }

    #[test]
    fn success_burn_batch() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");
        let user_2 = String::from("2");

        let first_id = {
            // 1. Create token
            contract.send_transaction(&user);
            let id = contract
                .create_token(TokenType::Fungible, String::from("hello-world-token"))
                .unwrap();
            contract.process_transaction();

            id
        };

        let second_id = {
            // 1. Create token
            contract.send_transaction(&user);
            let id = contract
                .create_token(TokenType::Fungible, String::from("hello-world-token"))
                .unwrap();
            contract.process_transaction();

            id
        };

        let third_id = {
            // 1. Create NFT
            contract.send_transaction(&user);
            let id = contract
                .create_token(TokenType::NonFungible, String::from("hello-world-nft"))
                .unwrap();
            contract.process_transaction();

            id
        };

        let nft_id = MultiTokenContract::pack_id(contract.nonce, 2).unwrap();

        contract.send_transaction(&user);
        contract
            .mint_batch(
                &user_2,
                &[first_id, second_id, third_id],
                &[10000, 20000, 1],
            )
            .unwrap();
        contract.process_transaction();

        contract.send_transaction(&user_2);
        contract
            .burn_batch(
                &user_2,
                &[first_id, second_id, nft_id],
                &vec![None, None, None],
            )
            .unwrap();
        contract.process_transaction();

        assert_eq!(contract.balance_of(&user_2, first_id).unwrap(), 0);
        assert_eq!(contract.balance_of(&user_2, second_id).unwrap(), 0);
        assert_eq!(contract.balance_of(&user_2, nft_id).unwrap(), 0);
    }

    #[test]
    fn success_burn_fungible() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");

        // 1. Create token
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::Fungible, String::from("hello-world-token"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint token
        contract.send_transaction(&user);
        contract.mint(&user, id, 10000).unwrap();
        contract.process_transaction();
        assert_eq!(contract.balance_of(&user, id).unwrap(), 10000);

        // 3. Burn token
        contract.send_transaction(&user);
        contract.burn(&user, id, None).unwrap();
        contract.process_transaction();

        assert_eq!(contract.balance_of(&user, id).unwrap(), 0);
    }

    #[test]
    fn success_burn_non_fungible() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");

        // 1. Create NFT
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::NonFungible, String::from("hello-world-nft"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint NFT
        contract.send_transaction(&user);
        contract.mint(&user, id, 1).unwrap();
        let nft_id = MultiTokenContract::pack_id(contract.nonce, 2).unwrap();
        contract.process_transaction();

        // 3. Burn NFT
        contract.send_transaction(&user);
        contract.burn(&user, nft_id, None).unwrap();
        contract.process_transaction();

        assert_eq!(contract.balance_of(&user, nft_id).unwrap(), 0);
    }

    #[test]
    fn success_transfer_batch() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");
        let user_2 = String::from("2");

        let first_id = {
            // 1. Create token
            contract.send_transaction(&user);
            let id = contract
                .create_token(TokenType::Fungible, String::from("hello-world-token"))
                .unwrap();
            contract.process_transaction();

            // 2. Mint token
            contract.send_transaction(&user);
            contract.mint(&user, id, 10000).unwrap();
            contract.process_transaction();

            assert_eq!(contract.balance_of(&user, id).unwrap(), 10000);

            id
        };

        let second_id = {
            // 1. Create token
            contract.send_transaction(&user);
            let id = contract
                .create_token(TokenType::Fungible, String::from("hello-world-token"))
                .unwrap();
            contract.process_transaction();

            // 2. Mint token
            contract.send_transaction(&user);
            contract.mint(&user, id, 20000).unwrap();
            contract.process_transaction();

            assert_eq!(contract.balance_of(&user, id).unwrap(), 20000);

            id
        };

        let third_id = {
            // 1. Create NFT
            contract.send_transaction(&user);
            let id = contract
                .create_token(TokenType::NonFungible, String::from("hello-world-nft"))
                .unwrap();
            contract.process_transaction();

            // 2. Mint NFT
            contract.send_transaction(&user);
            contract.mint(&user, id, 1).unwrap();
            let nft_id = MultiTokenContract::pack_id(contract.nonce, 2).unwrap();
            contract.process_transaction();

            assert_eq!(contract.balance_of(&user, nft_id).unwrap(), 1);

            nft_id
        };

        contract.send_transaction(&user);
        contract
            .transfer_batch(
                &user,
                &user_2,
                &vec![first_id, second_id, third_id],
                &vec![5000, 10000, 1],
            )
            .unwrap();
        contract.process_transaction();

        assert_eq!(contract.balance_of(&user, first_id).unwrap(), 5000);
        assert_eq!(contract.balance_of(&user, second_id).unwrap(), 10000);
        assert_eq!(contract.balance_of(&user, third_id).unwrap(), 0);

        assert_eq!(contract.balance_of(&user_2, first_id).unwrap(), 5000);
        assert_eq!(contract.balance_of(&user_2, second_id).unwrap(), 10000);
        assert_eq!(contract.balance_of(&user_2, third_id).unwrap(), 1);
    }

    #[test]
    fn success_transfer_fungible() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");
        let user_2 = String::from("2");

        // 1. Create token
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::Fungible, String::from("hello-world-token"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint token
        contract.send_transaction(&user);
        contract.mint(&user, id, 10000).unwrap();
        contract.process_transaction();
        assert_eq!(contract.balance_of(&user, id).unwrap(), 10000);

        // 3. Transfer token
        contract.send_transaction(&user);
        contract.transfer(&user, &user_2, id, 5000).unwrap();
        contract.process_transaction();

        assert_eq!(contract.balance_of(&user_2, id).unwrap(), 5000);
        assert_eq!(contract.balance_of(&user, id).unwrap(), 5000);
    }

    #[test]
    fn success_transfer_non_fungible() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");
        let user_2 = String::from("2");

        // 1. Create NFT
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::NonFungible, String::from("hello-world-nft"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint NFT
        contract.send_transaction(&user);
        contract.mint(&user, id, 1).unwrap();
        let nft_id = MultiTokenContract::pack_id(contract.nonce, 2).unwrap();
        contract.process_transaction();
        assert_eq!(contract.balance_of(&user, nft_id).unwrap(), 1);

        // 3. Transfer NFT
        contract.send_transaction(&user);
        contract.transfer(&user, &user_2, nft_id, 1).unwrap();
        contract.process_transaction();

        assert_eq!(contract.balance_of(&user_2, nft_id).unwrap(), 1);
        assert_eq!(contract.balance_of(&user, nft_id).unwrap(), 0);
    }

    #[test]
    fn success_set_approve_fungible() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");
        let user_2 = String::from("2");

        // 1. Create token
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::Fungible, String::from("hello-world-token"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint token
        contract.send_transaction(&user);
        contract.mint(&user, id, 10000).unwrap();
        contract.process_transaction();
        assert_eq!(contract.balance_of(&user, id).unwrap(), 10000);

        // 3. Approve token
        contract.send_transaction(&user);
        contract.set_approve(&user_2, true).unwrap();
        contract.process_transaction();

        // 4. Transfer token
        contract.send_transaction(&user_2);
        contract.transfer(&user, &user_2, id, 5000).unwrap();
        contract.process_transaction();

        assert_eq!(contract.balance_of(&user_2, id).unwrap(), 5000);
        assert_eq!(contract.balance_of(&user, id).unwrap(), 5000);
    }

    #[test]
    fn success_set_approve_non_fungible() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");
        let user_2 = String::from("2");

        // 1. Create NFT
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::NonFungible, String::from("hello-world-nft"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint NFT
        contract.send_transaction(&user);
        contract.mint(&user, id, 1).unwrap();
        let nft_id = MultiTokenContract::pack_id(contract.nonce, 2).unwrap();
        contract.process_transaction();
        assert_eq!(contract.balance_of(&user, nft_id).unwrap(), 1);

        // 3. Approve NFT
        contract.send_transaction(&user);
        contract.set_approve(&user_2, true).unwrap();
        contract.process_transaction();

        // 4. Transfer NFT
        contract.send_transaction(&user_2);
        contract.transfer(&user, &user_2, nft_id, 1).unwrap();
        contract.process_transaction();

        assert_eq!(contract.balance_of(&user_2, nft_id).unwrap(), 1);
        assert_eq!(contract.balance_of(&user, nft_id).unwrap(), 0);
    }

    #[test]
    fn fail_transfer_invalid_signer() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");
        let user_2 = String::from("2");

        // 1. Create token
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::Fungible, String::from("hello-world-token"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint token
        contract.send_transaction(&user);
        contract.mint(&user, id, 10000).unwrap();
        contract.process_transaction();
        assert_eq!(contract.balance_of(&user, id).unwrap(), 10000);

        // 3. Transfer token
        contract.send_transaction(&user_2);
        let error = contract.transfer(&user, &user_2, id, 5000).unwrap_err();
        contract.process_transaction();

        assert_eq!(error, Error::InvalidSigner);
    }

    #[test]
    fn fail_transfer_token_not_found() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");
        let user_2 = String::from("2");

        // 1. Create token
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::Fungible, String::from("hello-world-token"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint token
        contract.send_transaction(&user);
        contract.mint(&user, id, 10000).unwrap();
        contract.process_transaction();
        assert_eq!(contract.balance_of(&user, id).unwrap(), 10000);

        // 3. Transfer token
        contract.send_transaction(&user);
        let error = contract.transfer(&user, &user_2, 1337, 5000).unwrap_err();
        contract.process_transaction();

        assert_eq!(error, Error::TokenNotFound);
    }

    #[test]
    fn fail_transfer_insufficient_funds() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");
        let user_2 = String::from("2");

        // 1. Create token
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::Fungible, String::from("hello-world-token"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint token
        contract.send_transaction(&user);
        contract.mint(&user, id, 10000).unwrap();
        contract.process_transaction();
        assert_eq!(contract.balance_of(&user, id).unwrap(), 10000);

        // 3. Transfer token
        contract.send_transaction(&user);
        let error = contract.transfer(&user, &user_2, id, 5000000).unwrap_err();
        contract.process_transaction();

        assert_eq!(error, Error::InsufficientFunds);
    }

    #[test]
    fn fail_mint_token_not_found() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");

        // 1. Create token
        contract.send_transaction(&user);
        let _id = contract
            .create_token(TokenType::Fungible, String::from("hello-world-token"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint token
        contract.send_transaction(&user);
        let error = contract.mint(&user, 1337, 10000).unwrap_err();
        contract.process_transaction();

        assert_eq!(error, Error::TokenNotFound);
    }

    #[test]
    fn fail_mint_invalid_signer() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");
        let fake_user = String::from("1337");

        // 1. Create token
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::Fungible, String::from("hello-world-token"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint token
        contract.send_transaction(&fake_user);
        let error = contract.mint(&user, id, 10000).unwrap_err();
        contract.process_transaction();

        assert_eq!(error, Error::InvalidSigner);
    }

    #[test]
    fn fail_mint_exceed_max_supply() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");

        // 1. Create NFT
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::NonFungible, String::from("hello-world-token"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint NFT
        contract.send_transaction(&user);
        contract.mint(&user, id, 10000).unwrap();
        contract.process_transaction();

        let nft_id = MultiTokenContract::pack_id(contract.nonce, 2).unwrap();
        assert_eq!(contract.balance_of(&user, nft_id).unwrap(), 1);

        // 3. Mint NFT
        contract.send_transaction(&user);
        let error = contract.mint(&user, nft_id, 10000).unwrap_err();
        contract.process_transaction();

        assert_eq!(error, Error::ExceededMaxSupply);
    }

    #[test]
    fn fail_burn_math_overflow() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");

        // 1. Create token
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::Fungible, String::from("hello-world-token"))
            .unwrap();
        contract.process_transaction();

        // 2. Mint token
        contract.send_transaction(&user);
        contract.mint(&user, id, 10000).unwrap();
        contract.process_transaction();
        assert_eq!(contract.balance_of(&user, id).unwrap(), 10000);

        // 3. Burn token
        contract.send_transaction(&user);
        let error = contract.burn(&user, id, Some(10001)).unwrap_err();
        contract.process_transaction();

        assert_eq!(error, Error::MathOverflow);
    }

    #[test]
    fn fail_burn_insufficient_funds() {
        let mut contract = MultiTokenContract::default();
        let user = String::from("1");

        // 1. Create token
        contract.send_transaction(&user);
        let id = contract
            .create_token(TokenType::Fungible, String::from("hello-world-token"))
            .unwrap();
        contract.process_transaction();

        // 2. Burn token
        contract.send_transaction(&user);
        let error = contract.burn(&user, id, Some(1337)).unwrap_err();
        contract.process_transaction();

        assert_eq!(error, Error::InsufficientFunds);
    }
}
