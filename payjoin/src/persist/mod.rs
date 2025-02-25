use serde::de::DeserializeOwned;
use serde::Serialize;

/// Token returned by persistence operations that can be used to retrieve stored data
pub trait Token<P: Persister> {
    /// Load the data associated with this token
    fn load<T: DeserializeOwned>(&self, persister: &P) -> Result<T, P::Error>;
}

/// Implemented types that should be persisted by the application.
pub trait Persister: Sized {
    type Token: Token<Self>;
    type Error: std::error::Error + Send + Sync + 'static;
    type Key: Serialize;

    fn save<V: Serialize, K: Serialize>(
        &mut self,
        key: K,
        value: V,
    ) -> Result<Self::Token, Self::Error>;
    fn load<T: DeserializeOwned>(&self, token: &Self::Token) -> Result<T, Self::Error>;
}

/// Noop implementation
#[derive(Debug, Clone)]
pub struct NoopPersister;

#[derive(Debug, Clone)]
pub struct NoopToken(Vec<u8>);

impl Token<NoopPersister> for NoopToken {
    fn load<T: DeserializeOwned>(
        &self,
        _persister: &NoopPersister,
    ) -> Result<T, std::convert::Infallible> {
        Ok(serde_json::from_slice(&self.0).unwrap())
    }
}

impl Persister for NoopPersister {
    type Token = NoopToken;
    type Error = std::convert::Infallible;
    type Key = ();

    fn save<V: Serialize, K: Serialize>(
        &mut self,
        _key: K,
        value: V,
    ) -> Result<Self::Token, Self::Error> {
        let bytes = serde_json::to_vec(&value).unwrap();
        Ok(NoopToken(bytes))
    }

    fn load<T: DeserializeOwned>(&self, token: &Self::Token) -> Result<T, Self::Error> {
        token.load(self)
    }
}
