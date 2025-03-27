use serde::de::DeserializeOwned;
use serde::Serialize;

/// Implemented types that should be persisted by the application.
pub trait Persister: Sized {
    type Token: Into<Vec<u8>> + From<Vec<u8>>;
    type Error: std::error::Error + Send + Sync + 'static;

    fn save<V: Serialize, K: Into<Vec<u8>>>(
        &self,
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

impl From<Vec<u8>> for NoopToken {
    fn from(value: Vec<u8>) -> Self { Self(value) }
}

impl Into<Vec<u8>> for NoopToken {
    fn into(self) -> Vec<u8> { self.0 }
}

impl Persister for NoopPersister {
    type Token = NoopToken;
    type Error = std::convert::Infallible;

    fn save<V: Serialize, K: Into<Vec<u8>>>(
        &self,
        _key: K,
        value: V,
    ) -> Result<Self::Token, Self::Error> {
        let bytes = serde_json::to_vec(&value).unwrap();
        Ok(NoopToken(bytes))
    }
    fn load<T: DeserializeOwned>(&self, token: &Self::Token) -> Result<T, Self::Error> {
        Ok(serde_json::from_slice(&token.0).unwrap())
    }
}
