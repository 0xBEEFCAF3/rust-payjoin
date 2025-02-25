use serde::de::DeserializeOwned;
use serde::Serialize;

pub trait PersistableValue: Serialize + DeserializeOwned + Sized + Clone {}
/// Implemented types that should be persisted by the application.
pub trait Persister<V: PersistableValue> {
    type Token;
    type Error: std::error::Error + Send + Sync + 'static;

    fn save<K: Into<Vec<u8>>>(&mut self, key: K, value: V) -> Result<Self::Token, Self::Error>;
    fn load(&self, token: &Self::Token) -> Result<V, Self::Error>;
}

/// Noop implementation
#[derive(Debug, Clone)]
pub struct NoopPersister;

#[derive(Debug, Clone)]
pub struct NoopToken<V: PersistableValue>(V);

impl<V: PersistableValue> Persister<V> for NoopPersister {
    type Token = NoopToken<V>;
    type Error = std::convert::Infallible;

    fn save<K: Into<Vec<u8>>>(&mut self, _key: K, value: V) -> Result<Self::Token, Self::Error> {
        Ok(NoopToken(value))
    }

    fn load(&self, token: &Self::Token) -> Result<V, Self::Error> { Ok(token.0.clone()) }
}
