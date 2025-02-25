use serde::Serialize;

/// Implemented types that should be persisted by the application.
pub trait Persister: Sized {
    type Key;
    type Error: std::error::Error + Send + Sync + 'static;
    fn save<T: Serialize>(&self, key: Self::Key, value: T) -> Result<(), Self::Error>;
}
