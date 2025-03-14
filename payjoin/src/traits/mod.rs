pub trait Jsonable: Sized {
    fn to_json(&self) -> Result<String, serde_json::Error>;
    fn from_json(json: &str) -> Result<Self, serde_json::Error>;
}
