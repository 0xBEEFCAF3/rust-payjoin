use std::sync::Arc;

use bitcoincore_rpc::jsonrpc::serde_json;
use payjoin::directory::ShortId;
use payjoin::persist::Persister;
use payjoin::receive::v2::Receiver;
use payjoin::send::v2::Sender;
use sled::{IVec, Tree};
use url::Url;

use super::*;

#[derive(Clone)]
pub(crate) struct SenderPersister(pub Arc<Database>);
impl Persister<Sender> for SenderPersister {
    type Error = crate::db::error::Error;
    type Token = ShortId;
    fn save<K: Into<Vec<u8>>>(
        &self,
        key: K,
        value: Sender,
    ) -> std::result::Result<Self::Token, Self::Error> {
        let send_tree = self.0 .0.open_tree("send_sessions")?;
        let value = serde_json::to_string(&value).map_err(Error::Serialize)?;
        let key_bytes: Vec<u8> = key.into();
        send_tree.insert(key_bytes.as_slice(), IVec::from(value.as_str()))?;
        send_tree.flush()?;

        Ok(ShortId::from(key_bytes))
    }

    fn load(
        &self,
        token: &Self::Token,
    ) -> std::result::Result<Sender, Self::Error> {
        let send_tree = self.0 .0.open_tree("send_sessions")?;
        let value = send_tree.get(token.as_bytes())?.ok_or(Error::NotFound(token.to_string()))?;
        let x = String::from_utf8(value.to_vec()).unwrap();
        println!(">>>>> x: {}", x);
        serde_json::from_str(&x).map_err(Error::Deserialize)
    }
}

#[derive(Clone)]
pub(crate) struct RecieverPersister(pub Arc<Database>);
impl Persister<Receiver> for RecieverPersister {
    type Error = crate::db::error::Error;
    type Token = ShortId;
    fn save<K: Into<Vec<u8>>>(
        &self,
        key: K,
        value: Receiver,
    ) -> std::result::Result<Self::Token, Self::Error> {
        let recv_tree = self.0 .0.open_tree("recv_sessions")?;
        let value = serde_json::to_string(&value).map_err(Error::Serialize)?;
        let key_bytes: Vec<u8> = key.into();
        recv_tree.insert(key_bytes.as_slice(), IVec::from(value.as_str()))?;
        recv_tree.flush()?;

        Ok(ShortId::from(key_bytes))
    }

    fn load(
        &self,
        token: &Self::Token,
    ) -> std::result::Result<Receiver, Self::Error> {
        let recv_tree = self.0 .0.open_tree("recv_sessions")?;
        let value = recv_tree.get(token.as_bytes())?.ok_or(Error::NotFound(token.to_string()))?;
        let x = String::from_utf8(value.to_vec()).unwrap();
        serde_json::from_str(&x).map_err(Error::Deserialize)
    }
}

impl Database {
    pub(crate) fn get_recv_sessions(&self) -> Result<Vec<Receiver>> {
        let recv_tree = self.0.open_tree("recv_sessions")?;
        let mut sessions = Vec::new();
        for item in recv_tree.iter() {
            let (key, value) = item?;
            let x = String::from_utf8(value.to_vec()).unwrap();
            let session: Receiver = serde_json::from_str(&x).map_err(Error::Deserialize)?;
            sessions.push(session);
        }
        Ok(sessions)
    }

    pub(crate) fn clear_recv_session(&self) -> Result<()> {
        let recv_tree: Tree = self.0.open_tree("recv_sessions")?;
        recv_tree.clear()?;
        recv_tree.flush()?;
        Ok(())
    }

    pub(crate) fn get_send_sessions(&self) -> Result<Vec<Sender>> {
        let send_tree: Tree = self.0.open_tree("send_sessions")?;
        let mut sessions = Vec::new();
        for item in send_tree.iter() {
            let (_, value) = item?;
            let x = String::from_utf8(value.to_vec()).unwrap();
            println!(">>>>> y: {}", x);
            let session: Sender = serde_json::from_str(&x).map_err(Error::Deserialize)?;
            sessions.push(session);
        }
        Ok(sessions)
    }

    pub(crate) fn get_send_session(&self, pj_url: &Url) -> Result<Option<Sender>> {
        let send_tree = self.0.open_tree("send_sessions")?;
        if let Some(val) = send_tree.get(pj_url.to_string())? {
            let session: Sender = serde_json::from_slice(&val).map_err(Error::Deserialize)?;
            Ok(Some(session))
        } else {
            Ok(None)
        }
    }

    pub(crate) fn clear_send_session(&self, pj_url: &Url) -> Result<()> {
        let send_tree: Tree = self.0.open_tree("send_sessions")?;
        send_tree.remove(pj_url.to_string())?;
        send_tree.flush()?;
        Ok(())
    }
}
