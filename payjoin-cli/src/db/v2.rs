use bitcoincore_rpc::jsonrpc::serde_json;
use payjoin::receive::v2::Receiver;
use payjoin::send::v2::Sender;
use payjoin::traits::Jsonable;
use sled::{IVec, Tree};
use url::Url;

use super::*;

impl Database {
    pub(crate) fn insert_recv_session(&self, session: Receiver) -> Result<()> {
        let recv_tree = self.0.open_tree("recv_sessions")?;
        let key = &session.id();
        let value = session.to_json().map_err(Error::Serialize)?;
        recv_tree.insert(key.as_slice(), IVec::from(value.as_str()))?;
        recv_tree.flush()?;
        Ok(())
    }

    pub(crate) fn get_recv_sessions(&self) -> Result<Vec<Receiver>> {
        let recv_tree = self.0.open_tree("recv_sessions")?;
        let mut sessions = Vec::new();
        for item in recv_tree.iter() {
            let (_, value) = item?;
            let value = std::str::from_utf8(&value).map_err(Error::Utf8)?;
            let session: Receiver = serde_json::from_str(value).map_err(Error::Deserialize)?;
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

    pub(crate) fn insert_send_session(&self, session: &mut Sender, pj_url: &Url) -> Result<()> {
        let send_tree: Tree = self.0.open_tree("send_sessions")?;
        let value = session.to_json().map_err(Error::Serialize)?;
        send_tree.insert(pj_url.to_string(), IVec::from(value.as_str()))?;
        send_tree.flush()?;
        Ok(())
    }

    pub(crate) fn get_send_sessions(&self) -> Result<Vec<Sender>> {
        let send_tree: Tree = self.0.open_tree("send_sessions")?;
        let mut sessions = Vec::new();
        for item in send_tree.iter() {
            let (_, value) = item?;
            let value = std::str::from_utf8(&value).map_err(Error::Utf8)?;
            let session: Sender = serde_json::from_str(value).map_err(Error::Deserialize)?;
            sessions.push(session);
        }
        Ok(sessions)
    }

    pub(crate) fn get_send_session(&self, pj_url: &Url) -> Result<Option<Sender>> {
        let send_tree = self.0.open_tree("send_sessions")?;
        if let Some(val) = send_tree.get(pj_url.to_string())? {
            let value = std::str::from_utf8(&val).map_err(Error::Utf8)?;
            let session: Sender = serde_json::from_str(value).map_err(Error::Deserialize)?;
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
