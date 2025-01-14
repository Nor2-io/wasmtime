//! Implements the host state for the `wasi-nn` API: [WasiNnCtx].

use crate::backend::{Backend, BackendError, BackendKind};
use crate::wit::types::GraphEncoding;
use crate::{ExecutionContext, Graph, GraphRegistry, InMemoryRegistry};
use anyhow::anyhow;
use std::{collections::HashMap, hash::Hash, path::Path};
use thiserror::Error;
use wiggle::GuestError;

type Backends = HashMap<BackendKind, Box<dyn Backend>>;
type Registry = Box<dyn GraphRegistry>;
type GraphId = u32;
type GraphExecutionContextId = u32;
type BackendName = String;
type GraphDirectory = String;

/// Construct an in-memory registry from the available backends and a list of
/// `(<backend name>, <graph directory>)`. This assumes graphs can be loaded
/// from a local directory, which is a safe assumption currently for the current
/// model types.
pub fn preload(
    preload_graphs: &[(BackendName, GraphDirectory)],
) -> anyhow::Result<(Backends, Registry)> {
    let mut backends: HashMap<_, _> = crate::backend::list().into_iter().collect();
    let mut registry = InMemoryRegistry::new();
    for (kind, path) in preload_graphs {
        let backend = backends
            .get_mut(&kind.parse()?)
            .ok_or(anyhow!("unsupported backend: {}", kind))?
            .as_dir_loadable()
            .ok_or(anyhow!("{} does not support directory loading", kind))?;
        registry.load(backend, Path::new(path))?;
    }
    Ok((backends, Box::new(registry)))
}

/// Capture the state necessary for calling into the backend ML libraries.
pub struct WasiNnCtx {
    pub(crate) backends: Backends,
    pub(crate) registry: Registry,
    pub(crate) graphs: Table<GraphId, Graph>,
    pub(crate) executions: Table<GraphExecutionContextId, ExecutionContext>,
}

impl WasiNnCtx {
    /// Make a new context from the default state.
    pub fn new(backends: Backends, registry: Registry) -> Self {
        Self {
            backends,
            registry,
            graphs: Table::default(),
            executions: Table::default(),
        }
    }
}

/// Possible errors while interacting with [WasiNnCtx].
#[derive(Debug, Error)]
pub enum WasiNnError {
    #[error("backend error")]
    BackendError(#[from] BackendError),
    #[error("guest error")]
    GuestError(#[from] GuestError),
    #[error("usage error")]
    UsageError(#[from] UsageError),
}

#[derive(Debug, Error)]
pub enum UsageError {
    #[error("Invalid context; has the load function been called?")]
    InvalidContext,
    #[error("Only OpenVINO's IR is currently supported, passed encoding: {0:?}")]
    InvalidEncoding(GraphEncoding),
    #[error("OpenVINO expects only two buffers (i.e. [ir, weights]), passed: {0}")]
    InvalidNumberOfBuilders(u32),
    #[error("Invalid graph handle; has it been loaded?")]
    InvalidGraphHandle,
    #[error("Invalid execution context handle; has it been initialized?")]
    InvalidExecutionContextHandle,
    #[error("Not enough memory to copy tensor data of size: {0}")]
    NotEnoughMemory(u32),
    #[error("No graph found with name: {0}")]
    NotFound(String),
}

pub(crate) type WasiNnResult<T> = std::result::Result<T, WasiNnError>;

/// Record handle entries in a table.
pub struct Table<K, V> {
    entries: HashMap<K, V>,
    next_key: u32,
}

impl<K, V> Default for Table<K, V> {
    fn default() -> Self {
        Self {
            entries: HashMap::new(),
            next_key: 0,
        }
    }
}

impl<K, V> Table<K, V>
where
    K: Eq + Hash + From<u32> + Copy,
{
    pub fn insert(&mut self, value: V) -> K {
        let key = self.use_next_key();
        self.entries.insert(key, value);
        key
    }

    pub fn get(&self, key: K) -> Option<&V> {
        self.entries.get(&key)
    }

    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.entries.get_mut(&key)
    }

    fn use_next_key(&mut self) -> K {
        let current = self.next_key;
        self.next_key += 1;
        K::from(current)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn example() {
        struct FakeRegistry;
        impl GraphRegistry for FakeRegistry {
            fn get_mut(&mut self, _: &str) -> Option<&mut Graph> {
                None
            }
        }

        let ctx = WasiNnCtx::new(HashMap::new(), Box::new(FakeRegistry));
    }
}
