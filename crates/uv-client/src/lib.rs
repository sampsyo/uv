pub use base_client::{BaseClient, BaseClientBuilder, LazyBaseClientBuilder};
pub use cached_client::{CacheControl, CachedClient, CachedClientError, DataWithCachePolicy};
pub use error::{BetterReqwestError, Error, ErrorKind};
pub use flat_index::{FlatDistributions, FlatIndex, FlatIndexClient, FlatIndexError};
pub use registry_client::{
    Connectivity, RegistryClient, RegistryClientBuilder, SimpleMetadata, SimpleMetadatum,
    VersionFiles,
};
pub use rkyvutil::OwnedArchive;

mod base_client;
mod cached_client;
mod error;
mod flat_index;
mod html;
mod httpcache;
mod middleware;
mod registry_client;
mod remote_metadata;
mod rkyvutil;
mod tls;
