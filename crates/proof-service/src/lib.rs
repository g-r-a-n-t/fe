use serde::{Deserialize, Serialize};
use std::fmt::Display;
use std::io::{BufReader, BufWriter, Write};
use std::net::{SocketAddr, TcpStream, ToSocketAddrs};
use symbolic_test::SymbolicTest;

pub use serde_json;

pub mod symbolic_test;

pub struct ProofClient(SocketAddr);

#[derive(PartialEq, Eq, Serialize, Deserialize, Clone, Copy, Debug)]
pub enum ProofStatus {
    New,
    Ready,
    Proving,
    Complete,
    Incomplete,
}

impl Display for &ProofStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofStatus::New => write!(f, "New"),
            ProofStatus::Ready => write!(f, "Queued"),
            ProofStatus::Proving => write!(f, "Proving"),
            ProofStatus::Complete => write!(f, "Complete"),
            ProofStatus::Incomplete => write!(f, "Incomplete"),
        }
    }
}

impl ProofClient {
    pub fn new<A>(addr: A) -> Self
    where
        A: ToSocketAddrs,
    {
        Self(addr.to_socket_addrs().unwrap().into_iter().last().unwrap())
    }
}

impl ProofClient {
    pub fn prove_symbolic_test(&self, test: SymbolicTest, rerun: bool) -> ProofStatus {
        let mut stream = TcpStream::connect(self.0).expect("connection failed");
        let mut stream_clone = stream.try_clone().unwrap();

        let mut reader = BufReader::new(&mut stream);
        let mut writer = BufWriter::new(&mut stream_clone);

        let encoded_invariant = serde_json::to_string(&test).unwrap();
        writer.write(encoded_invariant.as_bytes()).unwrap();
        writer.write("\n".as_bytes()).unwrap();
        writer.flush().unwrap();

        let encoded_rerun = serde_json::to_string(&rerun).unwrap();
        writer.write(encoded_rerun.as_bytes()).unwrap();
        writer.write("\n".as_bytes()).unwrap();
        writer.flush().unwrap();

        let status = serde_json::from_reader(&mut reader).unwrap();
        status
    }
}
