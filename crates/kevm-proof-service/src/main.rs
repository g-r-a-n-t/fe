use fe_proof_service::{invariant::Invariant, serde_json};
use std::{
    io::{BufRead, BufReader, BufWriter},
    net::{TcpListener, TcpStream},
};

use server_impl::Server;

mod server_impl;

fn main() {
    let listener = TcpListener::bind("127.0.0.1:7878").unwrap();
    let mut server = Server::new("db.yaml");

    server.display();

    for stream in listener.incoming() {
        let stream = stream.unwrap();
        connection_handler(&mut server, stream);
    }
}

fn connection_handler(server: &mut Server, mut stream: TcpStream) {
    let mut stream_clone = stream.try_clone().unwrap();

    let mut reader = BufReader::new(&mut stream);
    let mut writer = BufWriter::new(&mut stream_clone);

    let invariant: Invariant = {
        let mut invariant_encoded = String::new();
        reader.read_line(&mut invariant_encoded).unwrap();
        serde_json::from_str(&invariant_encoded).expect("unable to decode invariant")
    };

    let status = server.check_invariant(invariant);
    serde_json::to_writer(&mut writer, &status).expect("unable to encode invariant status");
}
