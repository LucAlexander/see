from typing import List
import time

def pipe(s: str) -> None:
    with open('./world.q', 'w') as infile:
        infile.write(s+"\n")

def scan(target: int) -> None:
    pipe(f"{target} scan")

def lookup(service: int) -> None:
    pipe(f"{service} lookup")

def call(machine: int, service: int, name: str, args: List = []) -> str:
    if len(args) > 0:
        pipe(f"{machine} call {service} {name} " + ' '.join(args))
    else:
        pipe(f"{machine} call {service} {name}")
    ret = ""
    time.sleep(1)
    with open("./client.q") as infile:
        ret = infile.read()
    with open("./client.q", 'w') as infile:
        infile.write('\n')
    return ret
