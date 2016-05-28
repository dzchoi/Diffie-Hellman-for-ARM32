# Diffie-Hellman-for-ARM32
Implementation of Diffie-Hellman in C and ARM32 assembly

- A Diffie-Hellman algorithm is based on RSA encryption algorithm and computes a big number by exponentiating a big number to another big number, while both numbers usually span 4096 bits in size.  
- The open source code written in C did not perform well in speed. So, I implemented my own code in C based on the paper about the Diffie-Hellman algorithm, profiled every function and every loop in my source code, and changed the most CPU-hogging parts/sections of the code by rewriting them in assembly language.  
