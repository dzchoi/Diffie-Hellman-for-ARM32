## *Diffie-Hellman* key exchange algorithm implemented in C and ARM32 assembly

- The *Diffie-Hellman* key exchange algorithm (and the RSA algorithm as well) has at their core the most time-consuming operation:  
>  C = M<sup>e</sup>
  (where M is a message to encrypt and e is the key used in the encryption)

- As we need to compute the power of a big number M to a big number e, we cannot do the computation in a single step due to the limited size of registers in most CPUs.

- I implemented the *Diffie-Hellman* key exchange algorithm first in C, based on the paper *"A Cryptographic Library for the Motorola DSP56000"* (<http://link.springer.com/chapter/10.1007/3-540-46877-3_21>). Then I have found out, through profiling, the above computation takes more than 90% of the total running time, and so reimplemented the code corresponding to the compuatation in assembly language.
