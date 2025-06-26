import Mathlib.Data.Vector.Basic

namespace OTP
  open List.Vector
  -- Define types using List.Vector
  def Plaintext  (n : Nat) := List.Vector Bool n
  def Key        (n : Nat) := List.Vector Bool n
  def Ciphertext (n : Nat) := List.Vector Bool n

  -- Element-wise XOR for List.Vector
  def vec_xor {n : Nat} (v₁ v₂ : List.Vector Bool n) := map₂ xor v₁ v₂

  def encrypt {n : Nat} (m : Plaintext n) (k : Key n) : Ciphertext n :=
    vec_xor m k

  def decrypt {n : Nat} (c : Ciphertext n) (k : Key n) : Plaintext n :=
    vec_xor c k


-- Demo 1: Basic OTP Operations ----------------------------------
-- Examples using List literals for the List.Vector constructor
section Demo
  -- Create a 4-bit message
  def msg : Plaintext 4 := ⟨[true, false, true, true], rfl⟩
  -- `rfl` is the unique constructor for the equality type

  def key : Key 4 := ⟨[false, true, false, true], by rfl⟩

  -- Show encryption
  #eval encrypt msg key
  -- Output: [true, true, true, false]

  -- Show decryption recovers the message
  #eval decrypt (encrypt msg key) key
  -- Output: [true, false, true, true]

  -- Show that different keys give different ciphertexts
  def key2 : Key 4 := ⟨[true, true, false, false], by decide⟩
  #eval encrypt msg key2
  -- Output: [false, true, true, true]

end Demo
-----------------------------------------------------------------

end OTP
