import Mathlib.Data.Vector.Basic

/-! # OTP.Basic.lean

This is the first file in a collection of Lean programs about the one-time pad (OTP) cryptographic scheme.
It defines the basic types and operations needed for OTP, including:

- Types for plaintext, key, and ciphertext
- Boolean xor operation
- Pointwise xor operation for boolean vectors
- Encrypt and decrypt operations
- Properties of xor and vector xor operations
- Demos of basic OTP operations and xor properties

Other files in the collection prove properties like key uniqueness and perfect secrecy.

Files in this series:

- OTP.Basic: Basic definitions and operations for OTP
- OTP.KeyUniqueness: Properties of keys in OTP
- OTP.Distributions: Probability distributions related to OTP
- OTP.PerfectSecrecy: Properties of perfect secrecy in OTP
- OTP.Examples: Concrete examples and demos of OTP operations and properties
- OTP.SimpleSecrecy: Simplified version of OTP.PerfectSecrecy where we assume
                     the message distribution is uniform.


-/

/-! # Types for the one-time pad (OTP) and properties of xor -/


/-! ## Types for the OTP -/

def Plaintext  (n : Nat) := List.Vector Bool n
def Key        (n : Nat) := List.Vector Bool n
def Ciphertext (n : Nat) := List.Vector Bool n


/-! ## Definition of Boolean xor
This is actually a build-in function in Lean, called `Bool.xor`,
but we define it here for clarity. -/

def XOR (a b : Bool) : Bool := match a, b with
  | true, true   => false
  | true, false  => true
  | false, true  => true
  | false, false => false

#eval XOR true false -- Output: true  (our version)
#eval xor true false -- Output: true  (the build-in version)

/-! ## xor is associative -/
#check Bool.xor_assoc -- xor (xor a b) c = xor a (xor b c)
#check Bool.xor_comm

-- So (Bool, xor) is a commutative monoid, with identity `false`.

/-! ## Definition of vec_xor operation: point-wise xor for boolean vectors -/

def vec_xor {n : Nat} (v₁ v₂ : List.Vector Bool n) := List.Vector.map₂ xor v₁ v₂

-- N.B. If we define `vec_xor` using our own `XOR` function, then
-- lemmas about `xor` will not apply and `simp` won't be as powerful.


/-! ## Definitions of encrypt and decrypt operations -/

def encrypt {n : Nat} (m : Plaintext n) (k : Key n) : Ciphertext n :=
  vec_xor m k

def decrypt {n : Nat} (c : Ciphertext n) (k : Key n) : Plaintext n :=
  vec_xor c k


/-! ## Demo 1: Basic OTP Operations -/
-- Create a 4-bit message.
def msg : Plaintext 4 := ⟨[true, false, true, true], rfl⟩
-- `rfl` is the unique constructor for the equality type

def key : Key 4 := ⟨[false, true, false, true], by rfl⟩

-- Encryption.
#eval encrypt msg key                -- Output: [true, true, true, false]

-- Decryption recovers the original message.
#eval decrypt (encrypt msg key) key  -- Output: [true, false, true, true]

-- Different keys give different ciphertexts.
def key2 : Key 4 := ⟨[true, true, false, false], by decide⟩

#eval encrypt msg key2               -- Output: [false, true, true, true]



/-! ## Demo 2: xor properties -/

open Bool

-- For fixed `a`, the operation `f := λ b => a xor b` is idempotent.
-- That is, `f (f b) = b`.
lemma xor_aab_eq_b (a b : Bool) : xor a (xor a b) = b := by
  rw [← xor_assoc a a b] -- (a xor a) xor b
  rw [Bool.xor_self a]   -- false xor b
  rw [false_xor b]       -- b

-- For fixed `b`, the operation `g := λ a => a xor b` is idempotent.
-- That is, `g (g a) = a`.
lemma xor_abb_eq_a (a b : Bool) : xor (xor a b) b = a := by
  -- Let's explore the proof interactively
  rw [xor_assoc]
  -- Goal: xor a (xor b b) = a
  rw [Bool.xor_self]
  -- Goal: xor a false = a
  rw [Bool.xor_false]
  -- Done!

-- Another way using simp
example (a b : Bool) : xor (xor a b) b = a := by simp

-- Lemma: `a xor b = c ↔ b = a xor c`
-- Proof sketch:
--   If `a xor b = c`, then applying `xor a` to both sides,
--   `a xor (a xor b) = a xor c`
--   `b = a xor c`

lemma xor_ab_eq_c_iff_b_eq_ac (a b c : Bool) : xor a b = c ↔ b = xor a c := by
  constructor -- Splits the goal into two implications (↔)

  -- → goal: `a xor b = c → b = a xor c`
  · intro a_xor_b_eq_c   -- Assume: `a xor b = c`
    -- Goal: `b = a xor c`
    rw [← a_xor_b_eq_c]  -- substitute `a xor b` for `c`
    -- Goal: `b = a xor (a xor b)`
    rw [xor_aab_eq_b]

  -- ← goal: `b = xor a c → xor a b = c`
  · intro h_b_eq_ac      -- Assume: `b = a xor c`
    -- Goal: `a xor b = c`
    rw [h_b_eq_ac]       -- substitute `a xor c` for `b`
    -- Goal: `a xor (xor a c) = c`
    rw [xor_aab_eq_b a c]
