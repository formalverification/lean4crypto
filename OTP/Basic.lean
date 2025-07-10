import Mathlib.Data.Vector.Basic

/-! # Types for the One-time Pad  -/

def Plaintext  (n : Nat) := List.Vector Bool n
def Key        (n : Nat) := List.Vector Bool n
def Ciphertext (n : Nat) := List.Vector Bool n

/-! ## Boolean xor -/
def XOR (a b : Bool) : Bool := match a, b with
  | true, true   => false
  | true, false  => true
  | false, true  => true
  | false, false => false


-- This is actually a build-in function in Lean, called `Bool.xor`,
-- but we define it here for clarity.

#eval XOR true false -- Output: true  (our version)
#eval xor true false -- Output: true  (the build-in version)

/-! ## xor is associative -/
#check Bool.xor_assoc -- xor (xor a b) c = xor a (xor b c)
#check Bool.xor_comm

-- So (Bool, xor) is a commutative monoid, with identity `false`.

/-! ## Element-wise xor for List.Vector -/

def vec_xor {n : Nat} (v₁ v₂ : List.Vector Bool n) := List.Vector.map₂ xor v₁ v₂

-- N.B. If we define `vec_xor` using our own `XOR` function, then
-- lemmas about `xor` will not apply and `simp` won't be as powerful.

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


/-! ## Demo 2: XOR Properties -/
-- Some useful lemmas about Boolean xor

  -- Interactive proof that XOR is self-inverse
open Bool
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

lemma xor_aab_eq_b (a b : Bool) : xor a (xor a b) = b := by
  rw [← xor_assoc a a b] -- (a xor a) xor b
  rw [Bool.xor_self a]   -- false xor b
  rw [false_xor b]       -- b

-- Lemma: a xor b = c ↔ b = a xor c
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
