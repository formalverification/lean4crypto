import Mathlib.Data.Vector.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions -- for PMF.uniformOfFintype
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Probability.Distributions.Uniform -- for uniformOfFintype
import Mathlib.Data.Fintype.Vector -- Provides Fintype for List.Vector
import OTP.Basic -- definitions of Plaintext, Key, etc.
import OTP.Probability -- definitions of Plaintext, Key, etc.
-- OTP.Basic already imports Mathlib.Data.Vector.Basic (for Inhabited/Nonempty)

open OTP -- To use Key, Plaintext, etc. without OTP. prefix
open PMF -- To use uniformOfFintype without PMF. prefix

open List.Vector
open Fintype -- Add this to bring card into scope

-- Recall the definitions from OTP.Basic
-- def Plaintext  (n : Nat) := List.Vector Bool n
-- def Key        (n : Nat) := List.Vector Bool n
-- def Ciphertext (n : Nat) := List.Vector Bool n
-- def vec_xor {n : Nat} (v₁ v₂ : List.Vector Bool n) := map₂ xor v₁ v₂
-- def encrypt {n : Nat} (m : Plaintext n) (k : Key n) : Ciphertext n := vec_xor m k

----------------------------------------------------------------
-- Demo 1: Basic OTP Operations
section Demo1
  -- Create 4-bit message and key
  def msg : Plaintext 4 := ⟨[true, false, true, true], rfl⟩
  def key : Key 4 := ⟨[false, true, false, true], rfl⟩

  -- Show encryption
  #eval encrypt msg key                -- Output: [true, true, true, false]

  -- Show decryption recovers the message
  #eval decrypt (encrypt msg key) key  -- Output: [true, false, true, true]

  -- Show that different keys give different ciphertexts
  def key2 : Key 4 := ⟨[true, true, false, false], by decide⟩

  #eval encrypt msg key2               -- Output: [false, true, true, true]
end Demo1

----------------------------------------------------------------
-- Demo 2: xor properties
-- Some useful lemmas about Boolean xor

section Demo2
  open Bool
  -- Interactive proof that xor is self-inverse
  example (a b : Bool) : xor (xor a b) b = a := by
    -- Let's explore the proof interactively
    rw [xor_assoc]      -- New Goal: xor a (xor b b) = a
    rw [Bool.xor_self]  -- New Goal: xor a false = a
    rw [Bool.xor_false] -- Done!

  -- Another way using simp
  example (a b : Bool) : xor (xor a b) b = a := by simp
end Demo2

-------------------------------------------------------------------------
-- Demo 3: Bijection Property
/- First recall the `key_uniqueness` theorem we proved in OTP.Basic:
   `theorem key_uniqueness {n : Nat} (m : Plaintext n) (k : Key n)
     (c : Ciphertext n) : encrypt m k = c ↔ k = vec_xor m c`
-/
section Demo3
  -- For every ciphertext, there's a unique key.
  example {n : Nat} (m : Plaintext n) (c : Ciphertext n) :
    ∃! k : Key n, encrypt m k = c := by
    use vec_xor m c -- what we will use as our witness to existence
    constructor
    -- Existence: show encrypt m (vec_xor m c) = c
    · apply ext
      intro i
      unfold encrypt vec_xor
      repeat rw [get_map₂]
      simp
    · -- Uniqueness: show if encrypt m y = c, then y = vec_xor m c
      intro y hy
      -- key_uniqueness: vec_xor m y = c ↔ y = vec_xor m c
      apply (key_uniqueness m y c).mp hy
      -- mp is the "modus ponens" (forward direction) of the equivalence ↔
      -- mpr is the "reverse modus ponens" (backward direction) of the ↔
      -- so we could have written: `apply (key_uniqueness m y c).symm.mpr hy`

  -- Encryption with a fixed message is injective
  example {n : Nat} (m : Plaintext n) (k₁ k₂ : Key n)
    (h : encrypt m k₁ = encrypt m k₂) : k₁ = k₂ := by
    -- Goal: k₁ = k₂
    have h₁ : k₁ = vec_xor m (encrypt m k₁) := by
      unfold encrypt
      rw [(key_uniqueness m k₁ (vec_xor m k₁)).symm]
    have h₂ : k₂ = vec_xor m (encrypt m k₂) := by
      unfold encrypt
      rw [(key_uniqueness m k₂ (vec_xor m k₂)).symm]
    rw [h₁, h₂, h]

end Demo3
---------------------------------------------------------------------------


------------------------------------------------------------------------
-- Demo 4: Probability Calculations
-- The probability of any specific 3-bit key is 1/8
-- Lean knows that card (Key 3) = 2^3 = 8
section ProbabilityDemo
  example : (μK (n := 3)) ⟨[true, false, true], by decide⟩ = 1/8 := by
    simp [μK, uniformOfFintype_apply]
    -- New Goal: ↑(card (Key 3)) = 8
    unfold Key
    rw [card_vector]
    -- New Goal: ↑(card Bool ^ 3) = 8
    simp

  -- The conditional probability P(C = c | M = m) is also 1/8
  example (m : Plaintext 3) (c : Ciphertext 3) :
    (μC_M m) c = 1/8 := by
    rw [C_given_M_eq_inv_card_key]
    -- New Goal: 1 / ↑(card (Key 3)) = 1 / 8
    unfold Key
    rw [card_vector]
    -- New Goal: 1 / ↑(card Bool ^ 3) = 1 / 8
    simp
end ProbabilityDemo
--------------------------------------------------------------------


--------------------------------------------------------------------
-- Demo 5: Perfect Secrecy Visualization
-- For a 2-bit OTP, verify perfect secrecy manually.
-- Message: [true, false]
-- Key space: {[false,false], [false,true], [true,false], [true,true]}

section PerfectSecrecyDemo
  def msg_10 : Plaintext 2 := ⟨[true, false], by decide⟩

  -- Each key gives a different ciphertext:
  #eval encrypt msg_10 ⟨[false, false], by decide⟩  -- [true, false]
  #eval encrypt msg_10 ⟨[false, true], by decide⟩   -- [true, true]
  #eval encrypt msg_10 ⟨[true, false], by decide⟩   -- [false, false]
  #eval encrypt msg_10 ⟨[true, true], by decide⟩    -- [false, true]

-- Critical observation:
-- Each of the 4 possible 2-bit ciphertexts appears exactly once.
-- This uniform mapping is the essence of perfect secrecy!
end PerfectSecrecyDemo
---------------------------------------------------------------------

---------------------------------------------------------------
-- Demo 6: Common Pitfall - Key Reuse
-- Why can't we reuse a one-time pad key?

section KeyReuseDemo

  def msg1 : Plaintext 4 := ⟨[true, false, true, false], by decide⟩
  def msg2 : Plaintext 4 := ⟨[false, true, false, true], by decide⟩
  def shared_key : Key 4 := ⟨[true, true, false, false], by decide⟩

  def c1 := encrypt msg1 shared_key
  def c2 := encrypt msg2 shared_key

  -- If an attacker gets both ciphertexts, they can XOR them:
  #eval vec_xor c1 c2
  -- This equals vec_xor msg1 msg2 - the key cancels out!
  #eval vec_xor msg1 msg2

  -- Lesson: NEVER reuse a one-time pad key!
  -- If we xor two ciphertexts encrypted with the same key, the
  -- key cancels out, leaving $m_1 ⊕ m_2$.
  -- This leaks information about the messages!
end KeyReuseDemo
-------------------------------------------------------------------------
