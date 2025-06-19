-- 1. Mathlib Imports for Probability
import Mathlib.Probability.Distributions.Uniform -- for uniformOfFintype
import OTP.Basic -- definitions of Plaintext, Key, etc.
-- OTP.Basic already imports Mathlib.Data.Vector.Basic (for Inhabited/Nonempty)
-- import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions -- for PMF.uniformOfFintype
-- import Mathlib.Data.Vector.Basic
-- import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
-- import Mathlib.Data.Fintype.Vector -- Provides Fintype for List.Vector

open OTP -- To use Key, Plaintext, etc. without OTP. prefix
open List.Vector
-- 2. Ensure Fintype and Nonempty instances are available for:
--    Ciphertext n, Key n (needed for uniformOfFintype, etc.)
instance ciphertext_fintype {n : ℕ} : Fintype (Ciphertext n) := by
  unfold Ciphertext; exact inferInstance
instance ciphertext_nonempty {n : ℕ} : Nonempty (Ciphertext n) := by
  unfold Ciphertext; exact inferInstance
instance key_fintype {n : ℕ} : Fintype (Key n) := by
  unfold Key; exact inferInstance
instance key_nonempty {n : ℕ} : Nonempty (Key n) := by
  unfold Key; exact inferInstance
instance plaintext_fintype {n : ℕ} : Fintype (Plaintext n) := by
  unfold Plaintext; exact inferInstance
instance plaintext_nonempty {n : ℕ} : Nonempty (Plaintext n) := by
  unfold Plaintext; exact inferInstance

-- 3. Define Uniform Key Probability Mass Function
-- This defines a uniform PMF over the keys of length n.
noncomputable def μK {n : ℕ} : PMF (Key n) := PMF.uniformOfFintype (Key n)
-- `PMF.uniformOfFintype` is noncomputable because it involves division to
-- compute probabilities (which are `NNReal`, non-negative reals)---operations
-- that are not computable in Lean's constructive framework.

/-!
### Part 1: A Concrete First Proof
-/

-- To make our example concrete, we'll define Key n as vectors of booleans.
-- abbrev Key (n : ℕ) := Vector Bool n

-- Our theorem: The probability of the key [true, false, true] is 1/8.
example : μK ⟨[true, false, true], rfl⟩ = (1/8 : ENNReal) := by
    simp [μK, PMF.uniformOfFintype_apply]; rfl


/-!
### Part 2: Deconstructing `bind` and `pure`
-/

-- For our example, Plaintexts are also n-bit vectors.
-- abbrev Plaintext (n : ℕ) := Vector Bool n
-- abbrev Ciphertext (n : ℕ) := Vector Bool n

-- A simple toy encryption function: pointwise XOR.
-- def encrypt (m : Plaintext n) (k : Key n) : Ciphertext n := List.Vector.map₂ Bool.xor m k

-- Assume a uniform distribution on messages for this example.
noncomputable def μM {n : ℕ} : PMF (Plaintext n) := PMF.uniformOfFintype (Plaintext n)

-- The joint distribution assumes independence of message and key.
noncomputable def μMK {n : ℕ} : PMF (Plaintext n × Key n) :=
  PMF.map (λ p => (p.1, p.2)) (PMF.bind μM (λ m => PMF.map (λ k => (m, k)) μK))

-- The ciphertext distribution, built with bind and pure.
noncomputable def μC {n : ℕ} : PMF (Ciphertext n) :=
  PMF.bind μMK (λ ⟨m , k⟩ => PMF.pure (encrypt m k))


-- Theorem: The probability of a ciphertext `c` is the sum of probabilities
-- of all (message, key) pairs that produce `c`.
open Classical
theorem μC_apply_eq_sum {n : ℕ} (c : Ciphertext n) :
  μC c = ∑' mk : Plaintext n × Key n, if encrypt mk.1 mk.2 = c then μMK mk else 0
  := by
  rw [μC, PMF.bind_apply]
  simp only [PMF.pure_apply, mul_boole]
  -- The `mul_boole` simplifies the multiplication with the indicator function.
  -- It turns the `if` into a multiplication by `1` or `0`,
  -- which is what we want for the sum.
  -- Convert the equality direction in the sum
  simp only [eq_comm]

/-!
### Part 3: Proving a Cryptographic Property (One-Time Pad)
-/

-- The distribution of ciphertexts, conditioned on a fixed message `m`.
noncomputable def μC_M {n : ℕ} (m : Plaintext n) : PMF (Ciphertext n) :=
  PMF.map (encrypt m) μK

-- Helper lemma: For a fixed message m, encryption is a bijection from keys to ciphertexts.
lemma encrypt_involutive {n : ℕ} (m : Plaintext n) :
  Function.Involutive (encrypt m) := by
  -- This is true because XORing with a constant is its own inverse.
  -- The proof is to show that applying the function twice gets you back to the start.
    -- We need to show `encrypt m (encrypt m k) = k`
  intro k
  -- apply OTP.encrypt_m_involutive -- (finishes the proof)
  -- Unfold the definition of `encrypt`
  unfold encrypt vec_xor
  -- Use extensionality to change the goal from vector equality to element-wise equality.
  apply ext
  intro i
  -- The goal is now to show `((m xor k) xor m) i = k i`
  -- This is exactly `xor (get m i) (xor (get k i) (get m i)) = get k i`
  -- which holds by the definition of `vec_xor`.
  simp only [get_map₂]
  -- The goal is now `xor (get m i) (get k i) = get k i`
  -- This holds because `xor` is self-inverse.
  simp [xor_self, xor_false]

-- Helper lemma: For a fixed message m, encryption is a bijection from keys to ciphertexts.
lemma encrypt_bijective {n : ℕ} (m : Plaintext n) : Function.Bijective (encrypt m) :=
  -- This is true because XORing with a constant is its own inverse.
  -- The proof is to show that applying the function twice gets you back to the start.
  Function.Involutive.bijective (λ k => encrypt_involutive m k)

-- We can build an Equiv (a bijection with its inverse) from the involutive property.
#check PMF.map_ofFintype

noncomputable def encrypt_equiv {n : ℕ} (m : Plaintext n) : Key n ≃ Ciphertext n :=
  Equiv.ofBijective (encrypt m) (encrypt_bijective m)


/--  For a fixed message `m`, “xor with `m`” is a bijection on Boolean vectors. -/
def xorEquiv {n : ℕ} (m : Plaintext n) : Key n ≃ Ciphertext n where
  toFun   := encrypt m  -- := λ k => encrypt m k
  invFun  := vec_xor m  -- := λ c => vec_xor m c
  left_inv := by
    intro k
    unfold encrypt
    rw [key_uniqueness m (vec_xor m k)]

  right_inv := by
    intro c
    unfold encrypt
    rw [key_uniqueness m (vec_xor m c)]


open Fintype

/-! ### 2.  Mapping a uniform PMF through a bijection stays uniform -------------/
lemma map_uniformOfFintype_equiv
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) :
    PMF.map e (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := by
  -- Prove equality of PMFs by showing they assign the same probability to each element
  ext b
  -- Goal: (PMF.map e (uniformOfFintype α)) b = (uniformOfFintype β) b

  -- Step 1: Simplify the LHS using PMF.map_apply
  rw [PMF.map_apply]
  -- This gives us: ∑' (a : α), if b = e a then (uniformOfFintype α) a else 0

  -- Step 2: Simplify the uniform distribution on α
  simp only [PMF.uniformOfFintype_apply]
  -- Goal: ∑' (a : α), if b = e a then (↑(card α))⁻¹ else 0 = (↑(card β))⁻¹

  -- Step 3: The sum has exactly one non-zero term when a = e.symm b
  -- We can rewrite this as a sum over the singleton {e.symm b}
  have h_equiv : (∑' (a : α), if b = e a then (↑(card α : ENNReal))⁻¹ else 0) =
                 (∑' (a : α), if a = e.symm b then (↑(card α))⁻¹ else 0) := by
    congr 1
    ext a
    -- Show: (if b = e a then (↑(card α))⁻¹ else 0) = (if a = e.symm b then (↑(card α))⁻¹ else 0)
    by_cases h : b = e a
    · -- Case: b = e a
      rw [if_pos h, if_pos]
      -- Need to show a = e.symm b
      rw [←Equiv.symm_apply_apply e a]
      rw [h]
    · -- Case: b ≠ e a
      rw [if_neg h, if_neg]
      -- Need to show a ≠ e.symm b
      intro contra
      subst contra
      rw [Equiv.apply_symm_apply e] at h
      apply h
      rfl

  -- Step 4: Apply the equivalence and simplify
  rw [h_equiv]
  rw [tsum_ite_eq]
  -- Goal: (↑(card α))⁻¹ = (↑(card β))⁻¹

  -- Step 5: Use the fact that equivalent finite types have the same cardinality
  congr 1
  rw [card_congr e]


-- Theorem: For any message m, the distribution of ciphertexts is uniform.
-- This is a key lemma for proving the perfect secrecy of the one-time pad.
theorem otp_perfect_secrecy_lemma {n : ℕ} :
    ∀ (m : Plaintext n), μC_M m = PMF.uniformOfFintype (Ciphertext n) := by
  intro m
  -- rw [μC_M, μK]
  -- We use the fact that `encrypt m` is a bijection, which we've captured
  -- as an equivalence `encrypt_equiv m`. Mapping a uniform PMF through an
  -- equivalence results in a uniform PMF.
  -- First, identify `μC_M m` with a uniform PMF via the bijection `xorEquiv m`.
  have hμ : μC_M m = PMF.uniformOfFintype (Ciphertext n) := by
    -- `μC_M m` is `map (encrypt m) μK`
    apply map_uniformOfFintype_equiv (xorEquiv m)
  -- Now just evaluate the uniform PMF.
  simp [hμ, PMF.uniformOfFintype_apply]
    -- using card_congr (xorEquiv m)
