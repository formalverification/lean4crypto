import OTP.Basic -- definitions of Plaintext, Key, etc.

/-! # OTP.KeyUniqueness.lean

## Key Uniqueness in One-Time Pad (OTP)

This file proves properties of keys in the one-time pad (OTP) encryption scheme
that are crucial for OTP's perfect secrecy.

These properties include:
- The involutive nature of the `vec_xor _ k` and `vec_xor m _` operations
- The uniqueness of keys given a plaintext message and ciphertext
- The injectivity of encryption with a fixed key
- The injectivity of encryption of a fixed message
- The bijection between keys and ciphertexts for a fixed message
- The existence of a unique key for each ciphertext given a plaintext

Files in this series:

- OTP.Basic: Basic definitions and operations for OTP
- OTP.KeyUniqueness: Properties of keys in OTP
- OTP.Distributions: Probability distributions related to OTP
- OTP.PerfectSecrecy: Properties of perfect secrecy in OTP
- OTP.Examples: Concrete examples and demos of OTP operations and properties
- OTP.SimpleSecrecy: Simplified version of OTP.PerfectSecrecy where we assume
                     the message distribution is uniform.

 -/


open List.Vector

/-! ## Properties of vec_xor -/

-- `vec_xor` is a pointwise xor operation on boolean vectors.
-- For fixed vector `m`, `λ k => vec_xor m k` is involutive; i.e.,
-- `vec_xor m (vec_xor m k) = k`.
lemma vec_xor_left_involutive {n : Nat} (m : Plaintext n) (k : Key n) :
  vec_xor m (vec_xor m k) = k := by
  unfold vec_xor
  -- Goal: `map₂ xor m (map₂ xor m k) = k`
  apply ext
  -- Goal: `∀ (i : Fin n), map₂ xor m (map₂ xor m k) i = k i`
  intro i
  -- Goal: `map₂ xor m (map₂ xor m k) i = k i`
  simp only [get_map₂]
  -- Goal: `(m i) xor ((m i) xor (k i)) = k i`
  apply xor_aab_eq_b

lemma vec_xor_right_involutive {n : Nat} (m : Plaintext n) (k : Key n) :
  vec_xor (vec_xor m k) k = m := by
  unfold vec_xor
  -- Goal: `map₂ xor m (map₂ xor m k) = k`
  apply ext
  intro i
  -- Goal: `∀ (i : Fin n), map₂ xor m (map₂ xor m k) i = k i`
  simp only [get_map₂]
  -- Goal: `(m i) xor ((m i) xor (k i)) = k i`
  apply xor_abb_eq_a

lemma decrypt_encrypt {n : Nat} (m : Plaintext n) (k : Key n) :
  decrypt (encrypt m k) k = m := by
  unfold encrypt decrypt
  apply vec_xor_right_involutive m k

lemma encrypt_decrypt {n : Nat} (c : Ciphertext n) (k : Key n) :
  encrypt (decrypt c k) k = c := by
  apply decrypt_encrypt

example {n : Nat} (m : Plaintext n) (k : Key n) :
  encrypt (decrypt (encrypt m k) k) k = encrypt m k := by
  apply decrypt_encrypt

example {n : Nat} (c : Ciphertext n) (k : Key n) :
  decrypt (encrypt (decrypt c k) k) k = decrypt c k := by
  apply encrypt_decrypt

-- Example: encryption with a fixed key is injective
-- The function `λ m => encrypt m k` is injective.
example {n : Nat} (k : Key n) (m₁ m₂ : Plaintext n) :
    encrypt m₁ k = encrypt m₂ k → m₁ = m₂ := by

    intro h -- `h : encrypt m₁ k = encrypt m₂ k`

    have h₁ : m₁ = decrypt (encrypt m₁ k) k := by
      rw [decrypt_encrypt m₁ k]

    have h₂ : m₂ = decrypt (encrypt m₂ k) k := by
      rw [decrypt_encrypt m₂ k]
            -- Goal: `m₁ = m₂`
    rw [h₁] -- Goal: `decrypt (encrypt m₁ k) k = m₂`
    rw [h₂] -- Goal: `decrypt (encrypt m₁ k) k = decrypt (encrypt m₂ k) k`
    rw [h]

-- Example: encryption with a fixed message is injective
-- The function `λ k => encrypt m k` is injective.
example {n : Nat} (m : Plaintext n) (k₁ k₂ : Key n) :
    encrypt m k₁ = encrypt m k₂ → k₁ = k₂ := by

    intro h -- `h : encrypt m k₁ = encrypt m k₂`

    have h₁ : k₁ = vec_xor m (encrypt m k₁) := by
      unfold encrypt
      rw [vec_xor_left_involutive m k₁]

    have h₂ : k₂ = vec_xor m (encrypt m k₂) := by
      unfold encrypt
      rw [vec_xor_left_involutive m k₂]

            -- Goal: `k₁ = k₂`
    rw [h₁] -- Goal: `vec_xor m (encrypt m k₁) = k₂`
    rw [h₂] -- Goal: `vec_xor m (encrypt m k₁) = vec_xor m (encrypt m k₂)`
    rw [h]

theorem key_uniqueness {n : Nat} (m : Plaintext n) (k : Key n) (c : Ciphertext n) :
vec_xor m k = c ↔ k = vec_xor m c := by
constructor -- Splits ↔ goal into two subgoals, → and ←.

-- → goal: `vec_xor m k = c → k = vec_xor m c`
· intro m_xor_k_eq_c
  rw [← m_xor_k_eq_c]
  -- New Goal: k = vec_xor m (vec_xor m k)
  rw [vec_xor_left_involutive m k]

-- ← goal: `k = vec_xor m c → vec_xor m k = c`
· intro k_eq_m_xor_c -- Assume k = vec_xor m c
  -- Substitute k using h_k_eq_vmc:
  rw [k_eq_m_xor_c]
  apply vec_xor_left_involutive m c

/-! ## vec_xor is a bijection between Key and Ciphertext  -/

--  For a fixed message `m`, `vec_xor m` is a bijection on Boolean vectors.
def xorEquiv {n : ℕ} (m : Plaintext n) : Key n ≃ Ciphertext n where
  toFun   := vec_xor m  -- := λ k => vec_xor m k  (i.e., encrypt m k)
  invFun  := vec_xor m  -- := λ c => vec_xor m c
  left_inv := by
    intro k
    rw [key_uniqueness m (vec_xor m k)]

  right_inv := by
    intro c
    rw [key_uniqueness m (vec_xor m c)]

-------------------------------------------------------------------------

-- Demo 3: Bijection Property
section BijectionDemo
  -- Show that for every ciphertext there's a unique key.
  example {n : Nat} (m : Plaintext n) (c : Ciphertext n) :
    ∃! k : Key n, encrypt m k = c := by
    use vec_xor m c   -- what to use as existence witness
    constructor
    · -- Prove map₂ xor m (map₂ xor m c) = c by extensionality and xor properties
      apply ext
      intro i
      simp [encrypt, vec_xor, get_map₂]
    · -- Uniqueness
      intro k hk
      exact (key_uniqueness m k c).mp hk
      -- key_uniqueness: vec_xor m y = c ↔ y = vec_xor m c
      -- mp is the "modus ponens" (forward direction) of the equivalence ↔
      -- mpr is the "reverse modus ponens" (backward direction) of the ↔
      -- so we could have written: `exact (key_uniqueness m y c).symm.mpr hk`

  -- Show that encryption with a fixed message is injective
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

end BijectionDemo
