import OTP.Basic -- definitions of Plaintext, Key, etc.

/-! ## vec_xor properties -/

lemma decrypt_encrypt {n : Nat} (m : Plaintext n) (k : Key n) :
  decrypt (encrypt m k) k = m := by
  unfold encrypt decrypt vec_xor
  -- Goal: `map₂ xor (map₂ xor m k) k = m`
  apply List.Vector.ext
  intro i
  -- Goal: `(map₂ xor (map₂ xor m k) k).get i = get m i`
  simp only [List.Vector.get_map₂] -- `get_map₂ (f : α → β → γ) (v₁ : List.Vector α n)`
                                   --          `(v₂ : List.Vector β n) (i : Fin n) :`
                                   --          `(map₂ f v₁ v₂).get i = f (v₁.get i) (v₂.get i)`
  -- Goal: `(m i xor k i) xor k i = m i`
  apply xor_abb_eq_a

open List.Vector

lemma encrypt_decrypt {n : Nat} (c : Ciphertext n) (k : Key n) :
  encrypt (decrypt c k) k = c := by
  unfold encrypt decrypt vec_xor
  apply decrypt_encrypt

lemma vec_xor_of_m_involutive {n : Nat} (m : Plaintext n) (k : Key n) :
  vec_xor m (vec_xor m k) = k := by
  unfold vec_xor
  -- Goal: `map₂ xor m (map₂ xor m k) = k`
  apply ext
  intro i
  -- Goal: `∀ (i : Fin n), map₂ xor m (map₂ xor m k) i = k i`
  simp only [get_map₂]
  -- Goal: `(m i) xor ((m i) xor (k i)) = k i`
  apply xor_aab_eq_b

theorem key_uniqueness {n : Nat} (m : Plaintext n) (k : Key n) (c : Ciphertext n) :
vec_xor m k = c ↔ k = vec_xor m c := by
constructor -- Splits ↔ goal into two subgoals, → and ←.

-- → goal: `vec_xor m k = c → k = vec_xor m c`
· intro m_xor_k_eq_c
  rw [← m_xor_k_eq_c]
  -- New Goal: k = vec_xor m (vec_xor m k)
  rw [vec_xor_of_m_involutive m k]

-- ← goal: `k = vec_xor m c → vec_xor m k = c`
· intro k_eq_m_xor_c -- Assume k = vec_xor m c
  -- Substitute k using h_k_eq_vmc:
  rw [k_eq_m_xor_c]
  apply vec_xor_of_m_involutive m c


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
