import Mathlib.Probability.ProbabilityMassFunction.Constructions -- for PMF.uniformOfFintype
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Probability.Distributions.Uniform -- for uniformOfFintype
import Mathlib.Data.Fintype.Vector -- Provides Fintype for List.Vector
import OTP.Basic -- definitions of Plaintext, Key, etc.
-- OTP.Basic already imports Mathlib.Data.Vector.Basic (for Inhabited/Nonempty)
open OTP -- To use Key, Plaintext, etc. without OTP. prefix
open PMF -- To use uniformOfFintype without PMF. prefix

-- Ensure Fintype and Nonempty instances are available for:
-- Ciphertext n, Key n (needed for uniformOfFintype, etc.)
instance key_fintype {n : ℕ} : Fintype (Key n) := by
  unfold Key; exact inferInstance
instance key_nonempty {n : ℕ} : Nonempty (Key n) := by
  unfold Key; exact inferInstance


-- 3. Define Uniform Key Probability Mass Function
-- This defines a uniform PMF over the keys of length n.
noncomputable def μK {n : ℕ} : PMF (Key n) := uniformOfFintype (Key n)
-- `PMF.uniformOfFintype` is noncomputable because it involves division to
-- compute probabilities (which are `NNReal`, non-negative reals)---operations
-- that are not computable in Lean's constructive framework.

-- card (Key n) is 2^n. Mathlib has `card_vector`.
-- `card (List.Vector Bool n) = (card Bool) ^ n = 2 ^ n`.
-- So, (μK k) should be (1 / (2^n : ℝ≥0)). (NNReal for probabilities)
#check μK (n := 3) -- PMF (Key 3)
#check μK (n := 3) ⟨[true, false, true], by decide⟩ -- PMF (Key 3)

-- This is a PMF with probabilities 1/8 for each key

-- We can verify properties later, e.g.,
-- `(μK k) = 1 / card (Key n)`

/- **Independence and Joint Distribution**
  The crucial assumption for OTP's perfect secrecy is that the key $K$
  is chosen independently of the message $M$.

  For pmfs `μM : PMF (Plaintext n)` and `μK : PMF (Key n)`, their joint
  distribution `μMK : PMF (Plaintext n × Key n)` assigns probability
  `(μM m) * (μK k)` to the pair `(m, k)`.
 -/
noncomputable def μMK {n : ℕ} (μM : PMF (Plaintext n)) : PMF (Plaintext n × Key n) :=
  PMF.bind μM (λ m => PMF.map (λ k => (m, k)) μK)

/- **Ciphertext Distribution**
  Obtained by applying the `encrypt` function to each pair.
-/
noncomputable def μC {n : Nat} (μM : PMF (Plaintext n)) : PMF (Ciphertext n) :=
  PMF.bind (μMK μM) (λ ⟨m, k⟩ => PMF.pure (encrypt m k))
  -- or, PMF.map (λ ⟨m, k⟩ => encrypt m k) (μMK μM)

/- $ℙ(C = c | M = m)$
  This term represents the probability that the ciphertext is `c`, given
  that the plaintext was `m`.  If the plaintext is fixed as `m`, the
  ciphertext r.v. $C = encrypt(m, K)$ depends only on the randomly chosen
  key $K$ (which follows the `μK` distribution).
-/
noncomputable def μC_M {n : Nat} (m : Plaintext n) : PMF (Ciphertext n) :=
  PMF.map (λ k : Key n => encrypt m k) μK
