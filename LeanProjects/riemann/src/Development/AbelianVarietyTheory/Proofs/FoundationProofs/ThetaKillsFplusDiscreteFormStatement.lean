import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaKillsFplusDiscreteForm
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import ReciprocityTheory.GaloisValuations.Global
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ GlobalTheory.Glue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kills_Fplus_discrete_form : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω),
  (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → A.valuation (l : Ω) < 1 → ∀ (N w : ℕ) (F : Finset Ω), l ≠ 2 → ¬ l ∣ N → 1 ≤ N → Odd w → ∃ c : ℕ, ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) → X.galB l s b = ((cycZ ℚ Ω l s : ℤ_[l]) ^ (w + 1)) • b) →
  ∀ (n : ℕ) (φ : HahnSeries ℚ Ω), IsThB X A N l n b φ → ∀ r, CgA A l n ((l : Ω) ^ c * φ.coeff r) 0 := by
  first | exact @GlobalTheory.ThKill.th_kills_Fplus_discrete | exact GlobalTheory.ThKill.th_kills_Fplus_discrete | (intros; apply GlobalTheory.ThKill.th_kills_Fplus_discrete <;> assumption)
