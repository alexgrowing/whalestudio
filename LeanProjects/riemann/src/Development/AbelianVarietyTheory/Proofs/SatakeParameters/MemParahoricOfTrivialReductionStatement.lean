import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_parahoric_of_trivial_reduction : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs → (∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E))) → ∀ h : AutY X R j, h ∈ stabL X.E _ (lamYat (Pr := Pr) j w) → ∀ κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j), κ ∈ GLint X.E (R.N j) w → (∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) → κ ∈ prCat (Pr := Pr) sharp j w h := by
  first | exact @GlobalTheory.CongLevel.cong_mem_prCat | exact GlobalTheory.CongLevel.cong_mem_prCat | (intros; apply GlobalTheory.CongLevel.cong_mem_prCat <;> assumption)
