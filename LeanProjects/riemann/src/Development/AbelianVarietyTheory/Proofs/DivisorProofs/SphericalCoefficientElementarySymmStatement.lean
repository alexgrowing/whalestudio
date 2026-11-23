import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalCoefficientElementarySymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_coefficient_elementary_symm : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) (k : ℕ), ParGL P n lab c s → k ≤ n → lab (dualLab (splitLab n k)) → c (dualLab (splitLab n k)) = (qV E P : ℂ) ^ (((k : ℂ) * ((n : ℂ) - k)) / 2) * s.esymm k := by
  first | exact @GlobalTheory.SphPar.parGL_dualLab_splitLab | exact GlobalTheory.SphPar.parGL_dualLab_splitLab | (intros; apply GlobalTheory.SphPar.parGL_dualLab_splitLab <;> assumption)
