import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChartLocalizationFiniteTypeFormallyUnramifi
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtChart
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleChart_localization_finiteType_formallyUnramified : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω] (I : Ideal (TensorProduct R Ω A)),
  letI : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) :=
    (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ I) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) (Ideal.Quotient.mk I (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
  Algebra.FiniteType (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) ∧
    Algebra.FormallyUnramified (MvPolynomial (Fin g) Ω) (Localization.Away (Ideal.Quotient.mk I (1 ⊗ₜ[R] h))) := by
  first | exact @GlobalTheory.DenseSec.locQuot_finiteType_formallyUnramified | exact GlobalTheory.DenseSec.locQuot_finiteType_formallyUnramified | (intros; apply GlobalTheory.DenseSec.locQuot_finiteType_formallyUnramified <;> assumption)
