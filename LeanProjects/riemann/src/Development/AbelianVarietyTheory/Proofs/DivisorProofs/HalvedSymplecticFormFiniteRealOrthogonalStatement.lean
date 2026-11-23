import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalvedSymplecticFormFiniteRealOrthogonal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halvedSymplecticForm_finite_real_orthogonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (u x : WOF F E nS nT),
      u.map (infPartF F E) = 0 → x.map (finPartF F E) = 0 → symplOHF σ JS JT ξ₀ u x = 0 ∧ symplOHF σ JS JT ξ₀ x u = 0 := by
  first | exact @GlobalTheory.WeilDatumF.symplOHF_fin_real_orth | exact GlobalTheory.WeilDatumF.symplOHF_fin_real_orth | (intros; apply GlobalTheory.WeilDatumF.symplOHF_fin_real_orth <;> assumption)
