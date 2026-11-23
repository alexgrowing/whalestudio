import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumFiniteDimensionalOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_datum_finite_dimensional_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.KP → GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ Φ ∈ GlobalTheory.ThK.PolData B M,
      ∃ S : Submodule ℂ (GlobalTheory.ThK.Fn F n d), FiniteDimensional ℂ S ∧ S ≤ GlobalTheory.ThK.PolData B M ∧ ∀ k ∈ KInf σ W B.emb, om (1, k) Φ ∈ S := by
  first | exact @GlobalTheory.FockKFin.polData_kfin | exact GlobalTheory.FockKFin.polData_kfin | (intros; apply GlobalTheory.FockKFin.polData_kfin <;> assumption)
