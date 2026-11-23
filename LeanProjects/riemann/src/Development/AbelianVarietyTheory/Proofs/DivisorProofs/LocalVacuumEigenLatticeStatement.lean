import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalVacuumEigenLattice
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_vacuum_eigen_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → ∀ (v : Pl F) (t : Matrix (Fin n) (Fin d) (AE F E) → ℂ),
    (∀ γ ∈ latAtV X W v, locOp B.ψ v (locPt v (M.co.e γ)) (M.vac v) = t γ • M.vac v) →
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), (∀ γ ∈ latAtV X W v, locOp B.ψ v (locPt v (M.co.e γ)) φ = t γ • φ) →
      ∃ a : ℂ, φ = a • M.vac v := by
  first | exact @GlobalTheory.VacEigenLine.eigen_line | exact GlobalTheory.VacEigenLine.eigen_line | (intros; apply GlobalTheory.VacEigenLine.eigen_line <;> assumption)
