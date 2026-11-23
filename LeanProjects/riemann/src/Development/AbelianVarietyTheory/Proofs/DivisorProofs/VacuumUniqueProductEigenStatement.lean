import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumUniqueProductEigen
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_unique_product_eigen : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ) (Q : ∀ v : Pl F, Set (((κ → Fv F v) × (κ → Fv F v)) × ℂ)),
    (∀ v, vac v ∈ SB (κ → Fv F v)) → (∀ v, vac v ≠ 0) → (∀ᶠ v in cofinite, vac v = indO v) →
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), (∀ q ∈ Q v, locOp ψ v q.1 φ = q.2 • φ) → ∃ a : ℂ, φ = a • vac v) →
    ∀ g ∈ SB (κ → Af F), (∀ v, ∀ q ∈ Q v, finOp ψ v q.1 g = q.2 • g) → ∃ a : ℂ, g = a • vacProd vac := by
  first | exact @GlobalTheory.VacFactor.eq_smul_vacProd | exact GlobalTheory.VacFactor.eq_smul_vacProd | (intros; apply GlobalTheory.VacFactor.eq_smul_vacProd <;> assumption)
