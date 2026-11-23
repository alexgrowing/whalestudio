import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRepOfMatrixTuplePadicBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TupMemLatT
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_rep_of_matrixTuple_padic_basis : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (T : Submodule ℤ_[l] (Fin m → Matrix (Fin a) (Fin a) (Om l))) (d' : ℕ) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)), (∀ k, Continuous (ρs k)) → LinearIndependent ℚ_[l] bb → (∀ s, bb s ∈ T) → (∀ x ∈ T, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) → (∀ g, ∀ x ∈ T, GlobalTheory.TraceConjugationCover.tup ρs g * x ∈ T) → ∃ ρ' : Γ →* GL (Fin d') ℤ_[l], Continuous ρ' ∧ ∀ g j, GlobalTheory.TraceConjugationCover.tup ρs g * bb j = ∑ s, zOm l (((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) s j) • bb s := by
  first | (exact @GlobalTheory.CovRep.rep_of_basis) | (exact GlobalTheory.CovRep.rep_of_basis) | (intros; apply GlobalTheory.CovRep.rep_of_basis  <;> assumption)
