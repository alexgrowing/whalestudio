import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmTypeStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdUnn

theorem exists_unique_of_comp_finPart : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (x₀ : Mx D m n), ∃! x : Mx D m n, (∀ τ, compAt θ τ x = z τ) ∧ x.map (finPart D) = x₀.map (finPart D) := by
  intro D θ hθ m n z x₀
  have hL : ∀ τ (w : Matrix (Fin m) (Fin n) ℂ), IsLineAt θ τ w (lineAt θ τ w) := fun τ w =>
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ w)
  let C : D.what₂.Tau → Mx D m n →+ Matrix (Fin m) (Fin n) ℂ := fun τ =>
    (((θ τ).comp (infPart D)).toAddMonoidHom).mapMatrix
  have hC : ∀ τ w, compAt θ τ w = C τ w := fun τ w => rfl
  let P : Mx D m n →+ Matrix (Fin m) (Fin n) _ := ((finPart D).toAddMonoidHom).mapMatrix
  have hP : ∀ w : Mx D m n, w.map (finPart D) = P w := fun w => rfl
  have key : ∀ x y : Mx D m n, (∀ τ, compAt θ τ x = compAt θ τ y) → x.map (finPart D) = y.map (finPart D) → x = y := by
    intro x y h1 h2
    refine Matrix.ext fun i j => ?_
    rw [← sub_eq_zero]
    refine (GlobalTheory.T.extensionAdele_realComponents_cmType D θ hθ).2.2.2 (x i j - y i j) (fun τ => ?_) ?_
    · have := congrFun (congrFun (h1 τ) i) j
      simp only [compAt, Matrix.map_apply] at this
      rw [(infPart D).map_sub, (θ τ).map_sub, this, sub_self]
    · have := congrFun (congrFun h2 i) j
      simp only [Matrix.map_apply] at this
      rw [(finPart D).map_sub, this, sub_self]
  refine ⟨x₀ + ∑ σ, lineAt θ σ (z σ - compAt θ σ x₀) 1, ⟨fun τ => ?_, ?_⟩, ?_⟩
  · rw [hC, map_add, map_sum, ← hC]
    simp_rw [← hC, (hL _ _).2.2 1 τ]
    rw [Finset.sum_eq_single τ (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl, Complex.ofReal_one, one_smul]
    abel
  · rw [hP, hP, map_add, map_sum]
    simp_rw [← hP, (hL _ _).2.1 1]
    simp
  · rintro y ⟨hy1, hy2⟩
    apply key
    · intro τ
      rw [hy1, hC, map_add, map_sum, ← hC]
      simp_rw [← hC, (hL _ _).2.2 1 τ]
      rw [Finset.sum_eq_single τ (fun b _ hb => if_neg (Ne.symm hb)) (by simp), if_pos rfl, Complex.ofReal_one, one_smul]
      abel
    · rw [hy2, hP, hP, map_add, map_sum]
      simp_rw [← hP, (hL _ _).2.1 1]
      simp

end GlobalTheory.StdUnn
