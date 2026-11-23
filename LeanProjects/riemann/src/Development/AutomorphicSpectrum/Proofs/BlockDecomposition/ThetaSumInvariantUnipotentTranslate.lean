import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThetaInv

variable {D : D7}

theorem trA_incA (e : D.host.E) :
    trA (incA D e) = algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
  change Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem halfTr_incA (e : D.host.E) :
    halfTr (incA D e) =
      algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E e) := by
  rw [halfTr, trA_incA, map_mul]

theorem psi_unip_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {n : ℕ} (V : HSp D)
    (b : Matrix (Fin n) (Fin n) D.host.E) (ξ : Matrix (Fin V.rank) (Fin n) D.host.E) :
    ψ (halfTr (Matrix.trace (b.map (incA D) ⬝ inner V (ξ.map (incA D)) (ξ.map (incA D)) : Mx D n n))) = 1 := by
  have h : (b.map (incA D) ⬝ inner V (ξ.map (incA D)) (ξ.map (incA D)) : Mx D n n) =
      (b * (ξᴴ * (V.gram * ξ))).map (incA D) := by
    change (rat b ⬝ (adj (rat ξ) ⬝ (gA V ⬝ rat ξ)) : Mx D n n) = rat (b * (ξᴴ * (V.gram * ξ)))
    rw [rat_mul, rat_mul, rat_mul, rat_conjTranspose, gA]
  have ht : ∀ M : Matrix (Fin n) (Fin n) D.host.E,
      Matrix.trace (M.map (incA D)) = incA D (Matrix.trace M) := fun M => by
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  rw [h, ht, halfTr_incA]
  exact hψ.2.2.1 _

theorem theta_unip : ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
    ∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 →
    ∀ Φ : schwartzA θ V.rank n,
      ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, (ω g Φ).1 (ξ.map (incA D)) =
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Φ.1 (ξ.map (incA D)) := by
  intro D n V ψ χ θ μ ω hS g b hg Φ
  refine tsum_congr fun ξ => ?_
  rw [hS.2.2.2.2.2.2.2.unip g (b.map (incA D)) hg Φ (ξ.map (incA D)), psi_unip_rat hS.2.2.1, one_mul]

end GlobalTheory.CompanionTheory.ThetaInv
