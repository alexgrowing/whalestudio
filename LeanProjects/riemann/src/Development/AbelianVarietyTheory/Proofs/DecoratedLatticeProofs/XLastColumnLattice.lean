import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SplitLast

variable {D : D7}

theorem proj_mem_adelic_lattice_of_mono {W W₀ : HSp D} {σ : ℕ} (d : HypDec W W₀ σ) {LW : Lat W} {LW₀ : Lat W₀} {v : Pl D}
    (hm : MonoAt d LW LW₀ v) {y : Fin W.rank → AE D} (hy : y ∈ latA W LW (· = v)) :
    d.p0 *ᵥ y ∈ latA W₀ LW₀ (· = v) := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin W.rank → AE D := fun k => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x k) with hu
    have hu' : u ∈ latV W LW (· = v) := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hg : (fun k => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x k)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • u := by
      funext k
      simp only [hu, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have heq : d.p0 *ᵥ (((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • u) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (d.p0 *ᵥ u) k := by
      funext k
      simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    rw [hg, heq]
    exact VacFlat.smul_mem_latA ha (((hm u).1 hu').2.2)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end GlobalTheory.FinPl.SplitLast

end
