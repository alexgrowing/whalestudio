import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionSumMulMiddleCoordinate

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

namespace GlobalTheory.BumpMixQuasi

variable {D : D7}

theorem pair_add_left (T : HSp D) {ρ : ℕ} (x x' a : Mx D T.rank ρ) :
    trHalf D (pairS T (x + x') a) = trHalf D (pairS T x a) + trHalf D (pairS T x' a) := by
  rw [← map_add]
  congr 1
  simp only [pairS, Matrix.mul_add, trace_add]

theorem pair_add_right (T : HSp D) {ρ : ℕ} (x a a' : Mx D T.rank ρ) :
    trHalf D (pairS T x (a + a')) = trHalf D (pairS T x a) + trHalf D (pairS T x a') := by
  rw [← map_add]
  congr 1
  simp only [pairS, adj_add, Matrix.add_mul, trace_add]

theorem pair_sub_left (T : HSp D) {ρ : ℕ} (x x' a : Mx D T.rank ρ) :
    trHalf D (pairS T (x - x') a) = trHalf D (pairS T x a) - trHalf D (pairS T x' a) := by
  rw [eq_sub_iff_add_eq, ← pair_add_left, sub_add_cancel]

theorem pair_rat {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ) {x a : Mx D T.rank ρ}
    (hx : x ∈ ratMx D T.rank ρ) (ha : a ∈ ratMx D T.rank ρ) :
    ∃ c, trHalf D (pairS T x a) = algebraMap D.host.F (AF D.host.F) c := by
  rw [← d.symplOH_extX_extY]
  exact (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.2.1 _ (ratMx_mul hx (rat_mem _)) _ (ratMx_mul ha (rat_mem _))

theorem symplOH_coords {S S₀ : HSp D} (T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ) (h0 : S₀.rank = 0) (u w : WO S T) :
    symplOH S T u w = trHalf D (pairS T (u ⬝ d.jX) (w ⬝ d.jY)) - trHalf D (pairS T (w ⬝ d.jX) (u ⬝ d.jY)) := by
  have hz : ∀ v : WO S₀ T, v = 0 := fun v => by
    funext i j
    exact absurd j.2 (by omega)
  have e : ∀ v : WO S T, v = d.extX T (v ⬝ d.jX) + d.extY T (v ⬝ d.jY) := fun v => by
    have h := eq_coords d v
    rwa [hz (v ⬝ d.j0), map_zero, add_zero] at h
  conv_lhs => rw [e u, e w]
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
    d.symplOH_extX_extX, d.symplOH_extY_extY, d.symplOH_extX_extY, symplOH_Y_X]
  ring

theorem poinX_quasi : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), S₀.rank = 0 → ∀ (β : Mx D T.rank ρ → ℂ) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T), poinX ψ d T β (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * poinX ψ d T β w := by
  intro D ψ hψ S S₀ T ρ d h0 β γ w
  obtain ⟨δ, hδ⟩ : (ratW T S γ : WO S T) ⬝ d.jX ∈ ratMx D T.rank ρ := ratMx_mul (rat_mem γ) (rat_mem _)
  have hδ' : (ratW T S γ : WO S T) ⬝ d.jX = rat δ := hδ.symm
  have ha : (ratW T S γ : WO S T) ⬝ d.jY ∈ ratMx D T.rank ρ := ratMx_mul (rat_mem γ) (rat_mem _)
  have eX : (ratW T S γ + w : WO S T) ⬝ d.jX = rat δ + w ⬝ d.jX := by
    rw [← hδ']; exact Matrix.add_mul _ _ _
  have eY : (ratW T S γ + w : WO S T) ⬝ d.jY = (ratW T S γ : WO S T) ⬝ d.jY + w ⬝ d.jY := Matrix.add_mul _ _ _
  rw [symplOH_coords T d h0, hδ']
  unfold poinX
  rw [eX, eY, ← (Equiv.subRight δ).tsum_eq, ← tsum_mul_left]
  generalize (ratW T S γ : WO S T) ⬝ d.jY = a at ha ⊢
  generalize w ⬝ d.jX = x
  generalize w ⬝ d.jY = y
  congr 1
  funext g
  simp only [Equiv.subRight_apply]
  rw [rat_sub]
  have e1 : rat δ + x + (rat g - rat δ) = x + rat g := by abel
  have e2 : rat δ + x + 2 • (rat g - rat δ) = x + 2 • rat g - rat δ := by
    rw [two_smul, two_smul]; abel
  have e3 : x + 2 • rat g - rat δ = x + (rat g + rat g - rat δ) := by
    rw [two_smul]; abel
  obtain ⟨c, hc⟩ := pair_rat T d (((ratMx D T.rank ρ).sub_mem ((ratMx D T.rank ρ).add_mem (rat_mem g) (rat_mem g))
    (rat_mem δ))) ha
  have e4 : trHalf D (pairS T (x + 2 • rat g - rat δ) (a + y)) =
      algebraMap D.host.F (AF D.host.F) c + (-(trHalf D (pairS T (rat δ) y) - trHalf D (pairS T x a)) +
        trHalf D (pairS T (x + 2 • rat g) y)) := by
    rw [pair_add_right, pair_sub_left T _ _ y, e3, pair_add_left T x _ a, hc]
    ring
  rw [e1, e2, e4, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψ.1.2.2.1 c]
  ring

end GlobalTheory.BumpMixQuasi

end
