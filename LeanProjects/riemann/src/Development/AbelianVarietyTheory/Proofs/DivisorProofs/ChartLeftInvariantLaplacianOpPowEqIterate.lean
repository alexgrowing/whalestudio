import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

namespace GlobalTheory.HCAlpha

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem vecF_eqOn_invSet (X : Lie E a) {f f' : Lie E a → ℂ} (h : Set.EqOn f f' (invSet E a)) :
    Set.EqOn (vecF E a X f) (vecF E a X f') (invSet E a) := fun y hy => by
  have e : f =ᶠ[nhds y] f' := Filter.eventually_of_mem (isOpen_invSet.mem_nhds hy) h
  simp only [vecF, e.fderiv_eq]

theorem lapF_eqOn_invSet {f f' : Lie E a → ℂ} (h : Set.EqOn f f' (invSet E a)) :
    Set.EqOn (lapF E a f) (lapF E a f') (invSet E a) := fun y hy => by
  simp only [lapF, Finset.sum_apply, Pi.add_apply]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [vecF_eqOn_invSet _ (vecF_eqOn_invSet _ h) hy, vecF_eqOn_invSet _ (vecF_eqOn_invSet _ h) hy]

theorem chart_lie_eqOn_invSet (X : Lie E a) (φ : Sm E a) (g : GA E a) :
    Set.EqOn (chart (lie E a X φ).1 g) (vecF E a X (chart φ.1 g)) (invSet E a) := fun _ hy =>
  chart_lieD φ.2 X g hy

theorem chart_lie_sq_eqOn_invSet (X : Lie E a) (φ : Sm E a) (g : GA E a) :
    Set.EqOn (chart ((lie E a X ^ 2) φ).1 g) (vecF E a X (vecF E a X (chart φ.1 g))) (invSet E a) := by
  rw [sq]
  exact (chart_lie_eqOn_invSet X (lie E a X φ) g).trans (vecF_eqOn_invSet X (chart_lie_eqOn_invSet X φ g))

theorem chart_lapOp_eqOn_invSet (φ : Sm E a) (g : GA E a) :
    Set.EqOn (chart (lapOp E a φ).1 g) (lapF E a (chart φ.1 g)) (invSet E a) := fun y hy => by
  have hy' : IsUnit (Matrix.of y) := hy
  have key : ∀ X : Lie E a, ((lie E a X ^ 2) φ).1 (g * infGL E a hy'.unit) =
      vecF E a X (vecF E a X (chart φ.1 g)) y := fun X => by
    rw [← chart_lie_sq_eqOn_invSet X φ g hy, chart, dif_pos hy']
  rw [chart, dif_pos hy']
  simp only [lapOp, lapF, LinearMap.sum_apply, LinearMap.add_apply, Submodule.coe_sum, Submodule.coe_add,
    Finset.sum_apply, Pi.add_apply]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← key, ← key]
  rfl

theorem chart_lapOp_pow (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (g : GA E a) (n : ℕ) :
    ∀ y ∈ invSet E a, chart ((lapOp E a ^ n) φ).1 g y = (lapF E a)^[n] (chart φ.1 g) y := by
  induction n with
  | zero => intro y _; rfl
  | succ n ih =>
    intro y hy
    rw [pow_succ', Function.iterate_succ_apply', Module.End.mul_apply, chart_lapOp_eqOn_invSet _ g hy]
    exact lapF_eqOn_invSet ih hy

end GlobalTheory.HCAlpha

end
