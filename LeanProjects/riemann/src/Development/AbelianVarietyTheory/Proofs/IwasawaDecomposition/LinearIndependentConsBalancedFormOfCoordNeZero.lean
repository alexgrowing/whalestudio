import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem linearIndependent_cons_of_coord_ne_zero :
    ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m p : ℕ}
    (δ : Fin m → balForms bar X) (β : balForms bar X) (c : Fin m → ℝ) (j : Fin m) (e : Fin p ↪ Fin m),
    LinearIndependent ℤ δ → toReal (β : LinearMap.BilinForm ℤ X) = ∑ i, c i • toReal (δ i : LinearMap.BilinForm ℤ X) →
    c j ≠ 0 → j ∉ Set.range e → LinearIndependent ℤ (Fin.cons β (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) := by
  intro O _ bar X _ _ m p δ β c j e hδ hβ hcj hj
  rw [Fintype.linearIndependent_iff] at hδ ⊢
  intro g hg
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ] at hg

  have hgB : g 0 • (β : LinearMap.BilinForm ℤ X) + ∑ k, g k.succ • (δ (e k) : LinearMap.BilinForm ℤ X) = 0 := by
    have := congrArg Subtype.val hg
    simpa [Submodule.coe_sum] using this

  let s : Fin m → ℝ := fun i => ∑ k, if e k = i then (g k.succ : ℝ) else 0
  let r : Fin m → ℝ := fun i => (g 0 : ℝ) * c i + s i
  have hind : ∀ (d : Fin 0 → ℤ) (a : Fin m → ℤ),
      ∑ i, a i • (δ i : LinearMap.BilinForm ℤ X) = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) → a = 0 := by
    intro d a h
    have h' : ∑ i, a i • δ i = 0 := by
      apply Subtype.ext
      simpa [Submodule.coe_sum] using h
    funext i
    exact hδ a h' i
  have hrel : ∑ i, r i • toReal (δ i : LinearMap.BilinForm ℤ X) =
      ∑ k : Fin 0, (0 : Fin 0 → ℝ) k • toReal (Fin.elim0 k : LinearMap.BilinForm ℤ X) := by
    apply LinearMap.ext₂
    intro x y
    have h1 := LinearMap.congr_fun₂ hβ x y
    have h2 := LinearMap.congr_fun₂ hgB x y
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, LinearMap.add_apply, smul_eq_mul,
      LinearMap.zero_apply] at h1 h2
    have h2' : (g 0 : ℝ) * (((β : LinearMap.BilinForm ℤ X) x y : ℤ) : ℝ) + ∑ k, (g k.succ : ℝ) * (((δ (e k) : LinearMap.BilinForm ℤ X) x y : ℤ) : ℝ) = 0 := by
      exact_mod_cast h2
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, Finset.univ_eq_empty,
      Finset.sum_empty, LinearMap.zero_apply]
    rw [← h2', h1]
    simp only [r, s, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, ite_mul, zero_mul, mul_assoc]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hr : r = 0 := eq_zero_of_toReal_rel hind hrel
  have hsj : s j = 0 := Finset.sum_eq_zero fun k _ => by
    rw [if_neg]
    intro h
    exact hj ⟨k, h⟩
  have hg0 : g 0 = 0 := by
    have := congrFun hr j
    simp only [r, hsj, add_zero, Pi.zero_apply] at this
    exact_mod_cast (mul_eq_zero.1 this).resolve_right hcj
  intro i
  refine Fin.cases hg0 (fun k => ?_) i
  have := congrFun hr (e k)
  have hs : s (e k) = (g k.succ : ℝ) := by
    simp only [s]
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'
      rw [if_neg]
      exact fun h => hk' (e.injective h)
    · simp
  simp only [r, hs, hg0, Int.cast_zero, zero_mul, zero_add, Pi.zero_apply] at this
  exact_mod_cast this

end GlobalTheory.PolFan
