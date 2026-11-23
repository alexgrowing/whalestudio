import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph

set_option autoImplicit false

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory.CayleyBlock

theorem coeff_dList_of_nodup {σ : Type} [DecidableEq σ] (l : List σ) (hl : l.Nodup) (m : σ →₀ ℕ)
    (hm : ∀ v ∈ l, m v = 0) (G : MvPolynomial σ ℂ) :
    coeff m (dList l G) = coeff (m + (l.map fun v => Finsupp.single v 1).sum) G := by
  induction l generalizing m with
  | nil => simp [dList]
  | cons v l ih =>
    have hc : dList (v :: l) G = pderiv v (dList l G) := by
      simp [dList]
    rw [List.nodup_cons] at hl
    have h0 : m v = 0 := hm v (List.mem_cons_self ..)
    have h1 : ∀ w ∈ l, (m + Finsupp.single v 1 : σ →₀ ℕ) w = 0 := by
      intro w hw
      have hne : w ≠ v := fun h => hl.1 (h ▸ hw)
      rw [Finsupp.add_apply, hm w (List.mem_cons_of_mem _ hw), Finsupp.single_eq_of_ne hne, add_zero]
    rw [hc, MvPolynomial.coeff_pderiv, ih hl.2 _ h1, h0, List.map_cons, List.sum_cons, add_assoc]
    simp

end GlobalTheory.CayleyBlock
