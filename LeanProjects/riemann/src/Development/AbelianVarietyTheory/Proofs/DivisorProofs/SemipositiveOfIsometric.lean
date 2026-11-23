import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts

namespace GlobalTheory

namespace HermLB

theorem Isometric.semiPos : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    (L M : GlobalTheory.HermLB p) (D : ℕ), L.Isometric M → L.SemiPos D → M.SemiPos D := by
  intro k _ X p L M D h hL σ a c y hy ξ
  have hb := mem_pick (L.φ σ).isLB y
  have hL' := hL σ _ c y ⟨hy.1, hb⟩ ξ
  have e := h.hess_eq c hy.1 hy.2 hb
  have hM : ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((M.φ σ).φ a (c.e.symm v) : ℂ)) (c.e y) ξ =
      ∑ j, ∑ l, c.hess (M.φ σ) a y j l * ξ j * (starRingEnd ℂ) (ξ l) := rfl
  have hL₂ : ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((L.φ σ).φ (pick (L.φ σ).isLB y) (c.e.symm v) : ℂ))
      (c.e y) ξ = ∑ j, ∑ l, c.hess (L.φ σ) (pick (L.φ σ).isLB y) y j l * ξ j * (starRingEnd ℂ) (ξ l) := rfl
  rw [hM, e, ← hL₂]
  exact hL'

end HermLB

end GlobalTheory
