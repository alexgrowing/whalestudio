import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Mum

theorem intAt_of_integral_mul_basicOpen : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ∀ (x : X) (d : Γ(X, W)), x ∈ X.basicOpen d → (α.app W).hom.IsIntegralElem ((α.app W).hom d * chartVal L α s j W hW) → IntAt L α s x := by
  intro X Y L α k s j W hW hWa x d hx hint
  have hle : X.basicOpen d ≤ W := X.basicOpen_le d
  have hW' : X.basicOpen d ≤ L.U j := hle.trans hW
  refine ⟨j, X.basicOpen d, hW', hx, hWa.basicOpen d, ?_⟩
  set ρX := (X.presheaf.map (homOfLE hle).op).hom with hρX
  set ρY := (Y.presheaf.map ((TopologicalSpace.Opens.map α.base).map (homOfLE hle)).op).hom with hρY
  have hnat : ∀ r, ρY ((α.app W).hom r) = (α.app (X.basicOpen d)).hom (ρX r) := by
    intro r
    have := congrArg (fun g => g.hom r) (Scheme.Hom.naturality α (homOfLE hle).op)
    simpa [ρX, ρY] using this.symm
  have hcv : chartVal L α s j (X.basicOpen d) hW' = ρY (chartVal L α s j W hW) := by
    simp only [chartVal, ρY]
    change _ = (Y.presheaf.map (homOfLE (locInt_le_chart L α j W hW)).op ≫
      Y.presheaf.map ((TopologicalSpace.Opens.map α.base).map (homOfLE hle)).op).hom _
    rw [← Functor.map_comp]
    rfl

  have hint' : (α.app (X.basicOpen d)).hom.IsIntegralElem (ρY ((α.app W).hom d * chartVal L α s j W hW)) := by
    obtain ⟨p, hp, hp0⟩ := hint
    refine ⟨p.map ρX, hp.map ρX, ?_⟩
    rw [Polynomial.eval₂_map]
    have : ((α.app (X.basicOpen d)).hom.comp ρX) = ρY.comp (α.app W).hom := by
      ext r; exact (hnat r).symm
    rw [this, ← Polynomial.hom_eval₂, hp0, map_zero]
  obtain ⟨u, hu⟩ : IsUnit (ρX d) := X.toRingedSpace.isUnit_res_basicOpen d
  have hmul : ρY ((α.app W).hom d * chartVal L α s j W hW) =
      (α.app (X.basicOpen d)).hom (u : Γ(X, X.basicOpen d)) * chartVal L α s j (X.basicOpen d) hW' := by
    rw [map_mul, hnat, hcv]
    congr 2
    exact hu.symm
  rw [hmul] at hint'
  have key : chartVal L α s j (X.basicOpen d) hW' =
      (α.app (X.basicOpen d)).hom ((u⁻¹ : (Γ(X, X.basicOpen d))ˣ) : Γ(X, X.basicOpen d)) *
        ((α.app (X.basicOpen d)).hom (u : Γ(X, X.basicOpen d)) * chartVal L α s j (X.basicOpen d) hW') := by
    rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
  rw [key]
  exact RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) hint'

end GlobalTheory.Mum
