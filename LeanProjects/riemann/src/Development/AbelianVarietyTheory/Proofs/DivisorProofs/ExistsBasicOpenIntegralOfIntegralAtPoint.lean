import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem chart_res_res {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem chart_res_app {X Y : Scheme.{0}} (α : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (Y.presheaf.map (homOfLE (α.preimage_mono h)).op).hom ((α.app U).hom x) =
      (α.app V).hom ((X.presheaf.map (homOfLE h).op).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]; rfl

theorem isIntegralElem_of_square {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : C →+* D) (a : A →+* C) (b : B →+* D) (h : g.comp a = b.comp f) {x : B}
    (hx : f.IsIntegralElem x) : g.IsIntegralElem (b x) := by
  obtain ⟨p, hp, hpx⟩ := hx
  refine ⟨p.map a, hp.map a, ?_⟩
  rw [Polynomial.eval₂_map, h, ← Polynomial.hom_eval₂, hpx, map_zero]

theorem intAt_chart {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (ζ : X) :
    IntAt L α s ζ → ∀ (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ζ ∈ W →
      ∃ c : Γ(X, W), ζ ∈ X.basicOpen c ∧ (α.app (X.basicOpen c)).hom.IsIntegralElem
        ((Y.presheaf.map (homOfLE (α.preimage_mono (X.basicOpen_le c))).op).hom (chartVal L α s j W hW)) := by
  intro hint j W hW hWa hζW
  obtain ⟨j', W', hW', hζW', hW'a, hint'⟩ := hint
  obtain ⟨c, hcle, hζc⟩ := hWa.exists_basicOpen_le (V := W ⊓ W') ⟨ζ, hζW, hζW'⟩ hζW
  refine ⟨c, hζc, ?_⟩
  have hBW : X.basicOpen c ≤ W := hcle.trans inf_le_left
  have hBW' : X.basicOpen c ≤ W' := hcle.trans inf_le_right
  have hBV : α ⁻¹ᵁ X.basicOpen c ≤ LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j) ⊓
      LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j') :=
    le_inf ((α.preimage_mono hBW).trans (locInt_le_chart L α j W hW))
      ((α.preimage_mono hBW').trans (locInt_le_chart L α j' W' hW'))
  have hBjj : X.basicOpen c ≤ L.U j ⊓ L.U j' := le_inf (hBW.trans hW) (hBW'.trans hW')
  have key := congrArg (Y.presheaf.map (homOfLE hBV).op).hom (s.compat (fun _ => j) (fun _ => j'))
  erw [chart_res_res, map_mul, chart_res_res] at key
  have ht : (Y.presheaf.map (homOfLE hBV).op).hom
      ((LB.LinComb L (K := Fin 1) (fun _ => α) (fun _ => (k : ℤ))).g (fun _ => j) (fun _ => j')).val =
      (α.app (X.basicOpen c)).hom (((X.presheaf.map (homOfLE hBjj).op).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) ^ k) := by
    simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, res, pullU, Units.coe_map, map_pow]
    congr 1
    erw [Units.coe_map, Units.coe_map]
    erw [chart_res_res, ← chart_res_app α hBjj]
    rfl
  have hj' : (α.app (X.basicOpen c)).hom.IsIntegralElem
      ((Y.presheaf.map (homOfLE (α.preimage_mono hBW')).op).hom (chartVal L α s j' W' hW')) :=
    isIntegralElem_of_square (α.app W').hom (α.app (X.basicOpen c)).hom (X.presheaf.map (homOfLE hBW').op).hom
      (Y.presheaf.map (homOfLE (α.preimage_mono hBW')).op).hom (RingHom.ext fun x => (chart_res_app α hBW' x).symm) hint'
  rw [chartVal] at hj' ⊢
  erw [chart_res_res] at hj' ⊢
  erw [key, ht]
  exact RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) hj'

end GlobalTheory.Mum
