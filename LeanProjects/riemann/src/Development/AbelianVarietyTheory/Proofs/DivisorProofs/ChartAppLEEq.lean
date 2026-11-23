import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocReg

theorem chart_appLE_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), ∃ hg : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1, ((ξ ≫ genι Y).appLE U.1 ⊤ hg).hom = (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx) := by
  intro E _ _ _ H Dw l Xo c Y U k _ m d ξ hx
  have hx' : (ξ ≫ genι Y) (closedPoint (CommRingCat.of (ChartRing k m d))) ∈ U.1 := hx
  refine ⟨(Scheme.preimage_eq_top_of_closedPoint_mem (ξ ≫ genι Y) hx').ge, ?_⟩
  have key : (gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) _ hx ≫ Scheme.stalkClosedPointTo ξ =
      ξ.appLE (genι Y ⁻¹ᵁ U.1) ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge ≫
        (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  have e : (ξ ≫ genι Y).appLE U.1 ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem (ξ ≫ genι Y) hx').ge =
      (genι Y).app U.1 ≫ (gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) _ hx ≫ Scheme.stalkClosedPointTo ξ ≫
        (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv := by
    rw [reassoc_of% key, Iso.hom_inv_id, Category.comp_id, Scheme.Hom.comp_appLE]
  rw [e]
  rfl

end GlobalTheory.LocReg
