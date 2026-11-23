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

noncomputable section
namespace GlobalTheory.LocReg

theorem comp_genι_eq_spMap_chartHom (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) :
    ξ ≫ genι Y = spMap (GlobalTheory.LocReg.chartHom Y U ξ hx) ≫ chart U := by
  have hx' : (ξ ≫ genι Y) (closedPoint (ChartRing k m d)) ∈ U.1 := hx
  have e1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (ξ ≫ genι Y)
  have e2 : Y.X.fromSpecStalk ((ξ ≫ genι Y) (closedPoint (ChartRing k m d))) =
      Spec.map (Y.X.presheaf.germ U.1 _ hx') ≫ U.2.fromSpec :=
    (U.2.fromSpecStalk_eq_fromSpecStalk hx').symm
  rw [e2, ← Spec.map_comp_assoc, Scheme.stalkClosedPointTo_comp] at e1
  rw [← e1, chart]
  congr 2
  exact (Scheme.Hom.germ_stalkMap_assoc (genι Y) U.1 (ξ (closedPoint _)) hx (Scheme.stalkClosedPointTo ξ)).trans rfl

end GlobalTheory.LocReg
end
