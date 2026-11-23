import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularFnAgreeOnOverlapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalRegularFnOrdinaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularFnUnitNearGenerizationStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TorRef

theorem exists_regularFn_traitOrd : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)), HasCones Cn Z → HasLinForms Cn φ → ∀ z : Z.X, ∃ (U : Z.X.Opens) (_ : z ∈ U) (f : Γ(Z.X, U)), IsRegularFn f ∧ TraitOrd φ Z U f := by
  intro E _ _ _ H D l Xo c Z Cn φ hC hL z
  obtain ⟨U0, hz0, f0, hreg0, -, hgen0⟩ := GlobalTheory.T.exists_local_regular_fn_ordinary Z Cn φ hC hL z
  obtain ⟨U, hUU0, hzU, hcod⟩ := GlobalTheory.T.regular_fn_unit_near_generization Z Cn φ hC hL z U0 f0 hz0 hreg0 hgen0
  refine ⟨U, hzU, resG Z.X hUU0 f0, hreg0.resG hUU0, traitOrd_of_traitOrdPt fun x hx => ?_⟩
  obtain ⟨V0, hxV0, g0, hregg, hgx, hgen'⟩ := GlobalTheory.T.exists_local_regular_fn_ordinary Z Cn φ hC hL x
  obtain ⟨V, hVV0, hxV, hcodV⟩ := GlobalTheory.T.regular_fn_unit_near_generization Z Cn φ hC hL x V0 g0 hxV0 hregg hgen'
  have ha := GlobalTheory.T.regular_fn_agree_on_overlap Z Cn φ hC U V (resG Z.X hUU0 f0) (resG Z.X hVV0 g0) (hreg0.resG hUU0) (hregg.resG hVV0)
    (fun q hq hq' hd => ⟨hcod q hq hd, hcodV q hq' hd⟩) x hx hxV
  have ha' : Associated ((Z.X.presheaf.germ U x hx).hom (resG Z.X hUU0 f0))
      ((Z.X.presheaf.germ V0 x hxV0).hom g0) := by
    rw [germ_resG (X := Z.X) hVV0 x hxV g0] at ha
    exact ha
  exact TraitOrdPt.of_associated hx hxV0 ha' hgx

end GlobalTheory.TorRef
