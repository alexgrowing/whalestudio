import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularFnUnitNearGenerization
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_fn_unit_near_generization : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)), HasCones Cn Z → HasLinForms Cn φ → ∀ (z : Z.X) (U : Z.X.Opens) (f : Γ(Z.X, U)), z ∈ U → IsRegularFn f → (∀ q ∈ U, q ⤳ z → ringKrullDim (Z.X.presheaf.stalk q) ≤ 1 → TraitOrdPt φ Z U f q) → ∃ (V : Z.X.Opens) (hVU : V ≤ U), z ∈ V ∧ ∀ q ∈ V, ringKrullDim (Z.X.presheaf.stalk q) ≤ 1 → TraitOrdPt φ Z V (resG Z.X hVU f) q := by
  first | exact @GlobalTheory.ShrinkCentre.exists_shrink | exact GlobalTheory.ShrinkCentre.exists_shrink | (intros; apply GlobalTheory.ShrinkCentre.exists_shrink <;> assumption)
