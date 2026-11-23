import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrderCompatible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trait_order_compatible : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)), HasCones Cn Z → ∀ (U U' : Z.X.Opens) (f : Γ(Z.X, U)) (f' : Γ(Z.X, U')), IsRegularFn f → IsRegularFn f' → TraitOrd φ Z U f → TraitOrd φ Z U' f' → ∀ (x : Z.X) (hx : x ∈ U) (hx' : x ∈ U'), Associated ((Z.X.presheaf.germ U x hx).hom f) ((Z.X.presheaf.germ U' x hx').hom f') := by
  first | exact @GlobalTheory.TorRef.Overlap.associated_germ | exact GlobalTheory.TorRef.Overlap.associated_germ | (intros; apply GlobalTheory.TorRef.Overlap.associated_germ <;> assumption)
