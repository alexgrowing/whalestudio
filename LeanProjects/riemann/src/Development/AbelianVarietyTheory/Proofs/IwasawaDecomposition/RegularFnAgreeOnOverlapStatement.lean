import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularFnAgreeOnOverlap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_fn_agree_on_overlap : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)), HasCones Cn Z → ∀ (U V : Z.X.Opens) (f : Γ(Z.X, U)) (g : Γ(Z.X, V)), IsRegularFn f → IsRegularFn g → (∀ q, q ∈ U → q ∈ V → ringKrullDim (Z.X.presheaf.stalk q) ≤ 1 → TraitOrdPt φ Z U f q ∧ TraitOrdPt φ Z V g q) → ∀ (x : Z.X) (hx : x ∈ U) (hx' : x ∈ V), Associated ((Z.X.presheaf.germ U x hx).hom f) ((Z.X.presheaf.germ V x hx').hom g) := by
  first | exact @GlobalTheory.TorRef.associated_germ_of_traitOrdPt | exact GlobalTheory.TorRef.associated_germ_of_traitOrdPt | (intros; apply GlobalTheory.TorRef.associated_germ_of_traitOrdPt <;> assumption)
