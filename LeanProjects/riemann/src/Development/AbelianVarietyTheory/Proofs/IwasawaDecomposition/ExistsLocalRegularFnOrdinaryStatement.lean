import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalRegularFnOrdinary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_regular_fn_ordinary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)), HasCones Cn Z → HasLinForms Cn φ → ∀ z : Z.X, ∃ (U : Z.X.Opens) (_ : z ∈ U) (f : Γ(Z.X, U)), IsRegularFn f ∧ TraitOrdPt φ Z U f z ∧ ∀ q ∈ U, q ⤳ z → ringKrullDim (Z.X.presheaf.stalk q) ≤ 1 → TraitOrdPt φ Z U f q := by
  first | exact @GlobalTheory.TorRef.exists_regularFn_traitOrdPt_chart | exact GlobalTheory.TorRef.exists_regularFn_traitOrdPt_chart | (intros; apply GlobalTheory.TorRef.exists_regularFn_traitOrdPt_chart <;> assumption)
