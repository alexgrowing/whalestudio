import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionEqBasePoint
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_eq_basePoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (x : Sp R ⟶ X) (g₀ : Sp S ⟶ t.G.left) (v : Sp (DualNumber R) ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ x → IsTanAtG t x v → IsTranslate t φ g₀ v w → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ := by
  first | exact @GlobalTheory.LogKS.IsTranslate.fst_comp | exact GlobalTheory.LogKS.IsTranslate.fst_comp | (intros; apply GlobalTheory.LogKS.IsTranslate.fst_comp <;> assumption)
