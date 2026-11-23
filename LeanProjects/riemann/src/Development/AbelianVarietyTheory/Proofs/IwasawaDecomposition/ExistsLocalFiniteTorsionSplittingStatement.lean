import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFiniteTorsionSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_finite_torsion_splitting : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ X) (q : ℕ), q ≠ 0 → SplitTors t x q → ∀ 𝔭 : Ideal R, 𝔭.IsPrime → ∃ (f : R) (B : Type) (_ : CommRing B) (_ : Algebra (Localization.Away f) B) (u : Over.mk (spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ t.G), f ∉ 𝔭 ∧ IsFinPart t (spMap (algebraMap R (Localization.Away f)) ≫ x) q u ∧ ∀ (k : Type) [Field k] (φ : Localization.Away f →+* k), RingHom.ker (φ.comp (algebraMap R (Localization.Away f))) = 𝔭 → ∀ w : Over.mk (spMap φ ≫ spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ t.G, w ^ q = 1 → Thru t u.left φ w.left := by
  first | exact @GlobalTheory.SplitFinitePart.exists_finite_part | exact GlobalTheory.SplitFinitePart.exists_finite_part | (intros; apply GlobalTheory.SplitFinitePart.exists_finite_part <;> assumption)
