import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharacterCocycleDescent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_character_cocycle_descent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (x : Sp R ⟶ X) (q : ℕ) (B : Type) [CommRing B] [Algebra R B] (u : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G), IsFinPart t x q u → ∀ κ : (B →ₐ[R] R) → Rˣ, (∀ (σ σ' σ'' : B →ₐ[R] R) (w w' : Over.mk (spMap (RingHom.id R) ≫ x) ⟶ t.G), spMap σ.toRingHom ≫ u.left = w.left → spMap σ'.toRingHom ≫ u.left = w'.left → spMap σ''.toRingHom ≫ u.left = (w * w').left → κ σ'' = κ σ * κ σ') → ∃ b : Bˣ, (∀ σ : B →ₐ[R] R, σ (b : B) = (κ σ : R)) ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (w w' : Over.mk (spMap φ ≫ x) ⟶ t.G) (β β' β'' : B →+* S), β.comp (algebraMap R B) = φ → β'.comp (algebraMap R B) = φ → β''.comp (algebraMap R B) = φ → spMap β ≫ u.left = w.left → spMap β' ≫ u.left = w'.left → spMap β'' ≫ u.left = (w * w').left → β'' (b : B) = β (b : B) * β' (b : B) := by
  first | exact @GlobalTheory.LineNorm.exists_groupLike_unit_of_isFinPart | exact GlobalTheory.LineNorm.exists_groupLike_unit_of_isFinPart | (intros; apply GlobalTheory.LineNorm.exists_groupLike_unit_of_isFinPart <;> assumption)
