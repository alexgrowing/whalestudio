import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtFibreSpreadModelAtFieldPoint
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaPt_fibre_spread_model_at_fieldPoint : ∀ (F Ω T : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [CommRing T] [IsDomain T] [Algebra F T] (em : F →+* Ω) (jT : T →+* Ω) (t : T →ₐ[F] F), Algebra.FiniteType F T → Function.Injective jT → jT.comp (algebraMap F T) = em → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (m : ℕ) (I : Type) (x : I → (baseOver (Sp Ω) ⟶ A.A)) (y : I → (baseOver (Sp T) ⟶ P.A)) (v : I → F), Odd m → 3 ≤ m → (∀ i, (x i).left ≫ φ = spMap jT ≫ (y i).left) → (∀ i, y i ^ (m ^ 2) = 1) → (∀ z : Over.mk (spMap t.toRingHom) ⟶ P.A, z ^ m = 1 → ∃ i, ((Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫ y i) ^ m = z) → IsThetaPt A m x (fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → IsThetaPt P m (fun i => (Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫ y i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (v i)) := by
  first | exact @GlobalTheory.Mum.isThetaPt_fibre | exact GlobalTheory.Mum.isThetaPt_fibre | (intros; apply GlobalTheory.Mum.isThetaPt_fibre <;> assumption)
