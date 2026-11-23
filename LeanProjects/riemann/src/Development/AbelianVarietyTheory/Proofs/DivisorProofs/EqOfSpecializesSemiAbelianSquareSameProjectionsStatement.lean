import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSemiAbelianSquareSameProjections
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_specializes_semiAbelian_square_same_projections : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) → ∀ p q : (G ⊗ G).left, (fst G G).left p = x → (fst G G).left q = x → (snd G G).left p = (snd G G).left q → p ⤳ q → p = q := by
  first | exact @GlobalTheory.Mum.eq_of_specializes_of_fst_eq_of_snd_eq | exact GlobalTheory.Mum.eq_of_specializes_of_fst_eq_of_snd_eq | (intros; apply GlobalTheory.Mum.eq_of_specializes_of_fst_eq_of_snd_eq <;> assumption)
