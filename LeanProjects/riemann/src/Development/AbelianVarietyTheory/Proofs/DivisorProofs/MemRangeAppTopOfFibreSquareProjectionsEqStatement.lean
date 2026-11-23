import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppTopOfFibreSquareProjectionsEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_appTop_of_fibreSquare_projections_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → IsIntegral S → Function.Injective π.appTop.hom → ∀ x : Γ(S, ⊤), (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom := by
  first | exact @GlobalTheory.Mum.mem_range_appTop_of_fst_eq_snd | exact GlobalTheory.Mum.mem_range_appTop_of_fst_eq_snd | (intros; apply GlobalTheory.Mum.mem_range_appTop_of_fst_eq_snd <;> assumption)
