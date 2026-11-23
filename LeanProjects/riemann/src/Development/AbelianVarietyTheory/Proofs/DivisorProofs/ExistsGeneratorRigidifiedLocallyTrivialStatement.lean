import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorRigidifiedLocallyTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_rigidified_locally_trivial : ∀ (T : Scheme.{0}) (A' : Over T) [GrpObj A'] (N : LB A'.left), IsAbelianScheme A' → N.IsLB → Out.Rigidified A' N → (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ ∃ s : (N.pull (A'.hom ⁻¹ᵁ V).ι).Gen, s.IsGen) → ∃ s : N.Gen, s.IsGen := by
  first | exact @GlobalTheory.RigTriv.exists_gen_of_locally_trivial | exact GlobalTheory.RigTriv.exists_gen_of_locally_trivial | (intros; apply GlobalTheory.RigTriv.exists_gen_of_locally_trivial <;> assumption)
