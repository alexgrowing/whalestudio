import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionHodgeSubspaceConstantLiftMemFil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieConditionHodgeSubspace_constant_lift_mem_fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ z ∈ GlobalTheory.HTCount.lieZ o₀ β, z ∈ Fil o₀.A ∧ IsFilLift m'.cart z 0 := by
  first | (exact @GlobalTheory.HTCount.lieZ_mem_fil_and_lift) | (exact GlobalTheory.HTCount.lieZ_mem_fil_and_lift) | (intros; apply GlobalTheory.HTCount.lieZ_mem_fil_and_lift <;> assumption)
