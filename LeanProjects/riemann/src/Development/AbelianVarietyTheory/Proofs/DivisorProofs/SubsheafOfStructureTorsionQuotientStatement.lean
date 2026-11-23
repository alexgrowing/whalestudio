import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsheafOfStructureTorsionQuotient
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsheaf_of_structure_torsion_quotient : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → ∀ (F : T.Modules), QCoh.IsFiniteQC F → 0 < genRank F → ∃ (M : T.Modules) (f : M ⟶ structureModule T) (g : M ⟶ F), QCoh.IsFiniteQC M ∧ Mono f ∧ Mono g ∧ genRank (cokernel f) = 0 := by
  first | exact @GlobalTheory.exists_sub_mono_structure_of_genRank_pos | exact GlobalTheory.exists_sub_mono_structure_of_genRank_pos | (intros; apply GlobalTheory.exists_sub_mono_structure_of_genRank_pos <;> assumption)
