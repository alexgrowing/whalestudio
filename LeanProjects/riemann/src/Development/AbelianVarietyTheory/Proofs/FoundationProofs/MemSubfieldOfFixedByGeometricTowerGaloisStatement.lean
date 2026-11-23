import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSubfieldOfFixedByGeometricTowerGalois
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraMapZpInjective
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_subfield_of_fixed_by_geometric_tower_galois : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (F : Subfield Ω), (∀ c : O0 p, algebraMap (O0 p) Ω c ∈ F) → (∀ x : Ω, IsAlgZp p x → x ∈ F) → T.qq n ∈ F → ∀ o : Ω, (∀ g ∈ Ggeo p Ω ⊓ Gn T n, g o = o) → o ∈ F := by
  first | exact @GlobalTheory.GeoFix.mem_of_fixed_ggeo_gn | exact GlobalTheory.GeoFix.mem_of_fixed_ggeo_gn | (intros; apply GlobalTheory.GeoFix.mem_of_fixed_ggeo_gn <;> assumption)
