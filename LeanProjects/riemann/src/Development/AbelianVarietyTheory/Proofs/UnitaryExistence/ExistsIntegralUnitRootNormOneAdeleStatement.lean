import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralUnitRootNormOneAdele
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unit_root_norm_one_adele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → (∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) → ∀ u ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1 → ∃ x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), (∃ y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), x * y = 1) ∧ x = u * sg (FiniteAdeleRing (𝓞 F) F) c x := by
  first | exact @GlobalTheory.AdLat.exists_integral_unit_root | exact GlobalTheory.AdLat.exists_integral_unit_root | (intros; apply GlobalTheory.AdLat.exists_integral_unit_root <;> assumption)
