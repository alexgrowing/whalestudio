import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOrbitSmoothVectorFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_orbit_smooth_vector_finite : ∀ {H V : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup V]
    [Module ℂ V] (ρ : H →* Module.End ℂ V) (K : Subgroup H) (hK : IsCompact (K : Set H)) (x : V)
    (hx : ∃ U ∈ 𝓝 (1 : H), ∀ h ∈ U, h ∈ K → ρ h x = x), {y | ∃ k ∈ K, ρ k x = y}.Finite := by
  first | exact @GlobalTheory.finite_orbit_of_fixed_near_one | exact GlobalTheory.finite_orbit_of_fixed_near_one | (intros; apply GlobalTheory.finite_orbit_of_fixed_near_one <;> assumption)
