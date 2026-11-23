import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSocleOverOfSimple
open scoped Topology

namespace GlobalTheory

theorem finite_orbit_of_fixed_near_one {H V : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [AddCommGroup V] [Module ℂ V] (ρ : H →* Module.End ℂ V) (K : Subgroup H) (hK : IsCompact (K : Set H)) (x : V)
    (hx : ∃ U ∈ 𝓝 (1 : H), ∀ h ∈ U, h ∈ K → ρ h x = x) : {y | ∃ k ∈ K, ρ k x = y}.Finite := by
  obtain ⟨U, hU, hUx⟩ := hx
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Subgroup K :=
    { carrier := {k | ρ (k : H) x = x}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at ha hb ⊢
        rw [hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : ρ ((a : H)⁻¹) (ρ (a : H) x) = x := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rw [ha] at h1
        simpa using h1 }
  have hSn : (S : Set K) ∈ 𝓝 (1 : K) := by
    have : (Subtype.val : K → H) ⁻¹' U ∈ 𝓝 (1 : K) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hU)
    refine Filter.mem_of_superset this ?_
    intro k hk
    exact hUx k hk k.2
  have hSo : IsOpen (S : Set K) := Subgroup.isOpen_of_mem_nhds S hSn
  haveI : Finite (K ⧸ S) := Subgroup.quotient_finite_of_isOpen S hSo
  refine (Set.finite_range (fun q : K ⧸ S => ρ ((Quotient.out q : K) : H) x)).subset ?_
  rintro y ⟨k, hk, rfl⟩
  refine ⟨(QuotientGroup.mk (⟨k, hk⟩ : K) : K ⧸ S), ?_⟩
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (⟨k, hk⟩ : K)
  simp only
  rw [hs, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  have : ρ ((s : K) : H) x = x := s.2
  rw [this]

end GlobalTheory
