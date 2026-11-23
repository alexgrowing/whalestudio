import Mathlib

open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section

variable (ρ : Representation ℂ G E) (ι : E →ₗ[ℂ] H) (T : Submodule ℂ E)

def orbitSum (K : Subgroup G) (v : E) (hv : (Set.range fun k : K => ρ k v).Finite) : E :=
  ∑ w ∈ hv.toFinset, w

variable {ρ}

theorem orbitSum_mem {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite)
    {Y : Submodule ℂ E} (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hvY : v ∈ Y) : orbitSum ρ K v hv ∈ Y := by
  refine Submodule.sum_mem _ fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  obtain ⟨k, rfl⟩ := hw
  exact hY _ _ hvY

theorem orbitSum_fixed {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite)
    (k : K) : ρ k (orbitSum ρ K v hv) = orbitSum ρ K v hv := by
  unfold orbitSum
  rw [map_sum]
  refine Finset.sum_nbij' (fun w => ρ k w) (fun w => ρ (k⁻¹ : K) w) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨k', rfl⟩ := hw
    exact ⟨k * k', by show ρ ((k * k' : K) : G) v = _; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  · intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨k', rfl⟩ := hw
    exact ⟨k⁻¹ * k', by show ρ ((k⁻¹ * k' : K) : G) v = _; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  · intro w _
    change ρ ((k⁻¹ : K) : G) (ρ k w) = w
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  · intro w _
    change ρ (k : G) (ρ ((k⁻¹ : K) : G) w) = w
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel, map_one, Module.End.one_apply]

theorem card_orbit_pos {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite) :
    0 < hv.toFinset.card :=
  Finset.card_pos.2 ⟨v, by rw [Set.Finite.mem_toFinset]; exact ⟨1, by simp⟩⟩

end

variable {ρ : Representation ℂ G E} {ι : E →ₗ[ℂ] H} {T : Submodule ℂ E} {φ : E}

theorem mem_of_stable_of_eigen
    (hT : T = Submodule.span ℂ (Set.range fun g : G => ρ g φ))
    (hinj : ∀ v ∈ T, ι v = 0 → v = 0)
    (hunit : ∀ g : G, ∀ v ∈ T, ∀ w ∈ T, ⟪ι (ρ g v), ι (ρ g w)⟫_ℂ = ⟪ι v, ι w⟫_ℂ)
    (K : Subgroup G) (hφK : ∀ k : K, ρ k φ = φ)
    (horb : ∀ v ∈ T, (Set.range fun k : K => ρ k v).Finite)
    (hfd : FiniteDimensional ℂ ↥(T ⊓ Representation.invariants (ρ.comp K.subtype)))
    {J : Type*} (S : J → Finset G) (ev : J → ℂ) (hφS : ∀ j, ∑ g ∈ S j, ρ g φ = ev j • φ)
    (hP : ∀ z ∈ T, (∀ k : K, ρ k z = z) → (∀ j, ∑ g ∈ S j, ρ g z = ev j • z) → ∃ c : ℂ, z = c • φ)
    (Y : Submodule ℂ E) (hYT : Y ≤ T) (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hY0 : Y ≠ ⊥) : φ ∈ Y := by
  have hφT : φ ∈ T := by rw [hT]; exact Submodule.subset_span ⟨1, by simp⟩
  have hTg : ∀ g, ∀ v ∈ T, ρ g v ∈ T := by
    intro g v hv
    rw [hT] at hv ⊢
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, by show ρ (g * h) φ = _; rw [map_mul, Module.End.mul_apply]⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

  have hadj : ∀ g, ∀ v ∈ T, ∀ w ∈ T, ⟪ι v, ι (ρ g w)⟫_ℂ = ⟪ι (ρ g⁻¹ v), ι w⟫_ℂ := by
    intro g v hv w hw
    rw [← hunit g⁻¹ v hv _ (hTg g w hw), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]

  have havg : ∀ z ∈ T, (∀ k : K, ρ k z = z) → ∀ v (hv : v ∈ T),
      ⟪ι z, ι (orbitSum ρ K v (horb v hv))⟫_ℂ = ((horb v hv).toFinset.card : ℂ) * ⟪ι z, ι v⟫_ℂ := by
    intro z hz hzK v hv
    unfold orbitSum
    rw [map_sum, inner_sum, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Set.Finite.mem_toFinset] at hw
    obtain ⟨k, rfl⟩ := hw
    rw [hadj _ z hz v hv, ← Subgroup.coe_inv, hzK k⁻¹]

  obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  have hyT := hYT hyY
  obtain ⟨g, hg⟩ : ∃ g : G, ⟪ι φ, ι (ρ g y)⟫_ℂ ≠ 0 := by
    by_contra! hall
    have horth : ∀ t ∈ T, ⟪ι t, ι y⟫_ℂ = 0 := by
      intro t ht
      rw [hT] at ht
      induction ht using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        have := hall h⁻¹
        rw [hadj _ φ hφT y hyT, inv_inv] at this
        exact this
      | zero => rw [map_zero, inner_zero_left]
      | add x x' _ _ hx hx' => rw [map_add, inner_add_left, hx, hx', add_zero]
      | smul c x _ hx => rw [map_smul, inner_smul_left, hx, mul_zero]
    exact hy0 (hinj y hyT (inner_self_eq_zero.1 (horth y hyT)))
  set y' := ρ g y
  have hy'Y : y' ∈ Y := hY g y hyY
  have hy'T : y' ∈ T := hYT hy'Y
  set s := orbitSum ρ K y' (horb y' hy'T)
  have hsY : s ∈ Y := orbitSum_mem _ hY hy'Y
  have hsK : ∀ k : K, ρ k s = s := orbitSum_fixed _
  have hφs : ⟪ι φ, ι s⟫_ℂ ≠ 0 := by
    rw [havg φ hφT hφK y' hy'T]
    exact mul_ne_zero (Nat.cast_ne_zero.2 (card_orbit_pos _).ne') hg

  set M : Submodule ℂ E := Y ⊓ (T ⊓ Representation.invariants (ρ.comp K.subtype))
  have hMfd : FiniteDimensional ℂ M :=
    Submodule.finiteDimensional_of_le (inf_le_right : M ≤ T ⊓ Representation.invariants (ρ.comp K.subtype))
  set Mι : Submodule ℂ H := M.map ι
  have hMιfd : FiniteDimensional ℂ Mι := inferInstance
  haveI : CompleteSpace Mι := FiniteDimensional.complete ℂ Mι
  obtain ⟨u, huM, w, hw, hφw⟩ := Mι.exists_add_mem_mem_orthogonal (ι φ)
  obtain ⟨m, hmM, hmP⟩ := Submodule.mem_map.1 huM
  have hmY : m ∈ Y := hmM.1
  have hmT : m ∈ T := hmM.2.1
  have hmK : ∀ k : K, ρ k m = m := fun k => hmM.2.2 k
  set z := φ - m
  have hzT : z ∈ T := sub_mem hφT hmT
  have hzK : ∀ k : K, ρ k z = z := fun k => by rw [map_sub, hφK, hmK]
  have hzι : ι z ∈ Mιᗮ := by
    rw [map_sub, hmP, hφw, add_sub_cancel_left]
    exact hw

  have hzY : ∀ v ∈ Y, ⟪ι z, ι v⟫_ℂ = 0 := by
    intro v hvY
    have hvT := hYT hvY
    have hsv : orbitSum ρ K v (horb v hvT) ∈ M :=
      ⟨orbitSum_mem _ hY hvY, orbitSum_mem _ hTg hvT, fun k => orbitSum_fixed _ k⟩
    have h0 : ⟪ι z, ι (orbitSum ρ K v (horb v hvT))⟫_ℂ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.mem_map_of_mem hsv) hzι
    rw [havg z hzT hzK v hvT] at h0
    exact (mul_eq_zero.1 h0).resolve_left (Nat.cast_ne_zero.2 (card_orbit_pos _).ne')

  have hzE : ∀ j, ∑ g ∈ S j, ρ g z = ev j • z := by
    intro j
    set D := ∑ g ∈ S j, ρ g z - ev j • z
    have hDY : D ∈ Y := by
      have e : D = -(∑ g ∈ S j, ρ g m - ev j • m) := by
        simp only [D, z, map_sub, Finset.sum_sub_distrib, hφS, smul_sub]
        abel
      rw [e]
      exact neg_mem (sub_mem (Submodule.sum_mem _ fun g _ => hY g m hmY) (Submodule.smul_mem _ _ hmY))
    have hDT := hYT hDY
    have hDorth : ∀ v ∈ Y, ⟪ι D, ι v⟫_ℂ = 0 := by
      intro v hvY
      have hvT := hYT hvY
      simp only [D, map_sub, map_sum, map_smul, inner_sub_left, sum_inner, inner_smul_left, hzY v hvY,
        mul_zero, sub_zero]
      refine Finset.sum_eq_zero fun g _ => ?_
      rw [← hunit g⁻¹ _ (hTg g z hzT) v hvT, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
      exact hzY _ (hY _ _ hvY)
    have := hinj D hDT (inner_self_eq_zero.1 (hDorth D hDY))
    exact sub_eq_zero.1 this

  obtain ⟨c, hc⟩ := hP z hzT hzK hzE
  have hzs := hzY s hsY
  rw [hc, map_smul, inner_smul_left] at hzs
  have hc0 : c = 0 := by
    have := (mul_eq_zero.1 hzs).resolve_right hφs
    simpa using this
  have hz0 : z = 0 := by rw [hc, hc0, zero_smul]
  have : φ = m := sub_eq_zero.1 hz0
  rw [this]
  exact hmY

end GL2Classical

end

end GroundTheory.Automorphic
