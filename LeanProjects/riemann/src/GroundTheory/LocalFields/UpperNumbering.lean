import Mathlib
import GroundTheory.LocalFields.HerbrandFunction
import GroundTheory.LocalFields.LowerIndexQuotient

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

theorem enatMin_min (n N : ℕ∞) (a : ℝ) : enatMin (min n N) a = enatMin n (enatMin N a) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe k =>
    induction N using ENat.recTopCoe with
    | top => simp
    | coe l =>
      rw [← (Nat.mono_cast (α := ℕ∞)).map_min, enatMin_coe, enatMin_coe, enatMin_coe, Nat.cast_min,
        min_assoc]

theorem natCast_toNat_min (n : ℕ∞) (m : ℕ) : (((min n m).toNat : ℕ) : ℕ∞) = min n m :=
  ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top m) (min_le_right _ _))

theorem cast_toNat_min (n : ℕ∞) (m : ℕ) : (((min n m).toNat : ℕ) : ℝ) = enatMin n m := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe k =>
    rw [← (Nat.mono_cast (α := ℕ∞)).map_min, ENat.toNat_natCast, enatMin_coe, Nat.cast_min]

section Fiber

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (M : IntermediateField K L) [Normal K M]

open Classical in

theorem sum_filter_restrictNormalHom_eq {β : Type*} [AddCommMonoid β] [Fintype (L ≃ₐ[K] L)]
    [Fintype (L ≃ₐ[M] L)] (F : (L ≃ₐ[K] L) → β) (σ : L ≃ₐ[K] L) :
    ∑ ρ ∈ Finset.univ.filter
        (fun ρ ↦ AlgEquiv.restrictNormalHom M ρ = AlgEquiv.restrictNormalHom M σ), F ρ =
      ∑ τ : L ≃ₐ[M] L, F (σ * τ.restrictScalars K) := by
  symm
  refine Finset.sum_bij (fun τ _ ↦ σ * τ.restrictScalars K) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro τ _
    rw [Finset.mem_filter, map_mul, restrictNormalHom_restrictScalars, mul_one]
    exact ⟨Finset.mem_univ _, rfl⟩
  · intro a _ b _ hab
    exact AlgEquiv.restrictScalars_injective K (mul_left_cancel hab)
  · intro ρ hρ
    obtain ⟨τ, hτ⟩ := exists_eq_mul_restrictScalars_of_restrictNormalHom_eq M
      (Finset.mem_filter.mp hρ).2
    exact ⟨τ, Finset.mem_univ _, hτ⟩

end Fiber

section QuotientMap

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]

end QuotientMap

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem mem_lowerRamificationGroupReal_of_lowerIndex_le {t : ℝ} {σ σ' : L ≃ₐ[K] L}
    (h : σ ∈ lowerRamificationGroupReal K L t) (hle : lowerIndex K L σ ≤ lowerIndex K L σ') :
    σ' ∈ lowerRamificationGroupReal K L t := by
  rw [lowerRamificationGroupReal, mem_lowerRamificationGroup_iff_lowerIndex] at h ⊢
  exact h.trans hle

variable [IsGalois K L] (M : IntermediateField K L) [IsGalois K M]

theorem exists_lowerIndex_eq_herbrandPhi (σ : L ≃ₐ[K] L) :
    ∃ σ₀ : L ≃ₐ[K] L,
      AlgEquiv.restrictNormalHom M σ₀ = AlgEquiv.restrictNormalHom M σ ∧
      (∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ * τ.restrictScalars K) ≤ lowerIndex K L σ₀) ∧
      (∀ τ : L ≃ₐ[M] L, lowerIndex K L (σ₀ * τ.restrictScalars K) =
        min (lowerIndex M L τ) (lowerIndex K L σ₀)) ∧
      (AlgEquiv.restrictNormalHom M σ = 1 → lowerIndex K L σ₀ = ⊤) ∧
      (AlgEquiv.restrictNormalHom M σ ≠ 1 → ∃ m k : ℕ, lowerIndex K L σ₀ = m ∧
        lowerIndex K M (AlgEquiv.restrictNormalHom M σ) = k ∧
        (k : ℝ) = herbrandPhi M L ((m : ℝ) - 1) + 1) := by
  obtain ⟨τ₀, hmax, hmin⟩ := exists_lowerIndex_mul_eq_min M σ
  set σ₀ := σ * τ₀.restrictScalars K with hσ₀
  have hres : AlgEquiv.restrictNormalHom M σ₀ = AlgEquiv.restrictNormalHom M σ := by
    rw [hσ₀, map_mul, restrictNormalHom_restrictScalars, mul_one]
  refine ⟨σ₀, hres, hmax, hmin, ?_, ?_⟩
  · intro h1
    obtain ⟨τ', hτ'⟩ := exists_eq_mul_restrictScalars_of_restrictNormalHom_eq M (σ := 1) (ρ := σ)
      (by rw [h1, map_one])
    have hm : τ'.restrictScalars K * (τ'⁻¹).restrictScalars K = 1 :=
      AlgEquiv.ext fun x ↦ τ'.apply_symm_apply x
    have := hmax τ'⁻¹
    rwa [← hτ', one_mul, hm, lowerIndex_one, top_le_iff] at this
  · intro hs
    have hσ₀1 : σ₀ ≠ 1 := fun h ↦ hs (by rw [← hres, h, map_one])
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (lowerIndex_ne_top hσ₀1)
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (lowerIndex_ne_top hs)
    refine ⟨m, k, hm.symm, hk.symm, ?_⟩
    have hsum := ramificationIndex_mul_lowerIndex_restrictNormalHom M σ₀
    rw [hres, ← hk] at hsum
    simp_rw [hmin, ← hm] at hsum
    have hconv : (∑ τ : L ≃ₐ[M] L, min (lowerIndex M L τ) (m : ℕ∞)) =
        ((∑ τ : L ≃ₐ[M] L, (min (lowerIndex M L τ) (m : ℕ∞)).toNat : ℕ) : ℕ∞) := by
      rw [Nat.cast_sum]
      simp_rw [natCast_toNat_min]
    rw [hconv, ← Nat.cast_mul, Nat.cast_inj] at hsum
    have hsumR : (ramificationIndex M L : ℝ) * k =
        ∑ τ : L ≃ₐ[M] L, enatMin (lowerIndex M L τ) (m : ℝ) := by
      simp_rw [← cast_toNat_min]
      exact_mod_cast hsum
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    have hphi := herbrandPhi_eq_sum_lowerIndex (K := M) (L := L) (u := (m : ℝ) - 1) (by linarith)
    rw [sub_add_cancel, card_lowerRamificationGroup_zero M L, ← hsumR] at hphi
    have he : (0 : ℝ) < ramificationIndex M L := by exact_mod_cast ramificationIndex_pos M L
    rw [hphi]
    field_simp
    ring

theorem sum_enatMin_lowerIndex_coset (σ : L ≃ₐ[K] L) {u : ℝ} (hu : -1 ≤ u) :
    ∑ τ : L ≃ₐ[M] L, enatMin (lowerIndex K L (σ * τ.restrictScalars K)) (u + 1) =
      ramificationIndex M L *
        enatMin (lowerIndex K M (AlgEquiv.restrictNormalHom M σ)) (herbrandPhi M L u + 1) := by
  classical
  obtain ⟨σ₀, hres, -, hmin, h1, hne⟩ := exists_lowerIndex_eq_herbrandPhi M σ
  have hre : ∑ τ : L ≃ₐ[M] L, enatMin (lowerIndex K L (σ * τ.restrictScalars K)) (u + 1) =
      ∑ τ : L ≃ₐ[M] L, enatMin (lowerIndex K L (σ₀ * τ.restrictScalars K)) (u + 1) := by
    rw [← sum_filter_restrictNormalHom_eq M (fun ρ ↦ enatMin (lowerIndex K L ρ) (u + 1)) σ,
      ← sum_filter_restrictNormalHom_eq M (fun ρ ↦ enatMin (lowerIndex K L ρ) (u + 1)) σ₀, hres]
  rw [hre]
  simp_rw [hmin, enatMin_min]
  have he : (0 : ℝ) < ramificationIndex M L := by exact_mod_cast ramificationIndex_pos M L
  have hH : ∀ w : ℝ, 0 ≤ w → ∑ τ : L ≃ₐ[M] L, enatMin (lowerIndex M L τ) w =
      ramificationIndex M L * (herbrandPhi M L (w - 1) + 1) := by
    intro w hw
    rw [herbrandPhi_eq_sum_lowerIndex (K := M) (L := L) (by linarith), sub_add_cancel,
      card_lowerRamificationGroup_zero M L, sub_add_cancel, ← mul_assoc, mul_inv_cancel₀ he.ne',
      one_mul]
  by_cases hs : AlgEquiv.restrictNormalHom M σ = 1
  · rw [h1 hs, enatMin_top, hs, lowerIndex_one, enatMin_top, hH (u + 1) (by linarith),
      add_sub_cancel_right]
  · obtain ⟨m, k, hm, hk, hkφ⟩ := hne hs
    rw [hm, hk, enatMin_coe, enatMin_coe, hH _ (le_min (Nat.cast_nonneg m) (by linarith))]
    have hinner : herbrandPhi M L (min (m : ℝ) (u + 1) - 1) + 1 =
        min (k : ℝ) (herbrandPhi M L u + 1) := by
      rw [← min_sub_sub_right, add_sub_cancel_right,
        (herbrandPhi_strictMono (K := M) (L := L)).monotone.map_min, hkφ, min_add_add_right]
    rw [hinner]

theorem herbrandPhi_comp (u : ℝ) :
    herbrandPhi K M (herbrandPhi M L u) = herbrandPhi K L u := by
  classical
  by_cases hu : -1 ≤ u
  · have hv : -1 ≤ herbrandPhi M L u := by
      rw [← herbrandPhi_of_nonpos (K := M) (L := L) (show (-1 : ℝ) ≤ 0 by norm_num)]
      exact (herbrandPhi_strictMono (K := M) (L := L)).monotone hu
    rw [herbrandPhi_eq_sum_lowerIndex (K := K) (L := M) hv,
      herbrandPhi_eq_sum_lowerIndex (K := K) (L := L) hu]
    have hfib : ∑ σ : L ≃ₐ[K] L, enatMin (lowerIndex K L σ) (u + 1) =
        ∑ s : M ≃ₐ[K] M, (ramificationIndex M L : ℝ) *
          enatMin (lowerIndex K M s) (herbrandPhi M L u + 1) := by
      rw [← Finset.sum_fiberwise Finset.univ (fun σ ↦ AlgEquiv.restrictNormalHom M σ)
        (fun σ ↦ enatMin (lowerIndex K L σ) (u + 1))]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) L s
      rw [sum_filter_restrictNormalHom_eq M (fun ρ ↦ enatMin (lowerIndex K L ρ) (u + 1)) σ,
        sum_enatMin_lowerIndex_coset M σ hu]
    rw [hfib, ← Finset.mul_sum, card_lowerRamificationGroup_zero K L,
      card_lowerRamificationGroup_zero K M, ramificationIndex_tower K M L]
    have h1 : (0 : ℝ) < ramificationIndex K M := by exact_mod_cast ramificationIndex_pos K M
    have h2 : (0 : ℝ) < ramificationIndex M L := by exact_mod_cast ramificationIndex_pos M L
    push_cast
    field_simp
  · have hu0 : u ≤ 0 := by linarith [not_le.mp hu]
    rw [herbrandPhi_of_nonpos (K := M) (L := L) hu0, herbrandPhi_of_nonpos hu0,
      herbrandPhi_of_nonpos hu0]

theorem herbrandPsi_comp (v : ℝ) :
    herbrandPsi M L (herbrandPsi K M v) = herbrandPsi K L v := by
  symm
  rw [herbrandPsi_eq_iff, ← herbrandPhi_comp M, herbrandPhi_herbrandPsi, herbrandPhi_herbrandPsi]

theorem map_lowerRamificationGroupReal (u : ℝ) :
    (lowerRamificationGroupReal K L u).map (AlgEquiv.restrictNormalHom M) =
      lowerRamificationGroupReal K M (herbrandPhi M L u) := by
  ext s
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨σ₀, -, hmax, -, -, hne⟩ := exists_lowerIndex_eq_herbrandPhi M σ
    by_cases hs : AlgEquiv.restrictNormalHom M σ = 1
    · rw [hs]
      exact one_mem _
    obtain ⟨m, k, hm, hk, hkφ⟩ := hne hs
    have hle : lowerIndex K L σ ≤ lowerIndex K L σ₀ := by
      have := hmax 1
      rwa [show σ * (1 : L ≃ₐ[M] L).restrictScalars K = σ from AlgEquiv.ext fun _ ↦ rfl] at this
    have hσ₀ := mem_lowerRamificationGroupReal_of_lowerIndex_le hσ hle
    rw [mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq hm] at hσ₀
    rw [mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq hk, hkφ, add_le_add_iff_right]
    exact (herbrandPhi_strictMono (K := M) (L := L)).monotone (by linarith)
  · intro hs
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) L s
    obtain ⟨σ₀, hres, -, -, -, hne⟩ := exists_lowerIndex_eq_herbrandPhi M σ
    by_cases h1 : AlgEquiv.restrictNormalHom M σ = 1
    · exact ⟨1, one_mem _, by rw [h1, map_one]⟩
    obtain ⟨m, k, hm, hk, hkφ⟩ := hne h1
    refine ⟨σ₀, ?_, hres⟩
    rw [mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq hm]
    rw [mem_lowerRamificationGroupReal_iff_of_lowerIndex_eq hk, hkφ, add_le_add_iff_right,
      (herbrandPhi_strictMono (K := M) (L := L)).le_iff_le] at hs
    linarith

theorem map_upperRamificationGroup (v : ℝ) :
    (upperRamificationGroup K L v).map (AlgEquiv.restrictNormalHom M) =
      upperRamificationGroup K M v := by
  rw [upperRamificationGroup, map_lowerRamificationGroupReal, ← herbrandPsi_comp M,
    herbrandPhi_herbrandPsi]
  rfl

section Quotient

variable (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]

end Quotient

end GroundTheory.LocalField
