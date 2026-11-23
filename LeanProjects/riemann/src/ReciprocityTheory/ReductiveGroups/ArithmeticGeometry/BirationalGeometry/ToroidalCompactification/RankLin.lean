import Mathlib

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

open Module

variable {V k : Type} [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field k] [Algebra V k] [FaithfulSMul V k]

theorem exists_finset_iInf_le {M : Type} [AddCommGroup M] [Module k M] [FiniteDimensional k M] {O : Type}
    (K : O → Submodule k M) : ∃ F : Finset O, ∀ b, (⨅ a ∈ F, K a) ≤ K b := by
  classical
  obtain ⟨N, ⟨F, rfl⟩, hmin⟩ := (wellFounded_lt (α := Submodule k M)).has_min
    {N | ∃ F : Finset O, N = ⨅ a ∈ F, K a} ⟨⊤, ∅, by simp⟩
  refine ⟨F, fun b => ?_⟩
  have hle : (⨅ a ∈ insert b F, K a) ≤ ⨅ a ∈ F, K a := by
    rw [Finset.iInf_insert]
    exact inf_le_right
  have heq : (⨅ a ∈ insert b F, K a) = ⨅ a ∈ F, K a := by
    by_contra hne
    exact hmin _ ⟨insert b F, rfl⟩ (lt_of_le_of_ne hle hne)
  rw [← heq, Finset.iInf_insert]
  exact inf_le_left

theorem card_le_finrank_of_li {ι' ι : Type} [Fintype ι'] [Fintype ι] (v : ι → ι' → V) (hv : LinearIndependent V v)
    (W : Submodule k (ι' → k)) (hW : ∀ i, (algebraMap V k ∘ v i) ∈ W) : Fintype.card ι ≤ finrank k W := by
  have hk : LinearIndependent k (fun i => algebraMap V k ∘ v i) :=
    linearIndependent_algebraMap_comp_iff.mpr hv
  have hw : LinearIndependent k (fun i => (⟨algebraMap V k ∘ v i, hW i⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hk
  exact hw.fintype_card_le_finrank

theorem exists_li_of_submodule {ι' : Type} [Fintype ι'] [DecidableEq ι'] (N : Submodule V (ι' → V)) :
    ∃ v : Fin (finrank V N) → ι' → V, LinearIndependent V v ∧ ∀ i, v i ∈ N := by
  let b := Module.finBasis V N
  exact ⟨fun i => b i, b.linearIndependent.map' N.subtype (Submodule.ker_subtype N), fun i => (b i).2⟩

private theorem sub_algebraMap_smul_id_apply_algebraMap_comp {n : ℕ} {O : Type} (L : O → (Fin n → V) →ₗ[V] (Fin n → V))
    (Lk : O → (Fin n → k) →ₗ[k] (Fin n → k)) (hL : ∀ a c, Lk a (algebraMap V k ∘ c) = algebraMap V k ∘ L a c)
    (χ : O → V) (a : O) (c : Fin n → V) :
    (Lk a - algebraMap V k (χ a) • (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k))) (algebraMap V k ∘ c) =
      algebraMap V k ∘ ((L a - χ a • (LinearMap.id : (Fin n → V) →ₗ[V] (Fin n → V))) c) := by
  ext i
  have := congrFun (hL a c) i
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Function.comp_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul] at this ⊢
  rw [this]

private theorem finrank_range_le_finrank_range_of_reduction {m : ℕ} {ι' : Type} [Fintype ι'] [DecidableEq ι']
    (B : (Fin m → V) →ₗ[V] (ι' → V)) (Bk : (Fin m → k) →ₗ[k] (ι' → k))
    (h : ∀ c, Bk (algebraMap V k ∘ c) = algebraMap V k ∘ B c) :
    finrank V (LinearMap.range B) ≤ finrank k (LinearMap.range Bk) := by
  obtain ⟨v, hv, hvN⟩ := exists_li_of_submodule (LinearMap.range B)
  have := card_le_finrank_of_li (k := k) v hv (LinearMap.range Bk) (fun i => by
    obtain ⟨c, hc⟩ := hvN i
    exact ⟨algebraMap V k ∘ c, by rw [h, hc]⟩)
  simpa using this

theorem finrank_eig_bc {n : ℕ} {O : Type} (L : O → (Fin n → V) →ₗ[V] (Fin n → V))
    (Lk : O → (Fin n → k) →ₗ[k] (Fin n → k)) (hL : ∀ a c, Lk a (algebraMap V k ∘ c) = algebraMap V k ∘ L a c)
    (χ : O → V) :
    finrank V (⨅ a, LinearMap.ker (L a - χ a • LinearMap.id) : Submodule V (Fin n → V)) =
      finrank k (⨅ a, LinearMap.ker (Lk a - algebraMap V k (χ a) • LinearMap.id) : Submodule k (Fin n → k)) := by
  classical

  have hle : finrank V (⨅ a, LinearMap.ker (L a - χ a • LinearMap.id) : Submodule V (Fin n → V)) ≤
      finrank k (⨅ a, LinearMap.ker (Lk a - algebraMap V k (χ a) • (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k))) :
        Submodule k (Fin n → k)) := by
    obtain ⟨v, hv, hvN⟩ := exists_li_of_submodule
      (⨅ a, LinearMap.ker (L a - χ a • LinearMap.id) : Submodule V (Fin n → V))
    have := card_le_finrank_of_li (k := k) v hv
      (⨅ a, LinearMap.ker (Lk a - algebraMap V k (χ a) • (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k)))) (fun i => by
        have hi := hvN i
        simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hi ⊢
        intro a
        rw [sub_algebraMap_smul_id_apply_algebraMap_comp L Lk hL χ a, hi a]
        ext j
        simp)
    simpa using this

  obtain ⟨F, hF⟩ := exists_finset_iInf_le (k := k)
    (fun a => LinearMap.ker (Lk a - algebraMap V k (χ a) • (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k))))
  let B : (Fin n → V) →ₗ[V] (F × Fin n → V) :=
    LinearMap.pi fun p => (LinearMap.proj p.2).comp (L p.1 - χ p.1 • LinearMap.id)
  let Bk : (Fin n → k) →ₗ[k] (F × Fin n → k) :=
    LinearMap.pi fun p => (LinearMap.proj p.2).comp (Lk p.1 - algebraMap V k (χ p.1) • LinearMap.id)
  have hB : ∀ c, Bk (algebraMap V k ∘ c) = algebraMap V k ∘ B c := by
    intro c
    ext p
    have := congrFun (sub_algebraMap_smul_id_apply_algebraMap_comp L Lk hL χ p.1 c) p.2
    simpa [B, Bk] using this
  have hmemk : ∀ c : Fin n → k, Bk c = 0 ↔ ∀ a ∈ F, (Lk a - algebraMap V k (χ a) • (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k))) c = 0 := by
    intro c
    constructor
    · intro h a ha
      ext j
      exact congrFun h (⟨a, ha⟩, j)
    · intro h
      ext p
      exact congrFun (h p.1 p.1.2) p.2
  have hkerk : LinearMap.ker Bk =
      (⨅ a, LinearMap.ker (Lk a - algebraMap V k (χ a) • (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k))) : Submodule k (Fin n → k)) := by
    ext c
    rw [LinearMap.mem_ker, hmemk]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    constructor
    · intro h b
      have hc : c ∈ ⨅ a ∈ F, LinearMap.ker (Lk a - algebraMap V k (χ a) • (LinearMap.id : (Fin n → k) →ₗ[k] (Fin n → k))) := by
        simp only [Submodule.mem_iInf, LinearMap.mem_ker]
        exact h
      exact hF b hc
    · intro h a _
      exact h a
  have hker : LinearMap.ker B =
      (⨅ a, LinearMap.ker (L a - χ a • LinearMap.id) : Submodule V (Fin n → V)) := by
    ext c
    simp only [LinearMap.mem_ker, Submodule.mem_iInf]
    constructor
    · intro h b
      have h1 : Bk (algebraMap V k ∘ c) = 0 := by
        rw [hB, h]
        ext p
        simp
      have h2 := (LinearMap.mem_ker.2 h1 : _ ∈ LinearMap.ker Bk)
      rw [hkerk] at h2
      simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2
      have h3 := h2 b
      rw [sub_algebraMap_smul_id_apply_algebraMap_comp L Lk hL χ b] at h3
      ext j
      have := congrFun h3 j
      simp only [Function.comp_apply, Pi.zero_apply] at this
      exact (FaithfulSMul.algebraMap_injective V k) (by rw [this, Pi.zero_apply, map_zero])
    · intro h
      ext p
      simp [B, h p.1]
  have hrn : finrank V (LinearMap.range B) + finrank V (LinearMap.ker B) = n := by
    have h := LinearMap.rank_range_add_rank_ker B
    rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, rank_fin_fun] at h
    exact_mod_cast h
  have hrnk := LinearMap.finrank_range_add_finrank_ker Bk
  have hr := finrank_range_le_finrank_range_of_reduction B Bk hB
  rw [hker] at hrn
  rw [hkerk, Module.finrank_fin_fun] at hrnk
  omega

end ReciprocityTheory.ChartRestriction.G.Chart
