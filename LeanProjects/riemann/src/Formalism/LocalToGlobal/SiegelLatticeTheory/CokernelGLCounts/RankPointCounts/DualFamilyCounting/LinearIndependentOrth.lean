import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem locF_subset_span {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) V) :
    (locF 𝔭 L : Set V) ⊆ Submodule.span K (L : Set V) := by
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp L x).1 hx
  have ht0 : algebraMap F K (t : F) ≠ 0 := by
    rw [← jι_eq']; exact jι_ne_zero (ne_zero_of_notMem ht)
  have h1 : algebraMap F K (t : F) • x ∈ Submodule.span K (L : Set V) := by
    rw [← jι_eq', algebraMap_smul]; exact Submodule.subset_span htx
  exact (Submodule.smul_mem_iff _ ht0).1 h1

theorem le_span_of_locF {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {U : Submodule K V}
    {M : Submodule (𝓞 K) V} (hM : IsLatIn U M) {n : ℕ} {b : Fin n → V}
    (hb : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 M) :
    U ≤ Submodule.span K (Set.range b) := by
  rw [← hM.2, Submodule.span_le]
  intro x hx
  have h1 : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hb]; exact LocF.le_locF 𝔭 M hx
  have h2 := locF_subset_span hp _ h1
  rwa [Submodule.span_span_of_tower] at h2

theorem linearIndependent_orth {m : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (w : Fin m → V)
    (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0) (hwn : ∀ j, h (w j) (w j) ≠ 0) :
    LinearIndependent K w := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h1 := congrArg (h (w k)) hg
  rw [map_sum, map_zero] at h1
  simp only [map_smul, smul_eq_mul] at h1
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [hwo k j (Ne.symm hj), mul_zero])
    (by simp)] at h1
  exact (mul_eq_zero.1 h1).resolve_right (hwn k)

theorem family_top_holds : FamTop := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have hp := h𝔭.isPrime
  obtain ⟨hbU, hbL, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hw : ∀ j, w j ∈ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    fun j => Submodule.subset_span ⟨Sum.inr j, rfl⟩
  have hb : ∀ i, b i ∈ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) := by
    intro i
    have hg' : glueFam K 𝔭 b a π w τ (Sum.inl i) ∈
        Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) := Submodule.subset_span ⟨Sum.inl i, rfl⟩
    simp only [glueFam, Sum.elim_inl] at hg'
    by_cases hi : vF 𝔭 (a i) = 0
    · rwa [if_pos hi] at hg'
    · rw [if_neg hi] at hg'
      have h0 : (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) ≠ 0 := by
        apply pow_ne_zero; apply inv_ne_zero; rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
      have h1 := (Submodule.smul_mem_iff _ h0).1 hg'
      have h2 := Submodule.sub_mem _ h1 (hw (τ i))
      rwa [add_sub_cancel_right] at h2
  have hU : U ≤ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    le_trans (le_span_of_locF hp hM hbL) (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i))
  have hli : LinearIndependent K w := linearIndependent_orth h w hwo fun j => by
    rw [(hwn j).1]; exact (map_ne_zero _).2 (hwn j).2
  have hle : Submodule.span K (Set.range w) ≤ orthK h U :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hwW j)
  have hfr : finrank K (Submodule.span K (Set.range w)) = finrank K (orthK h U) := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hW : orthK h U ≤ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    le_trans (Submodule.eq_of_le_of_finrank_eq hle hfr).ge
      (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hw j))
  rw [eq_top_iff, ← hUc.sup_eq_top]
  exact sup_le hU hW

end Formalism.L2.SG.Pf.GluingBases
