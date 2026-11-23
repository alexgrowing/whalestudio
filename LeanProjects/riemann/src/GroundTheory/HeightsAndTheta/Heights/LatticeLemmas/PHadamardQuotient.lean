import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Module Submodule
open GroundTheory.Heights₂.Heights

universe u v w

noncomputable section

namespace HadamardQuotient

theorem exists_subfamily_card_eq_finrank {R M : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (F : Submodule R M)
    {ι : Type*} (x : ι → M) (hx : finrank R (span R (Set.range x)) = finrank R M) :
    ∃ s : Set ι, LinearIndepOn R (F.mkQ ∘ x) s ∧ Finite s ∧ Nat.card s = finrank R (M ⧸ F) := by
  classical
  set y : ι → M ⧸ F := F.mkQ ∘ x with hy_def
  obtain ⟨s, hs, hmax⟩ := exists_maximal_linearIndepOn R y
  have hfin : Finite s := LinearIndependent.finite_of_isNoetherian hs
  set S : Submodule R (M ⧸ F) := span R (y '' s) with hS_def

  have hy : ∀ i, S.mkQ (y i) ∈ torsion R ((M ⧸ F) ⧸ S) := by
    intro i
    by_cases hi : i ∈ s
    · have h0 : S.mkQ (y i) = 0 :=
        (Submodule.Quotient.mk_eq_zero S).mpr (subset_span ⟨i, hi, rfl⟩)
      rw [h0]
      exact zero_mem _
    · obtain ⟨a, ha, h⟩ := hmax i hi
      refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
      change a • S.mkQ (y i) = 0
      rw [← map_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h
  have hspan : span R (Set.range y) ≤ (torsion R ((M ⧸ F) ⧸ S)).comap S.mkQ :=
    span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hy i)

  set N : Submodule R M := span R (Set.range x) with hN_def
  have hN : finrank R (M ⧸ N) = 0 := by
    have h := rank_quotient_add_rank_of_isDomain N
    rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at h
    norm_cast at h
    omega

  have hQS : finrank R ((M ⧸ F) ⧸ S) = 0 := by
    rw [Module.finrank_eq_zero_iff]
    intro q
    obtain ⟨q, rfl⟩ := S.mkQ_surjective q
    obtain ⟨m, rfl⟩ := F.mkQ_surjective q
    obtain ⟨a, ha, ham⟩ := Module.finrank_eq_zero_iff.mp hN (N.mkQ m)
    have h1 : a • m ∈ N := by
      rw [← map_smul, mkQ_apply, Submodule.Quotient.mk_eq_zero] at ham
      exact ham
    have h2 : F.mkQ (a • m) ∈ span R (Set.range y) := by
      have h := Submodule.mem_map_of_mem (f := F.mkQ) h1
      rwa [hN_def, Submodule.map_span, ← Set.range_comp] at h
    obtain ⟨⟨b, hb⟩, hbm⟩ := hspan h2
    refine ⟨b * a, mul_ne_zero (nonZeroDivisors.ne_zero hb) ha, ?_⟩
    change b • S.mkQ (F.mkQ (a • m)) = 0 at hbm
    rw [mul_smul, ← map_smul, ← map_smul, ← map_smul, ← map_smul]
    rw [map_smul, map_smul] at hbm
    rw [map_smul, map_smul]
    exact hbm
  have hadd := rank_quotient_add_rank_of_isDomain S
  rw [← finrank_eq_rank, ← finrank_eq_rank, ← finrank_eq_rank] at hadd
  norm_cast at hadd
  have := Fintype.ofFinite s
  have hSr : finrank R S = Nat.card s := by
    rw [hS_def, Set.image_eq_range, Nat.card_eq_fintype_card]
    exact finrank_span_eq_card hs
  exact ⟨s, hs, hfin, by omega⟩

variable {K : Type*} [Field K] [NumberField K]

theorem normAt_mkQ_le (M : HermitianBundle K) (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F)
    (σ : K →+* ℂ) (x : M.carrier) :
    (M.quot F hF).normAt σ (F.mkQ x) ≤ M.normAt σ x := by
  have h := HermitianBundle.quot_norm_eq_iInf M F hF σ
    ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (F.mkQ x : M.carrier ⧸ F))
  refine (le_of_eq h).trans ?_
  exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩
    (⟨(1 : ComplexAt σ) ⊗ₜ[𝓞 K] x, rfl⟩ :
      {y : Fibre σ M.carrier // F.mkQ.lTensor (ComplexAt σ) y = (1 : ComplexAt σ) ⊗ₜ[𝓞 K] F.mkQ x})

end HadamardQuotient

theorem HadamardQuotient.proof (h1 : Hadamard.Statement.{u, v, w}) :
    HadamardQuotient.Statement.{u, v, w} := by
  intro K _ _ M F hF ι x La hx hLa
  obtain ⟨s, hs, hfin, hcard⟩ := exists_subfamily_card_eq_finrank F x hx
  have := Fintype.ofFinite s
  exact h1 K (M.quot F hF) (ι := s) (fun i ↦ F.mkQ (x i)) La hs
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
    (fun i σ ↦ (normAt_mkQ_le M F hF σ (x i)).trans (hLa i σ))

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
