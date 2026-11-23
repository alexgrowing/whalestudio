import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.CardUNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.SuperdiagSgnConj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarConvolutionTrace.AveragingOperatorIdempotent

open Finset

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem pi_sgn_mul (π : Representation ℂ (GL (Fin k) F) V) (x : GL (Fin k) F) (v : V) :
    π (sgn k) (π x v) = π (sgn k * x * sgn k) (π (sgn k) v) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, mul_assoc (sgn k * x),
    sgn_mul_self, mul_one]

theorem pi_sgn_sgn (π : Representation ℂ (GL (Fin k) F) V) (v : V) : π (sgn k) (π (sgn k) v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, sgn_mul_self, map_one, Module.End.one_apply]

theorem whit_sgn_projQ (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) (ℓ : Module.Dual ℂ V)
    (hℓ : IsWhit ψ₀ π ℓ) (v : V) : ℓ (π (sgn k) (projQ ψ₀ π v)) = ℓ (π (sgn k) v) := by
  have hterm : ∀ x : GL (Fin k) F, psiNat ψ₀ x * ℓ (π (sgn k) (π x v)) =
      (if IsUni k x then (1 : ℂ) else 0) * ℓ (π (sgn k) v) := by
    intro x
    rw [pi_sgn_mul]
    by_cases hx : IsUni k x
    · rw [hℓ _ (isUni_sgn_conj hx), ← mul_assoc, if_pos hx]
      unfold psiNat
      rw [if_pos hx, mul_comm (psiU ψ₀ x), psiU_sgn_conj]
    · unfold psiNat; rw [if_neg hx, if_neg hx, zero_mul, zero_mul]
  unfold projQ
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, smul_eq_mul]
  simp_rw [hterm]
  rw [← Finset.sum_mul, sum_boole_uni, ← mul_assoc, inv_mul_cancel₀ (cardU_ne_zero F k), one_mul]

theorem isWhit_of_dual (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) (f : Module.Dual ℂ V) :
    IsWhit ψ₀ π (f ∘ₗ (projQ ψ₀ π ∘ₗ π (sgn k))) := by
  intro u hu v
  have hq := LinearMap.congr_fun (projQ_comp_pi ψ₀ π (isUni_sgn_conj hu)) (π (sgn k) v)
  simp only [LinearMap.comp_apply] at hq ⊢
  rw [pi_sgn_mul, hq, LinearMap.smul_apply, map_smul, smul_eq_mul,
    inv_eq_of_mul_eq_one_right (psiU_sgn_conj ψ₀ u)]

theorem generic_iff_criterion : GenericIff := by
  intro F _ _ k ψ₀ V _ _ π
  constructor
  · rintro ⟨ℓ, hne, hw⟩ hQ
    apply hne
    ext v
    have := whit_sgn_projQ ψ₀ π ℓ hw (π (sgn k) v)
    rw [hQ, LinearMap.zero_apply, map_zero, map_zero, pi_sgn_sgn] at this
    rw [← this, LinearMap.zero_apply]
  · intro hQ
    obtain ⟨v, hv⟩ : ∃ v, projQ ψ₀ π v ≠ 0 := by
      by_contra h
      push_neg at h
      exact hQ (LinearMap.ext h)
    obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f (projQ ψ₀ π v) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
    refine ⟨f ∘ₗ (projQ ψ₀ π ∘ₗ π (sgn k)), ?_, isWhit_of_dual ψ₀ π f⟩
    intro h0
    apply hf
    have := LinearMap.congr_fun h0 (π (sgn k) v)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, pi_sgn_sgn] at this
    exact this

theorem intertwiner_rank_le_one : RankLeOne := by
  intro hm F _ _ k ψ₀ hψ V _ _ _ π hirr
  set T : V →ₗ[ℂ] V := projQ ψ₀ π ∘ₗ π (sgn k) with hTdef
  have hsurj : LinearMap.range (π (sgn k)) = ⊤ :=
    LinearMap.range_eq_top.2 fun v => ⟨π (sgn k) v, pi_sgn_sgn π v⟩
  have hrT : LinearMap.range T = LinearMap.range (projQ ψ₀ π) :=
    LinearMap.range_comp_of_range_eq_top _ hsurj
  rw [← hrT, ← LinearMap.finrank_range_dualMap_eq_finrank_range T]
  by_cases h : ∃ ℓ₁ ∈ LinearMap.range T.dualMap, ℓ₁ ≠ 0
  · obtain ⟨ℓ₁, ⟨f₁, rfl⟩, hne⟩ := h
    have hle : LinearMap.range T.dualMap ≤ Submodule.span ℂ {T.dualMap f₁} := by
      rintro _ ⟨f₂, rfl⟩
      obtain ⟨c, hc⟩ := hm F k ψ₀ hψ V π hirr _ _ (isWhit_of_dual ψ₀ π f₁) (isWhit_of_dual ψ₀ π f₂) hne
      rw [Submodule.mem_span_singleton]
      exact ⟨c, hc.symm⟩
    exact (Submodule.finrank_mono hle).trans (finrank_span_singleton hne).le
  · push_neg at h
    rw [(Submodule.eq_bot_iff _).2 h, finrank_bot]
    omega

end PI.GGConvScalarW
