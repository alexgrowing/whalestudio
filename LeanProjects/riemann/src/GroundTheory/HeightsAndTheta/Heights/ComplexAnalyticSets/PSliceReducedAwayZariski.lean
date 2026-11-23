import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedAwayZariski
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBundleRadicalAway
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem eq_ker_eval_of_X_sub_C_mem {n : ℕ} (q : Fin n → ℂ) (P : Ideal (MvPolynomial (Fin n) ℂ))
    (hP : P.IsPrime) (h : ∀ k, X k - C (q k) ∈ P) : P = RingHom.ker (eval q) := by
  have hext : Ideal.Quotient.mk P = ((Ideal.Quotient.mk P).comp C).comp (eval q) := by
    refine MvPolynomial.ringHom_ext (fun c => by simp) (fun i => ?_)
    simp only [RingHom.comp_apply, eval_X]
    exact Ideal.Quotient.eq.2 (h i)
  have hle : RingHom.ker (eval q) ≤ P := by
    intro f hf
    rw [← Ideal.Quotient.eq_zero_iff_mem, hext]
    simp [RingHom.mem_ker.1 hf]
  have hmax : (RingHom.ker (eval q)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, eval_C c⟩
  exact (hmax.eq_of_le hP.ne_top hle).symm

theorem SliceReducedAwayZariski.proof (hG : GenericFibreRadicalAway.Statement)
    (hB : SliceBundleRadicalAway.Statement) : SliceReducedAwayZariski.Statement := by
  intro n d J q hJ
  choose F hF0 hF using fun k : Fin n =>
    hG (Fin d × Fin n) n (universalSliceIdeal J d q) (X k - C (C (q k))) (hB n d J q hJ k)
  refine ⟨∏ k, F k, Finset.prod_ne_zero_iff.2 fun k _ => hF0 k, ?_⟩
  intro L hL P hP hIP hPq g hg
  rw [map_prod, Finset.prod_ne_zero_iff] at hL
  obtain ⟨k, hk⟩ : ∃ k, X k - C (q k) ∉ P := by
    by_contra h
    push Not at h
    exact hPq (eq_ker_eval_of_X_sub_C_mem q P hP h)
  have hk' := hF k _ (hL k (Finset.mem_univ k))
  rw [fibreIdeal_universalSliceIdeal] at hk'
  obtain ⟨m, hm⟩ := hk' g hg
  refine ⟨(X k - C (q k)) ^ m, fun h => hk (hP.mem_of_pow_mem m h), ?_⟩
  simpa using hm

end

end GroundTheory.Heights₂.Heights
