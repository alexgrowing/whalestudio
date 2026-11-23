import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlace

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HoweLocal.Psi

theorem psiAt_cont_norm_nontriv : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F,
    Continuous (GlobalTheory.LatVac.psiAt ψ v) ∧ (∀ t, ‖GlobalTheory.LatVac.psiAt ψ v t‖ = 1) ∧ GlobalTheory.LatVac.psiAt ψ v ≠ 1 := by
  intro F _ _ ψ hψ v
  have hc : Continuous (GlobalTheory.LatVac.psiAt ψ v) := by
    show Continuous (fun x => ψ (GlobalTheory.LatVac.liftV v x))
    exact hψ.1.comp (continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v))

  have hle : ∀ t, ‖GlobalTheory.LatVac.psiAt ψ v t‖ ≤ 1 := by
    intro t
    haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
    have hcf : Continuous fun y : v.adicCompletionIntegers F => ‖GlobalTheory.LatVac.psiAt ψ v (t * (y : Fv F v))‖ :=
      (hc.comp (continuous_const.mul continuous_subtype_val)).norm
    obtain ⟨M, hM⟩ := (isCompact_range hcf).isBounded.bddAbove
    have hpow : ∀ n : ℕ, ‖GlobalTheory.LatVac.psiAt ψ v t‖ ^ n ≤ M := by
      intro n
      have hn : ((n : Fv F v)) ∈ v.adicCompletionIntegers F := by
        exact natCast_mem _ n
      have := hM ⟨⟨(n : Fv F v), hn⟩, rfl⟩
      simp only at this
      rw [← norm_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]
      exact this
    by_contra hgt
    push_neg at hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hgt
    exact absurd (hpow n) (not_le.mpr hn)
  refine ⟨hc, fun t => ?_, ?_⟩
  · have h1 := hle t
    have h2 := hle (-t)
    have hmul : GlobalTheory.LatVac.psiAt ψ v t * GlobalTheory.LatVac.psiAt ψ v (-t) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    have hn : ‖GlobalTheory.LatVac.psiAt ψ v t‖ * ‖GlobalTheory.LatVac.psiAt ψ v (-t)‖ = 1 := by
      rw [← norm_mul, hmul, norm_one]
    nlinarith [norm_nonneg (GlobalTheory.LatVac.psiAt ψ v t), norm_nonneg (GlobalTheory.LatVac.psiAt ψ v (-t))]
  · intro h
    obtain ⟨t, ht⟩ := GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one ψ hψ v
    exact ht (by rw [h, AddChar.one_apply])

end GlobalTheory.HoweLocal.Psi
