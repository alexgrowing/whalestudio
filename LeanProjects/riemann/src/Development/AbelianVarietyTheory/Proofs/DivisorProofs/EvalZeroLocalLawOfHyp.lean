import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfTensEqOfNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace

noncomputable section

open scoped Classical

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem evZeroLocLaw : GlobalTheory.FunPr.Hypotheses₂ → EvZeroLocLaw := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hP₁ e hE ei ev hloc v
    g hg t h₁ m hL hm hh₁ u hu huv φ hφ
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hK
  have hM := hP.good
  have hM₁ := hP₁.good
  obtain ⟨hei, hev, hpure⟩ := hloc
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  obtain ⟨c₀, hc₀, hc₀t⟩ := GlobalTheory.PureFactor.exists_rest_factor v f M.vac hM.std
  obtain ⟨c₁, hc₁, hc₁t⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) M₁.vac hM₁.std
  have hc₁0 : c₁ ≠ 0 := by
    have ht : tens (evFin F v) (fun _ => (1 : ℂ)) c₁ = c₁ := by
      funext x
      simp [tens]
    have h1 := hc₁t (fun _ => 1)
    rw [ht] at h1
    rw [h1]
    refine GlobalTheory.EvNonzero.pure_ne_zero (ei f) hf _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v _ hM₁.std)
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      intro h
      exact one_ne_zero (congrFun h 0)
    · rw [Function.update_of_ne hw]
      exact (hM₁.vac w).2.1
  have hupd : ∀ ψ ∈ SB (Fin n × Fin d → Fv F v), ∀ w, Function.update M.vac v ψ w ∈ SB _ := by
    intro ψ hψ w
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact hψ
    · rw [Function.update_of_ne hw]
      exact (hM.vac w).1
  have hupd₁ : ∀ ψ ∈ SB (Fin n × Fin d₁ → Fv F v), ∀ w, Function.update M₁.vac v ψ w ∈ SB _ := by
    intro ψ hψ w
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact hψ
    · rw [Function.update_of_ne hw]
      exact (hM₁.vac w).1
  have hRest : ∀ ψ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) ψ c₀ := fun ψ hψ =>
    ⟨hc₀, by
      rw [hc₀t ψ]
      exact GlobalTheory.TensUniq.pure_mem_schA f _ (hupd ψ hψ) (GlobalTheory.PureFactor.update_eventually _ v ψ hM.std)⟩
  have hRest₁ : ∀ ψ ∈ SB (Fin n × Fin d₁ → Fv F v), Rest (evFin F v) ψ c₁ := fun ψ hψ =>
    ⟨hc₁, by
      rw [hc₁t ψ]
      exact GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (hupd₁ ψ hψ) (GlobalTheory.PureFactor.update_eventually _ v ψ hM₁.std)⟩
  have hevSB : ∀ ψ ∈ SB (Fin n × Fin d → Fv F v), ev v ψ ∈ SB _ := by
    intro ψ hψ
    rw [← (hev v).2]
    exact Submodule.mem_map_of_mem hψ
  have hev_pure : ∀ ψ ∈ SB (Fin n × Fin d → Fv F v),
      e (tens (evFin F v) ψ c₀) = tens (evFin F v) (ev v ψ) c₁ := by
    intro ψ hψ
    have hc : ∀ᶠ w in cofinite, Function.update M.vac v ψ w = M.vac w := by
      filter_upwards [Filter.eventually_cofinite_ne v] with w hw
      rw [Function.update_of_ne hw]
    have hfun : (fun w => ev w (Function.update M.vac v ψ w)) = Function.update M₁.vac v (ev v ψ) := by
      funext w
      by_cases hw : w = v
      · subst hw
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hw, (hev w).1]
    rw [hc₀t ψ, hpure f _ (hupd ψ hψ) hc, hfun, hc₁t]
  have hum : u * m ∈ UAt σ W (evFin F v) := (UAtSub σ W (evFin F v)).mul_mem huv hm
  have hA1 := acts_locOp_om hA hP hg hum hφ
  have hA2 := acts_locOp_om hA hP₁ hg hh₁ (hevSB φ hφ)
  have hlaw := GlobalTheory.T.adapted_plane_second_variable hK F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH' hP₁ e hE
    g t h₁ m hL u hu (tens (evFin F v) φ c₀) (hRest φ hφ).2
  apply GlobalTheory.ThK.EvZeroFinLoc.eq_of_tens_eq_of_ne_zero v c₁ hc₁ hc₁0
  rw [← hev_pure _ (locOp_mem _ _ _), ← hA1 c₀ (hRest φ hφ), hlaw, hev_pure φ hφ, hA2 c₁ (hRest₁ _ (hevSB φ hφ))]
  funext x
  simp only [tens, fac, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.ThK.LemF

end
