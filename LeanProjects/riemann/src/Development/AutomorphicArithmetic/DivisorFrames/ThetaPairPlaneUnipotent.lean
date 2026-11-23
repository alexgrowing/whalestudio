import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AutomorphicArithmetic.DivisorFrames.LocalThetaFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationIsoBTriplePair
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

theorem UpperTheory.theta_pair_plane_unipotent :
    GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
                 (n d n₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (M : Model σ X W) (M₂ : Model σ X₁ W) (H : Plane E n n₁) (j₀ j₁ : ℕ)
                 (χX χW : Chr F E) (om : Rep σ X W) (om₂ : Rep σ X₁ W) (r s r₁ s₁ r' s' : ℕ),
                 IsPair B M χX χW om r s r' s' → IsPair B M₂ χX χW om₂ r₁ s₁ r' s' → H.IsAdapted σ B X X₁ j₀ j₁ →
                 ∀ e₁ : Fn F n d →ₗ[ℂ] Fn F n₁ d, IsEv B M M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁ →
                 ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), ∀ Ψ ∈ M.So B.ψ t, e₁ Ψ = 0 := by
  intro _ F E _ _ _ _ _ σ B n d n₁ X W X₁ M M₂ H j₀ j₁ χX χW om om₂ r s r₁ s₁ r' s' hP hP₂ hH e₁ hEv v t Ψ hΨ
  classical
  obtain ⟨ei, ev, hei, hev, hfac⟩ := hEv.loc
  have hx : H.x ≠ 0 := by
    intro h0
    have h1 := hH.xy
    rw [h0] at h1
    simp [form] at h1
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hei (ContinuousLinearMap.ext hc)
  have hSB : ∀ c ∈ SB (Fin n × Fin d → Fv F v), ∀ w, Function.update M.vac v c w ∈ SB _ := by
    intro c hc w
    by_cases hwv : w = v
    · subst hwv
      rw [Function.update_self]; exact hc
    · rw [Function.update_of_ne hwv]; exact (hP.good.vac w).1
  have hco : ∀ c : (Fin n × Fin d → Fv F v) → ℂ,
      ∀ᶠ w in cofinite, Function.update M.vac v c w = M.vac w := by
    intro c
    filter_upwards [Filter.eventually_cofinite_ne v] with w hw
    exact Function.update_of_ne hw _ _
  have hup : ∀ c : (Fin n × Fin d → Fv F v) → ℂ,
      (fun w => ev w (Function.update M.vac v c w)) = Function.update M₂.vac v (ev v c) := by
    intro c
    funext w
    by_cases hwv : w = v
    · subst hwv
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hwv, Function.update_of_ne hwv]; exact (hev w).1
  have hloc : ∀ z : Fin d → AE F E, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) z)) φ φ₁ → ev v φ₁ = ev v φ := by
    intro z φ hφ φ₁ hφ₁ hact₀
    have hstd := GlobalTheory.PureFactor.update_eventually M.vac v φ hP.good.std
    have hpure := GlobalTheory.TensUniq.pure_mem_schA f _ (hSB φ hφ) hstd
    have hfin := GlobalTheory.PureFactor.mulSupport_finite _ hstd
    have hact : Acts (evFin F v) (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) z))
        (Function.update M.vac v φ v) φ₁ := by
      rw [Function.update_self]
      exact hact₀
    have hrho := GlobalTheory.ThK.LocalOps.acts_pure v _ f _ φ₁ hpure hfin hact
    rw [Function.update_idem] at hrho
    have hinv := hEv.inv _ ⟨z, rfl⟩ _ hpure
    rw [hrho, hfac f _ (hSB φ₁ hφ₁) (hco φ₁), hfac f _ (hSB φ hφ) (hco φ), hup, hup] at hinv
    exact GlobalTheory.VanishLocInv.eq_of_pure_update_eq M₂.vac (fun w => (hP₂.good.vac w).2.1) hP₂.good.std (ei f) hf v _ _ hinv
  have hzero : ∀ φ ∈ M.SoLoc B.ψ t, ev v φ = 0 := by
    intro φ hφ
    funext y
    exact UpperTheory.local_theta_functional F E σ B n d X W M r s r' s' hP.base hP.herm hP.skew H.x hx v t
      ((LinearMap.proj y).comp (ev v))
      (fun z _ φ hφ φ₁ hφ₁ h => congrFun (hloc z φ hφ φ₁ hφ₁ h) y) φ hφ
  have hle : M.So B.ψ t ≤ LinearMap.ker e₁ := by
    refine Submodule.span_le.2 ?_
    rintro Φ ⟨g, φ, hφ, hφv, hφs, rfl⟩
    show e₁ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) = 0
    rw [hfac g φ hφ hφv]
    have hstd : ∀ᶠ w in cofinite, ev w (φ w) =
        Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
      filter_upwards [hφv, hP₂.good.std] with w h1 h2
      rw [h1, (hev w).1, h2]
    funext x
    have hfin := GlobalTheory.PureFactor.mulSupport_finite (fun w => ev w (φ w)) hstd x
    rw [GlobalTheory.ThK.LocalOps.pure_split v (ei g) (fun w => ev w (φ w)) (fun w => ev w (φ w)) x hfin (fun _ _ => rfl)]
    simp only [hzero _ hφs, Pi.zero_apply, zero_mul]
  exact hle hΨ
