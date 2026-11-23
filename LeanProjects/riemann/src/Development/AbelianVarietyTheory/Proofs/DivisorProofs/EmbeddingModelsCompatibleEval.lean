import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfTensEqOfNeZero

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairLoc
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

noncomputable section

namespace GlobalTheory.ThK.EvLocParts

open scoped Classical in

theorem locParts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), B.IsGood σ → M.IsGood B.ψ →
    M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
      (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ v : Pl F, (∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), At (evFin F v) z → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
          ev v (locOp v (M.co.rho B.ψ (incM F ι * z * (incM F ι')ᵀ)) φ) = locOp v (M₁.co.rho B.ψ z) (ev v φ)) ∧
        ∀ u ∈ I, At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v (locOp v (M.co.rho B.ψ u) φ) = ev v φ := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hB hM hM₁ hE ei ev hei hev hloc v
  have hψ : Continuous B.ψ := hB.std.1
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  obtain ⟨r₀, hr₀, hr₀t⟩ := GlobalTheory.PureFactor.exists_rest_factor v f M.vac hM.std
  obtain ⟨r₁, hr₁, hr₁t⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) M₁.vac hM₁.std
  have hr₁0 : r₁ ≠ 0 := by
    have ht : tens (evFin F v) (fun _ => (1 : ℂ)) r₁ = r₁ := by
      funext x
      simp [tens]
    have h1 := hr₁t (fun _ => 1)
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
  have hupd : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ w, Function.update M.vac v φ w ∈ SB _ := by
    intro φ hφ w
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact hφ
    · rw [Function.update_of_ne hw]
      exact (hM.vac w).1
  have hupd₁ : ∀ φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v), ∀ w, Function.update M₁.vac v φ w ∈ SB _ := by
    intro φ hφ w
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact hφ
    · rw [Function.update_of_ne hw]
      exact (hM₁.vac w).1
  have hRest : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), Rest (evFin F v) φ r₀ := fun φ hφ =>
    ⟨hr₀, by
      rw [hr₀t φ]
      exact GlobalTheory.TensUniq.pure_mem_schA f _ (hupd φ hφ) (GlobalTheory.PureFactor.update_eventually _ v φ hM.std)⟩
  have hRest₁ : ∀ φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v), Rest (evFin F v) φ r₁ := fun φ hφ =>
    ⟨hr₁, by
      rw [hr₁t φ]
      exact GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (hupd₁ φ hφ) (GlobalTheory.PureFactor.update_eventually _ v φ hM₁.std)⟩
  have hevSB : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v φ ∈ SB _ := by
    intro φ hφ
    rw [← (hev v).2]
    exact Submodule.mem_map_of_mem hφ
  have hev_pure : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), e (tens (evFin F v) φ r₀) = tens (evFin F v) (ev v φ) r₁ := by
    intro φ hφ
    have hc : ∀ᶠ w in cofinite, Function.update M.vac v φ w = M.vac w := by
      filter_upwards [Filter.eventually_cofinite_ne v] with w hw
      rw [Function.update_of_ne hw]
    have hfun : (fun w => ev w (Function.update M.vac v φ w)) = Function.update M₁.vac v (ev v φ) := by
      funext w
      by_cases hw : w = v
      · subst hw
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hw, (hev w).1]
    rw [hr₀t φ, hloc f _ (hupd φ hφ) hc, hfun, hr₁t]
  refine ⟨?_, ?_⟩
  · intro z hz φ hφ
    have hu : At (evFin F v) (incM F ι * z * (incM F ι')ᵀ) := by
      intro a ha
      rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz a ha, Matrix.mul_zero, Matrix.zero_mul]
    have hA := (locOp_rho M.co hψ v (incM F ι * z * (incM F ι')ᵀ) hφ).1
    rw [partFin_of_at hu] at hA
    have hφ₁ := locOp_mem v (M.co.rho B.ψ (incM F ι * z * (incM F ι')ᵀ)) φ
    have hA₁ := (locOp_rho M₁.co hψ v z (hevSB φ hφ)).1
    rw [partFin_of_at hz] at hA₁
    apply GlobalTheory.ThK.EvZeroFinLoc.eq_of_tens_eq_of_ne_zero v r₁ hr₁ hr₁0
    rw [← hev_pure _ hφ₁, ← hA r₀ (hRest φ hφ), hE.Heisenberg₂ z _ (hRest φ hφ).2, hev_pure φ hφ,
      hA₁ r₁ (hRest₁ _ (hevSB φ hφ))]
  · intro u hu hat φ hφ
    have h2 := (locOp_rho M.co hψ v u hφ).2
    rw [partFin_of_at hat] at h2
    rw [h2]
    exact GlobalTheory.ThK.EvLocInv.ev_schr_of_mem B M M₁ ι ι' I e hE hψ hM hM₁ ei ev hei hev hloc v u hu hat φ hφ

end GlobalTheory.ThK.EvLocParts

end
