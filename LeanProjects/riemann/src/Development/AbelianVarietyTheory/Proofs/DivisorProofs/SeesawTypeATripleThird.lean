import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfTensEqOfNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped GlobalTheory.VacAny

namespace GlobalTheory.ThK.LawLoc

open scoped Classical in

theorem ev_locOp_law : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      ei ≠ 0 → (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (v : Pl F) (k : UA σ G.V.J), k ∈ UAt σ G.V (evFin F v) → ∀ g₁ : UA σ G₁.V.J, g₁ ∈ UAt σ G₁.V (evFin F v) →
    ∀ c : ℂ, (∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e (om (k, 1) Ψ) = c • om₁ (g₁, 1) (e Ψ)) →
      ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), ev v (locOp v (om (k, 1)) φ) = c • locOp v (om₁ (g₁, 1)) (ev v φ) := by
  intro hK F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' _cfg T T₁ e _hE ei ev hei hev hpure v k hk g₁ hg₁ c hlaw φ hφ
  have hHd : ∀ {χ₁ χ₂ : Chr F E}, IsHecke F E χ₁ → IsHecke F E χ₂ → IsHecke F E (χ₁ / χ₂) := fun h₁ h₂ =>
    ⟨h₁.1.div' h₂.1, fun x => by rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x]; exact div_self' 1⟩
  have hRd : ∀ {K : Subgroup (AF F)ˣ} {χ₁ χ₂ : Chr F E} {m n : ℕ}, ResEtaPow K χ₁ m → ResEtaPow K χ₂ n →
      ResEtaPow K (χ₁ / χ₂) (m + n) := by
    intro K χ₁ χ₂ m n h₁ h₂ x
    rw [MonoidHom.div_apply, Circle.coe_div, h₁ x, h₂ x]
    split_ifs
    · simp
    · have h : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
      rw [div_eq_iff (pow_ne_zero _ (by norm_num)), pow_add, mul_assoc, h, mul_one]
  have hP : IsPair B G.M X.β (X.β / X.α) om (b + 2 - G.p) G.p _ _ :=
    ⟨T.base, T.geo.hV, T.geo.hW, T.geo.hM, T.chars.heckeβ, hHd T.chars.heckeβ T.chars.heckeα,
      T.chars.resβ, hRd T.chars.resβ T.chars.resα, T.weil⟩
  have hP₁ : IsPair B G₁.M X.β (X.β / X.α) om₁ (b - G₁.p) G₁.p _ _ :=
    ⟨T₁.base, T₁.geo.hV, T₁.geo.hW, T₁.geo.hM, T₁.chars.heckeβ, hHd T₁.chars.heckeβ T₁.chars.heckeα,
      T₁.chars.resβ, hRd T₁.chars.resβ T₁.chars.resα, T₁.weil⟩
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hK.base
  have hM := hP.good
  have hM₁ := hP₁.good
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  obtain ⟨c₀, hc₀, hc₀t⟩ := GlobalTheory.PureFactor.exists_rest_factor v f G.M.vac hM.std
  obtain ⟨c₁, hc₁, hc₁t⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) G₁.M.vac hM₁.std
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
  have hupd : ∀ ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), ∀ w, Function.update G.M.vac v ψ w ∈ SB _ := by
    intro ψ hψ w
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact hψ
    · rw [Function.update_of_ne hw]
      exact (hM.vac w).1
  have hupd₁ : ∀ ψ ∈ SB (Fin b × Fin (b + a') → Fv F v), ∀ w, Function.update G₁.M.vac v ψ w ∈ SB _ := by
    intro ψ hψ w
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact hψ
    · rw [Function.update_of_ne hw]
      exact (hM₁.vac w).1
  have hRest : ∀ ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), Rest (evFin F v) ψ c₀ := fun ψ hψ =>
    ⟨hc₀, by
      rw [hc₀t ψ]
      exact GlobalTheory.TensUniq.pure_mem_schA f _ (hupd ψ hψ) (GlobalTheory.PureFactor.update_eventually _ v ψ hM.std)⟩
  have hRest₁ : ∀ ψ ∈ SB (Fin b × Fin (b + a') → Fv F v), Rest (evFin F v) ψ c₁ := fun ψ hψ =>
    ⟨hc₁, by
      rw [hc₁t ψ]
      exact GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (hupd₁ ψ hψ) (GlobalTheory.PureFactor.update_eventually _ v ψ hM₁.std)⟩
  have hevSB : ∀ ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), ev v ψ ∈ SB _ := by
    intro ψ hψ
    rw [← (hev v).2]
    exact Submodule.mem_map_of_mem hψ
  have hev_pure : ∀ ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      e (tens (evFin F v) ψ c₀) = tens (evFin F v) (ev v ψ) c₁ := by
    intro ψ hψ
    have hc : ∀ᶠ w in cofinite, Function.update G.M.vac v ψ w = G.M.vac w := by
      filter_upwards [Filter.eventually_cofinite_ne v] with w hw
      rw [Function.update_of_ne hw]
    have hfun : (fun w => ev w (Function.update G.M.vac v ψ w)) = Function.update G₁.M.vac v (ev v ψ) := by
      funext w
      by_cases hw : w = v
      · subst hw
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hw, (hev w).1]
    rw [hc₀t ψ, hpure f _ (hupd ψ hψ) hc, hfun, hc₁t]
  have h1 : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := (UAtSub σ G.W (evFin F v)).one_mem
  have h1' : (1 : UA σ G₁.W.J) ∈ UAt σ G₁.W (evFin F v) := (UAtSub σ G₁.W (evFin F v)).one_mem
  have hA1 := acts_locOp_om hA hP hk h1 hφ
  have hA2 := acts_locOp_om hA hP₁ hg₁ h1' (hevSB φ hφ)
  apply GlobalTheory.ThK.EvZeroFinLoc.eq_of_tens_eq_of_ne_zero v c₁ hc₁ hc₁0
  rw [← hev_pure _ (locOp_mem _ _ _), ← hA1 c₀ (hRest φ hφ), hlaw _ (hRest φ hφ).2, hev_pure φ hφ,
    hA2 c₁ (hRest₁ _ (hevSB φ hφ))]
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.ThK.LawLoc

end
