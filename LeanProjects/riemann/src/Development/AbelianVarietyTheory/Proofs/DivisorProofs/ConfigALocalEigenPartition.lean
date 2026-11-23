import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfTensEqOfNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace

noncomputable section

open scoped Classical

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.EvLawLoc

theorem resEtaPow_div' {R E : Type} [CommRing R] [CommRing E] [Algebra R E] [Invertible (2 : R)] {K : Subgroup Rˣ}
    {χ₁ χ₂ : Eˣ →* Circle} {m n : ℕ} (h₁ : ResEtaPow K χ₁ m) (h₂ : ResEtaPow K χ₂ n) :
    ResEtaPow K (χ₁ / χ₂) (m + n) := by
  intro x
  rw [MonoidHom.div_apply, Circle.coe_div, h₁ x, h₂ x]
  split_ifs
  · simp
  · have h : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [div_eq_iff (pow_ne_zero _ (by norm_num)), pow_add, mul_assoc, h, mul_one]

theorem isHecke_div' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {χ₁ χ₂ : Chr F E}
    (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) :=
  ⟨h₁.1.div' h₂.1, fun x => by rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x]; exact div_self' 1⟩

theorem incM_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem vecMulVec_mul_transpose {R : Type} [CommRing R] {k l p : ℕ} (a : Fin k → R) (b : Fin p → R)
    (M : Matrix (Fin l) (Fin p) R) : Matrix.vecMulVec a b * Mᵀ = Matrix.vecMulVec a (M *ᵥ b) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem evLaw_isoA_unip : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (t : (AE F E)ˣ) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi H' t h₁ m → ∀ u ∈ unip σ G.W H',
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      e (om (1, u * m) Ψ) = ((X.β t : ℂ) * (((absE F E t : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ)) • om₁ (1, h₁) (e Ψ) := by
  intro hK F E _ _ _ _ _ σ B b a' G G₁ H H' cfg e hev X om om' om₁ om₁' T T₁ t h₁ m hL u hu Ψ hΨ
  have P : IsPair B G.M X.β (X.β / X.α) om (b + 2 - G.p) G.p _ _ :=
    ⟨T.base, T.geo.hV, T.geo.hW, T.geo.hM, T.chars.heckeβ, isHecke_div' T.chars.heckeβ T.chars.heckeα,
      T.chars.resβ, resEtaPow_div' T.chars.resβ T.chars.resα, T.weil⟩
  have P₁ : IsPair B G₁.M X.β (X.β / X.α) om₁ (b - G₁.p) G₁.p _ _ :=
    ⟨T₁.base, T₁.geo.hV, T₁.geo.hW, T₁.geo.hM, T₁.chars.heckeβ, isHecke_div' T₁.chars.heckeβ T₁.chars.heckeα,
      T₁.chars.resβ, resEtaPow_div' T₁.chars.resβ T₁.chars.resα, T₁.weil⟩
  obtain ⟨Ma, hMa⟩ := GlobalTheory.T.exists_good_schrodinger_model F E σ B T.base (b + 2) (b + a') G.V G₁.W _ _ _ _ T.geo.hV T₁.geo.hW
  obtain ⟨oma, hwa⟩ := GlobalTheory.WeilExGen.exists_isWeil hK F E σ B T.base (b + 2) (b + a') G.V G₁.W _ _ _ _ T.geo.hV T₁.geo.hW Ma hMa
    X.β (X.β / X.α) T.chars.heckeβ (isHecke_div' T.chars.heckeβ T.chars.heckeα) T.chars.resβ
    (resEtaPow_div' T₁.chars.resβ T₁.chars.resα)
  have Pa : IsPair B Ma X.β (X.β / X.α) oma (b + 2 - G.p) G.p _ _ :=
    ⟨T.base, T.geo.hV, T₁.geo.hW, hMa, T.chars.heckeβ, isHecke_div' T.chars.heckeβ T.chars.heckeα,
      T.chars.resβ, resEtaPow_div' T₁.chars.resβ T₁.chars.resα, hwa⟩
  obtain ⟨e₁, he₁⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hK).1 F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P
    (b + a') G.V G₁.W H' 0 (b + 1) Ma rfl cfg.hH' hMa).1
  obtain ⟨⟨e₂, he₂⟩, law₂⟩ := GlobalTheory.T.adapted_plane_first_variable hK F E σ B (b + 2) (b + a') G.V G₁.W Ma X.β (X.β / X.α) oma _ _ _ _ Pa
    b G₁.V H 0 (b + 1) G₁.M om₁ _ _ cfg.hH P₁
  have heisC : ∀ (z : Matrix (Fin b) (Fin (b + a')) (AE F E)), ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      (e₂ ∘ₗ e₁) (G.M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = G₁.M.co.rho B.ψ z ((e₂ ∘ₗ e₁) Φ) := by
    intro z Φ hΦ
    have h1 := he₁.Heisenberg₂ (incM F H.ι * z) Φ hΦ
    have h2 := he₂.Heisenberg₂ z (e₁ Φ) (he₁.maps Φ hΦ)
    rw [incM_one', Matrix.one_mul] at h1
    rw [incM_one', Matrix.transpose_one, Matrix.mul_one] at h2
    simp only [LinearMap.comp_apply]
    rw [h1, h2]
  have invC : ∀ u ∈ isoA H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      (e₂ ∘ₗ e₁) (G.M.co.rho B.ψ u Φ) = (e₂ ∘ₗ e₁) Φ := by
    intro u hu Φ hΦ
    simp only [LinearMap.comp_apply]
    rcases hu with hu | ⟨z, rfl⟩
    · rw [he₁.inv u hu Φ hΦ]
    · have h1 := he₁.Heisenberg₂ (Matrix.vecMulVec (incV F H.x) z) Φ hΦ
      rw [incM_one', Matrix.one_mul, vecMulVec_mul_transpose] at h1
      rw [h1, he₂.inv _ ⟨z, rfl⟩ _ (he₁.maps Φ hΦ)]
  obtain ⟨c, hc⟩ := GlobalTheory.T.pair_double_descent hK F E σ B (b + 2) (b + 2 + a') b (b + a') G.V G.W G₁.V G₁.W G.M X.β (X.β / X.α) om
    _ _ _ _ P H H' 0 (b + 1) 0 (b + 1) G₁.M cfg.hH cfg.hH' T₁.geo.hM e hev (e₂ ∘ₗ e₁) heisC invC
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.pair_double_descent_models hK F E σ B (b + 2) (b + 2 + a') b (b + a') G.V G.W G₁.V G₁.W G.M X.β (X.β / X.α) om
    _ _ _ _ P H H' 0 (b + 1) 0 (b + 1) Ma oma _ _ G₁.M cfg.hH cfg.hH' Pa T₁.geo.hM e₁ e₂ he₁ he₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    have := hc Φ₀ hΦ₀
    rw [zero_smul, LinearMap.comp_apply] at this
    exact this
  have hpres : om (1, u * m) Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := (T.weil.isUSplitting).pres _ _ hΨ
  have hLX : IsLevi (W₁ := G₁.V) H 1 (1 : UA σ G₁.V.J) (1 : UA σ G.V.J) := by
    refine ⟨?_, ?_, ?_⟩
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _)
      simp
  have key : e₂ (e₁ (om (1, u * m) Ψ)) = ((X.β t : ℂ) * (((absE F E t : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ)) •
      om₁ (1, h₁) (e₂ (e₁ Ψ)) := by
    have h1 := GlobalTheory.T.adapted_plane_second_variable hK F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P (b + a') G₁.W H'
      0 (b + 1) Ma oma _ _ cfg.hH' Pa e₁ he₁ 1 t h₁ m hL u hu Ψ hΨ
    have h2 := law₂ e₂ he₂ h₁ 1 1 1 hLX 1 (Subgroup.one_mem _) (e₁ Ψ) (he₁.maps Ψ hΨ)
    simp only [one_mul, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] at h1 h2
    rw [h1, map_smul, h2]
  calc e (om (1, u * m) Ψ) = c⁻¹ • (c • e (om (1, u * m) Ψ)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • (((X.β t : ℂ) * (((absE F E t : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ)) • om₁ (1, h₁) (c • e Ψ)) := by
        rw [← hc _ hpres, ← hc _ hΨ]
        simp only [LinearMap.comp_apply]
        rw [key]
    _ = _ := by rw [map_smul, smul_comm _ c, smul_smul, inv_mul_cancel₀ hc0, one_smul]

end GlobalTheory.ThK.EvLawLoc

namespace GlobalTheory.ThK.LemF

open GlobalTheory.ThK.EvLawLoc

theorem evLocLaw_isoA : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, GlobalTheory.ThK.LemF.IsLocPart G.M G₁.M e ei ev →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ v : Pl F,
    ∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) → h₁ ∈ UAt σ G₁.W (evFin F v) →
    ∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ev v (locOp v (om (1, u * m)) φ) = GlobalTheory.ThK.LemF.fac X.β (((b + 2 : ℕ) : ℝ) / 2) t • locOp v (om₁ (1, h₁)) (ev v φ) := by
  intro hK F E _ _ _ _ _ σ B b a' G G₁ H H' cfg e hE ei ev hloc X om om' om₁ om₁' T T₁ v t h₁ m hL hm hh₁ u hu huv φ hφ
  have hP : IsPair B G.M X.β (X.β / X.α) om (b + 2 - G.p) G.p _ _ :=
    ⟨T.base, T.geo.hV, T.geo.hW, T.geo.hM, T.chars.heckeβ, isHecke_div' T.chars.heckeβ T.chars.heckeα,
      T.chars.resβ, resEtaPow_div' T.chars.resβ T.chars.resα, T.weil⟩
  have hP₁ : IsPair B G₁.M X.β (X.β / X.α) om₁ (b - G₁.p) G₁.p _ _ :=
    ⟨T₁.base, T₁.geo.hV, T₁.geo.hW, T₁.geo.hM, T₁.chars.heckeβ, isHecke_div' T₁.chars.heckeβ T₁.chars.heckeα,
      T₁.chars.resβ, resEtaPow_div' T₁.chars.resβ T₁.chars.resα, T₁.weil⟩
  have hA : ActsEx := GlobalTheory.T.theta_action_exists hK
  have hM := hP.good
  have hM₁ := hP₁.good
  obtain ⟨hei, hev, hpure⟩ := hloc
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
  have hum : u * m ∈ UAt σ G.W (evFin F v) := (UAtSub σ G.W (evFin F v)).mul_mem huv hm
  have hg : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := (UAtSub σ G.V (evFin F v)).one_mem
  have hg₁ : (1 : UA σ G₁.V.J) ∈ UAt σ G₁.V (evFin F v) := (UAtSub σ G₁.V (evFin F v)).one_mem
  have hA1 := acts_locOp_om hA hP hg hum hφ
  have hA2 := acts_locOp_om hA hP₁ hg₁ hh₁ (hevSB φ hφ)
  have hlaw := GlobalTheory.ThK.EvLawLoc.evLaw_isoA_unip hK F E σ B b a' G G₁ H H' cfg e hE X om om' om₁ om₁' T T₁ t h₁ m hL
    u hu (tens (evFin F v) φ c₀) (hRest φ hφ).2
  apply GlobalTheory.ThK.EvZeroFinLoc.eq_of_tens_eq_of_ne_zero v c₁ hc₁ hc₁0
  rw [← hev_pure _ (locOp_mem _ _ _), ← hA1 c₀ (hRest φ hφ), hlaw, hev_pure φ hφ, hA2 c₁ (hRest₁ _ (hevSB φ hφ))]
  funext x
  simp only [tens, fac, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.ThK.LemF

end
