import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfTensEqOfNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.EvInvALoc

theorem global_laws : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    (∀ u ∈ unip σ G.V H, ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e (om (u, 1) Ψ) = e Ψ) ∧
    (∀ (g₀ : UA σ G₁.V.J) (g : UA σ G.V.J), IsLevi H 1 g₀ g → ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      e (om (g, 1) Ψ) = om₁ (g₀, 1) (e Ψ)) := by
  intro hP F E _ _ _ _ _ σ B b a' G G₁ H H' cfg e hev X om om' om₁ om₁' T T₁
  have P := Inhab.pairV T
  have P₁ := Inhab.pairV T₁

  obtain ⟨Ma, hMa⟩ := GlobalTheory.T.exists_good_schrodinger_model F E σ B P.base (b + 2) (b + a') G.V G₁.W _ _ _ _ P.herm P₁.skew
  obtain ⟨oma, hwa⟩ := GlobalTheory.WeilExGen.exists_isWeil hP F E σ B P.base (b + 2) (b + a') G.V G₁.W _ _ _ _ P.herm P₁.skew Ma hMa
    X.β (X.β / X.α) P.hX P.hW P.resX P₁.resW
  have Pa : IsPair B Ma X.β (X.β / X.α) oma (b + 2 - G.p) G.p (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q) :=
    ⟨P.base, P.herm, P₁.skew, hMa, P.hX, P.hW, P.resX, P₁.resW, hwa⟩

  obtain ⟨e₁, he₁⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hP).1 F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P
    (b + a') G.V G₁.W H' 0 (b + 1) Ma rfl cfg.hH' hMa).1
  obtain ⟨⟨e₂, he₂⟩, law₂⟩ := GlobalTheory.T.adapted_plane_first_variable hP F E σ B (b + 2) (b + a') G.V G₁.W Ma X.β (X.β / X.α) oma _ _ _ _ Pa
    b G₁.V H 0 (b + 1) G₁.M om₁ _ _ cfg.hH P₁
  have h1 : incM F (1 : Matrix (Fin (b + 2)) (Fin (b + 2)) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin (b + a')) (Fin (b + a')) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have heisC : ∀ (z : Matrix (Fin b) (Fin (b + a')) (AE F E)), ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      (e₂ ∘ₗ e₁) (G.M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = G₁.M.co.rho B.ψ z ((e₂ ∘ₗ e₁) Φ) := by
    intro z Φ hΦ
    have k1 := he₁.Heisenberg₂ (incM F H.ι * z) Φ hΦ
    have k2 := he₂.Heisenberg₂ z (e₁ Φ) (he₁.maps Φ hΦ)
    rw [h1, Matrix.one_mul] at k1
    rw [h1', Matrix.transpose_one, Matrix.mul_one] at k2
    simp only [LinearMap.comp_apply]
    rw [k1, k2]
  have invC : ∀ u ∈ isoA H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      (e₂ ∘ₗ e₁) (G.M.co.rho B.ψ u Φ) = (e₂ ∘ₗ e₁) Φ := by
    intro u hu Φ hΦ
    simp only [LinearMap.comp_apply]
    rcases hu with hu | ⟨z, rfl⟩
    · rw [he₁.inv u hu Φ hΦ]
    · have k1 := he₁.Heisenberg₂ (Matrix.vecMulVec (incV F H.x) z) Φ hΦ
      have hvm : Matrix.vecMulVec (incV F H.x) z * (incM F H'.ι)ᵀ = Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ z) := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [h1, Matrix.one_mul, hvm] at k1
      rw [k1, he₂.inv _ ⟨z, rfl⟩ _ (he₁.maps Φ hΦ)]
  obtain ⟨c, hc⟩ := GlobalTheory.T.pair_double_descent hP F E σ B (b + 2) (b + 2 + a') b (b + a') G.V G.W G₁.V G₁.W G.M X.β (X.β / X.α) om
    _ _ _ _ P H H' 0 (b + 1) 0 (b + 1) G₁.M cfg.hH cfg.hH' T₁.geo.hM e hev (e₂ ∘ₗ e₁) heisC invC
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.pair_double_descent_models hP F E σ B (b + 2) (b + 2 + a') b (b + a') G.V G.W G₁.V G₁.W G.M X.β (X.β / X.α) om
    _ _ _ _ P H H' 0 (b + 1) 0 (b + 1) Ma oma _ _ G₁.M cfg.hH cfg.hH' Pa T₁.geo.hM e₁ e₂ he₁ he₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    have := hc Φ₀ hΦ₀
    rw [zero_smul, LinearMap.comp_apply] at this
    exact this
  have hLW : IsLevi (W₁ := G₁.W) H' 1 (1 : UA σ G₁.W.J) (1 : UA σ G.W.J) := by
    refine ⟨?_, ?_, ?_⟩
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _)
      simp
  have hLV : IsLevi (W₁ := G₁.V) H 1 (1 : UA σ G₁.V.J) (1 : UA σ G.V.J) := by
    refine ⟨?_, ?_, ?_⟩
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _)
      simp

  have law₁ : ∀ (g : UA σ G.V.J) Ψ, Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) → e₁ (om (g, 1) Ψ) = oma (g, 1) (e₁ Ψ) := by
    intro g Ψ hΨ
    have k := GlobalTheory.T.adapted_plane_second_variable hP F E σ B (b + 2) (b + 2 + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ P (b + a') G₁.W H'
      0 (b + 1) Ma oma _ _ cfg.hH' Pa e₁ he₁ g 1 1 1 hLW 1 (Subgroup.one_mem _) Ψ hΨ
    simpa only [one_mul, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] using k
  refine ⟨fun u hu Ψ hΨ => ?_, fun g₀ g hL Ψ hΨ => ?_⟩
  · have hpres : om (u, 1) Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := (T.weil.isUSplitting).pres _ _ hΨ
    have k2 := law₂ e₂ he₂ 1 1 1 1 hLV u hu (e₁ Ψ) (he₁.maps Ψ hΨ)
    simp only [mul_one, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul,
      Prod.mk_one_one, Module.End.one_apply] at k2
    apply smul_right_injective _ hc0
    show c • e (om (u, 1) Ψ) = c • e Ψ
    rw [← hc _ hpres, ← hc _ hΨ, LinearMap.comp_apply, LinearMap.comp_apply, law₁ u Ψ hΨ, k2]
  · have hpres : om (g, 1) Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := (T.weil.isUSplitting).pres _ _ hΨ
    have k2 := law₂ e₂ he₂ 1 1 g₀ g hL 1 (Subgroup.one_mem _) (e₁ Ψ) (he₁.maps Ψ hΨ)
    simp only [one_mul, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] at k2
    apply smul_right_injective _ hc0
    show c • e (om (g, 1) Ψ) = c • om₁ (g₀, 1) (e Ψ)
    rw [← hc _ hpres, ← map_smul, ← hc _ hΨ, LinearMap.comp_apply, LinearMap.comp_apply, law₁ g Ψ hΨ, k2]

end GlobalTheory.ThK.EvInvALoc

namespace GlobalTheory.ThK.EvInvALoc

open scoped Classical in

theorem evInvA : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.LemF.EvInvA := by
  intro hP F E _ _ _ _ _ σ B b a' G G₁ H H' cfg e hev ei ev hloc X om om' om₁ om₁' T T₁ v l hl
  obtain ⟨hU, hL⟩ := global_laws hP F E σ B b a' G G₁ H H' cfg e hev X om om' om₁ om₁' T T₁
  have P := Inhab.pairV T
  have P₁ := Inhab.pairV T₁
  have hA := GlobalTheory.T.theta_action_exists hP
  have hM := T.geo.hM
  have hM₁ := T₁.geo.hM
  obtain ⟨hei, hevv, hpure⟩ := hloc
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  obtain ⟨r₀, hr₀, hr₀t⟩ := GlobalTheory.PureFactor.exists_rest_factor v f G.M.vac hM.std
  obtain ⟨r₁, hr₁, hr₁t⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) G₁.M.vac hM₁.std
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
  have hupd : ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), ∀ w, Function.update G.M.vac v φ w ∈ SB _ := by
    intro φ hφ w
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact hφ
    · rw [Function.update_of_ne hw]
      exact (hM.vac w).1
  have hupd₁ : ∀ φ ∈ SB (Fin b × Fin (b + a') → Fv F v), ∀ w, Function.update G₁.M.vac v φ w ∈ SB _ := by
    intro φ hφ w
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact hφ
    · rw [Function.update_of_ne hw]
      exact (hM₁.vac w).1
  have hRest : ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), Rest (evFin F v) φ r₀ := fun φ hφ =>
    ⟨hr₀, by
      rw [hr₀t φ]
      exact GlobalTheory.TensUniq.pure_mem_schA f _ (hupd φ hφ) (GlobalTheory.PureFactor.update_eventually _ v φ hM.std)⟩
  have hRest₁ : ∀ φ ∈ SB (Fin b × Fin (b + a') → Fv F v), Rest (evFin F v) φ r₁ := fun φ hφ =>
    ⟨hr₁, by
      rw [hr₁t φ]
      exact GlobalTheory.TensUniq.pure_mem_schA (ei f) _ (hupd₁ φ hφ) (GlobalTheory.PureFactor.update_eventually _ v φ hM₁.std)⟩
  have hevSB : ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), ev v φ ∈ SB _ := by
    intro φ hφ
    rw [← (hevv v).2]
    exact Submodule.mem_map_of_mem hφ
  have hev_pure : ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      e (tens (evFin F v) φ r₀) = tens (evFin F v) (ev v φ) r₁ := by
    intro φ hφ
    have hc : ∀ᶠ w in cofinite, Function.update G.M.vac v φ w = G.M.vac w := by
      filter_upwards [Filter.eventually_cofinite_ne v] with w hw
      rw [Function.update_of_ne hw]
    have hfun : (fun w => ev w (Function.update G.M.vac v φ w)) = Function.update G₁.M.vac v (ev v φ) := by
      funext w
      by_cases hw : w = v
      · subst hw
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hw, (hevv w).1]
    rw [hr₀t φ, hpure f _ (hupd φ hφ) hc, hfun, hr₁t]

  have key : ∀ (Tg : Fn F (b + 2) (b + 2 + a') → Fn F (b + 2) (b + 2 + a')) (Sg : Fn F b (b + a') → Fn F b (b + a')),
      (∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e (Tg Φ) = Sg (e Φ)) →
      ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), ∀ φ₁ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      Acts (evFin F v) Tg φ φ₁ → ∀ ψ₁ : (Fin b × Fin (b + a') → Fv F v) → ℂ, Acts (evFin F v) Sg (ev v φ) ψ₁ →
      ev v φ₁ = ψ₁ := by
    intro Tg Sg hTS φ hφ φ₁ hφ₁ hT ψ₁ hS
    apply GlobalTheory.ThK.EvZeroFinLoc.eq_of_tens_eq_of_ne_zero v r₁ hr₁ hr₁0
    rw [← hev_pure φ₁ hφ₁, ← hT r₀ (hRest φ hφ), hTS _ (hRest φ hφ).2, hev_pure φ hφ,
      hS r₁ (hRest₁ _ (hevSB φ hφ))]
  have one_at : ∀ {n : ℕ} (Y : Spc F E n), (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun Y =>
    (UAtSub σ Y (evFin F v)).one_mem
  refine ⟨fun u hu huv φ hφ => ?_, fun g₀ g hLv hg hg₀ φ hφ => ?_⟩
  · congr 1
    exact key (om (u, 1)) (fun Ψ => Ψ) (hU u hu) φ hφ _ (locOp_mem v _ φ)
      (acts_locOp_om hA P huv (one_at G.W) hφ) (ev v φ) (fun _ _ => rfl)
  · have h2 := key (om (g, 1)) (om₁ (g₀, 1)) (hL g₀ g hLv) φ hφ _ (locOp_mem v _ φ)
      (acts_locOp_om hA P hg (one_at G.W) hφ) _ (acts_locOp_om hA P₁ hg₀ (one_at G₁.W) (hevSB φ hφ))
    rw [h2]
    exact hl g₀ hg₀ (ev v φ) (hevSB φ hφ)

end GlobalTheory.ThK.EvInvALoc
