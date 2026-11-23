import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsDIffDOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenIntertwinerModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.ThK.ConeEuler GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.ModelPol

theorem ei_dOp_eq_zero_of_inv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (B : Base F E)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁),
    IsStd B.ψ → M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
      (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ),
    (∀ v, ev v (M.vac v) = M₁.vac v) →
    (∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ u ∈ I, At (evI F) u → (∀ t : ℝ, realAd F t • u ∈ I) → ∀ f : SInf F (Fin n × Fin d),
      ei (GlobalTheory.ThK.EvAt0.PolD.dOp (GlobalTheory.ThK.EvAt0.PolD.arc (M.co.e u).1) (GlobalTheory.ThK.EvAt0.PolD.arc (M.co.e u).2) f) = 0 := by
  intro F E _ _ _ _ _ σ n d n₁ d₁ X W X₁ W₁ B M M₁ ι ι' I e hψ hM hM₁ hE ei ev hev hl u _ hu hI f
  classical
  have hg : finPr M.vac ∈ SB _ := finPr_mem _ (fun v => (hM.vac v).1) hM.std
  obtain ⟨y', hy'⟩ := exists_finPr_ne M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hψ
  have hDe : D u f = GlobalTheory.ThK.EvAt0.PolD.dOp (GlobalTheory.ThK.EvAt0.PolD.arc (M.co.e u).1) (GlobalTheory.ThK.EvAt0.PolD.arc (M.co.e u).2) f := by
    ext x
    rw [(hD u hu f).2 x, GlobalTheory.ThK.EvAt0.PolD.dOp_apply]
    rfl
  have hvac : ∀ f' : SInf F (Fin n × Fin d), e (pureA F f' (finPr M.vac)) = pureA F (ei f') (finPr M₁.vac) := fun f' => by
    have := hl f' M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl)
    simp only [hev] at this
    exact this
  have hmem : pureA F f (finPr M.vac) ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, _, hg, rfl⟩
  rw [← hDe]
  refine SchwartzMap.ext fun x => ?_
  have h1 := (hD u hu f).1 _ hg _ (GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hE _ (proj_adm x y'))
  have hc : (fun t : ℝ => ((LinearMap.proj (pt x y') : ((Fin n₁ × Fin d₁ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ e)
      (M.co.rho B.ψ (realAd F t • u) (pureA F f (finPr M.vac)))) = fun _ => e (pureA F f (finPr M.vac)) (pt x y') := by
    funext t
    rw [LinearMap.comp_apply, hE.inv _ (hI t) _ hmem, LinearMap.proj_apply]
  rw [hc] at h1
  have h2 := h1.unique (hasDerivAt_const (0 : ℝ) _)
  rw [LinearMap.comp_apply, LinearMap.proj_apply, hvac, pureA_pt] at h2
  simpa using (mul_eq_zero.1 h2).resolve_right hy'

end GlobalTheory.ThK.ModelPol

end
