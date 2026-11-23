import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaIntegralCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.ThK.EvAt0.PolD GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open Classical

private theorem heisLine_hasDerivAt {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : SInf F κ) (g : ℝ → SInf F κ) (hg : ∀ t : ℝ, ⇑(g t) = schrF (trP F κ) (t • w) ⇑f) (T : SInf F κ →L[ℂ] ℂ) :
    HasDerivAt (fun t : ℝ => T (g t)) (T (dOp w.1 w.2 f)) 0 := by
  have hP := isPairing_trP (F := F) κ
  have h := GlobalTheory.HeisDer.hasDerivAt_heis w.1 (linL w.2) (trP F κ w.1 w.2 / 2) f T
  have hL : ∀ x, linL w.2 x = trP F κ x w.2 := fun x => linL_apply _ _
  have e1 : (fun x => ((linL w.2 x : ℝ) : ℂ)) = lin w.2 := by
    funext x
    rw [linL_apply]
    rfl
  rw [e1] at h
  convert h using 3 with t
  · ext y
    rw [hg t, SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.HeisDer.hasTemperateGrowth_phase _ _ _),
      SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul, schrF, Prod.smul_fst, Prod.smul_snd,
      hP.smulR, hP.smulR, hP.smulL, hL]
    congr 4
    ring
  all_goals rfl

theorem _root_.GlobalTheory.T.standard_evaluation_model_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), IsStd B.ψ → M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
      (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ),
      (∀ v, ev v (M.vac v) = M₁.vac v) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (z : Matrix (Fin n₁) (Fin d₁) (AE F E)) (f : SInf F (Fin n × Fin d)),
      ei (dOp (coordI M (incM F ι * z * (incM F ι')ᵀ)).1 (coordI M (incM F ι * z * (incM F ι')ᵀ)).2 f) =
        dOp (coordI M₁ z).1 (coordI M₁ z).2 (ei f) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hψ hM hM₁ he ei ev hevac hloc z f
  set u := incM F ι * z * (incM F ι')ᵀ with hu
  ext y
  have h1 := heisLine_hasDerivAt (coordI M u) f
    (fun t => locOpInf (M.co.rho B.ψ (partInf F (realAd F t • u))) f) (fun t => by
      rw [(locOpInf_rho M.co hψ _ f).2, ← coordI_smul]
      rfl) ((GlobalTheory.ArchUniqStd.evAt y).comp ei)
  have h2 := heisLine_hasDerivAt (coordI M₁ z) (ei f)
    (fun t => locOpInf (M₁.co.rho B.ψ (partInf F (realAd F t • z))) (ei f)) (fun t => by
      rw [(locOpInf_rho M₁.co hψ _ (ei f)).2, ← coordI_smul]
      rfl) (GlobalTheory.ArchUniqStd.evAt y)
  refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_))
  have h3 := GlobalTheory.ConeInfNe.arch_heis hψ hM hM₁ he ei ev hevac hloc (realAd F t • z) f
  rw [Matrix.mul_smul, Matrix.smul_mul] at h3
  simp only [ContinuousLinearMap.comp_apply]
  rw [h3]
