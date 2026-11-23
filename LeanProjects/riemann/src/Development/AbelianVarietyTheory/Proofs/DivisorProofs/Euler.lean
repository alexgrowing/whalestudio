import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalFactorDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarStabilizerNormalizedLocalProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEvaluationLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEvaluationKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEvaluationExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEvaluationIsoCaseAStatement

noncomputable section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.ThK.ConeEuler

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem euler (hPr : GlobalTheory.FunPr.Hypotheses₂) (B : Base F E) {b a' : ℕ} (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')) (hC : CfgA B G G₁ H H')
    (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')) (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
    (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ)
    (hloc : ei ≠ 0 ∧ (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (K : Subgroup (UA σ G.V.J)) (hK : IsStab B K)
    (μK : Measure K) (μ : Measure (AE F E)ˣ) [hμK : μK.IsHaarMeasure] [hμ : μ.IsHaarMeasure]
    (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v))) (hμKv : ∀ v, IsNormK K (evFin F v) (μKv v))
    (μEv : ∀ v : Pl F, Measure (idelesAt E (evFin F v))) (hμEv : ∀ v, IsNormE E v (μEv v))
    (μKi : Measure (KAt K (evI F))) (hμKi : IsNormK K (evI F) μKi) (μEi : Measure (idelesAt E (evI F)))
    [hμEi : μEi.IsHaarMeasure] :
    ∃ κ₀ : ℂ, κ₀ ≠ 0 ∧ ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
      G₁.M.IsGood B.ψ →
      (∀ (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ)
        (T : Finset (Pl F)), (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = G.M.vac v) → ∀ y : Fin b × Fin (b + a') → AF F,
        Integrable (fun p : K × (AE F E)ˣ => e (G.M.co.rho B.ψ (shiftA H H' p.2) (om (p.1.1, 1) (pure f φ))) y *
          (X.ν p.2 : ℂ) * ((absE F E p.2 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) (μK.prod μ) ∧
        Multipliable (fun v => coneFin B G.M om v (ev v) K (μKv v) (μEv v) (shiftA H H') X.ν ((b + 2 - a') / 2) (φ v)
          fun i => evFin F v (y i)) ∧
        cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (pure f φ) y =
          κ₀ * coneInfFun B G.M om ei K μKi μEi (shiftA H H') X.ν ((b + 2 - a') / 2) f (fun i => evI F (y i)) *
            ∏' v, coneFin B G.M om v (ev v) K (μKv v) (μEv v) (shiftA H H') X.ν ((b + 2 - a') / 2) (φ v) fun i => evFin F v (y i)) ∧
      ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')), ∃ g : SInf F (Fin b × Fin (b + a')),
        ⇑g = coneInfFun B G.M om ei K μKi μEi (shiftA H H') X.ν ((b + 2 - a') / 2) f ∧
        (f ∈ G.M.Pol B.ψ B.emb → g ∈ G₁.M.Pol B.ψ B.emb) := by
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  by_cases hgood : B.IsGood σ ∧ G.V.IsHerm σ B (b + 2 - G.p) G.p
  swap
  · exact ⟨1, one_ne_zero, fun X om om' hT _ => absurd ⟨hT.base, hT.geo.hV⟩ hgood⟩
  obtain ⟨sK, sμ, sKi, sEi, sv, hmf, hma, hmK, hKv1, hX, κ, hκ, hcyl⟩ :=
    GlobalTheory.T.haar_stabilizer_normalized_local_product F E σ hPr B (b + 2) G.V (b + 2 - G.p) G.p hgood.1 hgood.2 K hK μK μ hμK hμ μKv hμKv μEv hμEv μKi hμKi μEi hμEi
  refine ⟨((κ : ℂ))⁻¹, inv_ne_zero (by exact_mod_cast hκ), fun X om om' hT hM₁ => ⟨?_, fun f =>
    GlobalTheory.T.local_evaluation_iso_case_a F E σ hPr B b a' G G₁ H H' hC e he ei ev hloc K hK μKv hμKv μEv hμEv μKi hμKi μEi hμEi X om om' hT hM₁ f⟩⟩
  intro f φ T hφ hφT y
  haveI := sK
  haveI := sμ
  haveI := sKi
  haveI := sEi
  haveI : SFinite μK := by
    set_option synthInstance.maxHeartbeats 400000 in infer_instance
  haveI : SFinite μ := by
    set_option synthInstance.maxHeartbeats 400000 in infer_instance
  haveI : ∀ v, SigmaFinite ((μKv v).map Subtype.val) := fun v => (sv v).1
  haveI : ∀ v, SigmaFinite ((μEv v).map Subtype.val) := fun v => (sv v).2
  let fa : Unit → UA σ G.V.J × (AE F E)ˣ → ℂ := fun _ q =>
    coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f q.1 q.2 (fun i => evI F (y i))
  let ff : ∀ v : Pl F, UA σ G.V.J × (AE F E)ˣ → ℂ := fun v q =>
    coneFinInt B G.M om v (ev v) (shiftA H H') X.ν ((b + 2 - a') / 2) (φ v) q.1 q.2 (fun i => evFin F v (y i))
  have hI : (fun p : K × (AE F E)ˣ => e (G.M.co.rho B.ψ (shiftA H H' p.2) (om (p.1.1, 1) (pure f φ))) y *
      (X.ν p.2 : ℂ) * ((absE F E p.2 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) = fun p =>
      (∏ w : Unit, fa w (compArch σ G.V.J p.1.1, unitArch F E p.2)) *
        ∏ᶠ v, ff v (compAt σ G.V.J v p.1.1, unitAt E v p.2) := by
    funext p
    rw [Fintype.prod_unique]
    exact GlobalTheory.T.config_a_local_factor_decomposition F E σ hPr B b a' G G₁ H H' hC e he ei ev hloc K hK X om om' hT hM₁ f φ T hφ hφT p.1.1 p.1.2 p.2 y _
  obtain ⟨S₀, C, h1, hC'⟩ := GlobalTheory.T.config_A_evaluation_ext F E σ hPr B b a' G G₁ H H' hC e he ei ev hloc K hK μKv hμKv μEv hμEv μKi hμKi μEi hμEi X om om' hT hM₁ φ T hφ hφT y
  have h1' : ∀ v ∉ S₀, ∀ q ∈ {q : UA σ G.V.J × (AE F E)ˣ | q.1 ∈ KAt K (evFin F v) ∧ q.2 ∈ unitsAt E v},
      ff v q = 1 := fun v hv q hq => h1 v hv q.1 hq.1 q.2 hq.2
  have hfa : ∀ w, Integrable (fa w) ((μKi.map Subtype.val).prod (μEi.map Subtype.val)) := fun _ =>
    (GlobalTheory.T.config_A_evaluation_kernel F E σ hPr B b a' G G₁ H H' hC e he ei ev hloc K hK μKv hμKv μEv hμEv μKi hμKi μEi hμEi X om om' hT hM₁ f _).1
  have hff : ∀ v, Integrable (ff v) (((μKv v).map Subtype.val).prod ((μEv v).map Subtype.val)) := fun v =>
    (GlobalTheory.T.config_A_evaluation_local F E σ hPr B b a' G G₁ H H' hC e he ei ev hloc K hK μKv hμKv μEv hμEv μKi hμKi μEi hμEi X om om' hT hM₁ v (φ v) (hφ v) _).1
  have hS1 : ∀ v ∉ S₀, ((μKv v).map Subtype.val).prod ((μEv v).map Subtype.val)
      {q : UA σ G.V.J × (AE F E)ˣ | q.1 ∈ KAt K (evFin F v) ∧ q.2 ∈ unitsAt E v} = 1 := fun v _ => hKv1 v
  have hint := hcyl.integrable_tensor (𝕜 := ℂ) (fun _ => hma) hmf hmK hX hS1 h1' hfa hff hC'
  have heq := hcyl.integral_tensor_eq_tprod (𝕜 := ℂ) (fun _ => hma) hmf hmK hX hS1 h1' hfa hff hC'
  have hmul := GlobalTheory.RestrMeas.multipliable_integral hmK hS1 h1' hff hC'
  have hfaI : ∫ q, fa () q ∂((μKi.map Subtype.val).prod (μEi.map Subtype.val)) =
      coneInfFun B G.M om ei K μKi μEi (shiftA H H') X.ν ((b + 2 - a') / 2) f (fun i => evI F (y i)) :=
    (GlobalTheory.T.config_A_evaluation_kernel F E σ hPr B b a' G G₁ H H' hC e he ei ev hloc K hK μKv hμKv μEv hμEv μKi hμKi μEi hμEi X om om' hT hM₁ f _).2
  have hffI : ∀ v, ∫ q, ff v q ∂(((μKv v).map Subtype.val).prod ((μEv v).map Subtype.val)) =
      coneFin B G.M om v (ev v) K (μKv v) (μEv v) (shiftA H H') X.ν ((b + 2 - a') / 2) (φ v) (fun i => evFin F v (y i)) := fun v =>
    (GlobalTheory.T.config_A_evaluation_local F E σ hPr B b a' G G₁ H H' hC e he ei ev hloc K hK μKv hμKv μEv hμEv μKi hμKi μEi hμEi X om om' hT hM₁ v (φ v) (hφ v) _).2
  rw [← hI] at hint heq
  have hκ' : (κ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκ
  have hint2 : Integrable (fun p : K × (AE F E)ˣ => e (G.M.co.rho B.ψ (shiftA H H' p.2) (om (p.1.1, 1) (pure f φ))) y *
      (X.ν p.2 : ℂ) * ((absE F E p.2 : ℝ) : ℂ) ^ ((b + 2 - a') / 2)) (μK.prod μ) := by
    rw [ENNReal.smul_def] at hint
    exact (integrable_smul_measure hκ' ENNReal.coe_ne_top).1 hint
  refine ⟨hint2, ?_, ?_⟩
  · simpa only [hffI] using hmul
  · rw [integral_smul_nnreal_measure, Fintype.prod_unique, hfaI] at heq
    simp only [hffI] at heq
    have hc : cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (pure f φ) y = ∫ p : K × (AE F E)ˣ,
        e (G.M.co.rho B.ψ (shiftA H H' p.2) (om (p.1.1, 1) (pure f φ))) y * (X.ν p.2 : ℂ) *
          ((absE F E p.2 : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂(μK.prod μ) := (integral_prod _ hint2).symm
    rw [hc, mul_assoc, ← heq, NNReal.smul_def, Complex.real_smul, ← mul_assoc]
    have : ((κ : ℂ))⁻¹ * ((κ : ℝ) : ℂ) = 1 := by
      rw [show ((κ : ℝ) : ℂ) = (κ : ℂ) from rfl]; exact inv_mul_cancel₀ (by exact_mod_cast hκ)
    rw [this, one_mul]

end GlobalTheory.ThK.ConeEuler
