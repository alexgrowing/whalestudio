import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeAArchimedeanEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeAArchimedeanSecondStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.ThK.ConeEulerInf

theorem cone_inf_iter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.FunPr.Hypotheses₂ → ∀ (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')), IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
    (ei ≠ 0 ∧ (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ (μKv : ∀ v : Pl F, Measure (KAt K (evFin F v))), (∀ v, IsNormK K (evFin F v) (μKv v)) →
    ∀ (μEv : ∀ v : Pl F, Measure (idelesAt E (evFin F v))), (∀ v, IsNormE E v (μEv v)) →
    ∀ (μKi : Measure (KAt K (evI F))), IsNormK K (evI F) μKi → ∀ (μEi : Measure (idelesAt E (evI F))), μEi.IsHaarMeasure →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G₁.M.IsGood B.ψ →
    ∀ (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (y : Fin b × Fin (b + a') → mixedEmbedding.mixedSpace F),
      Integrable (fun q : UA σ G.V.J × (AE F E)ˣ => coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f q.1 q.2 y)
        ((μKi.map Subtype.val).prod (μEi.map Subtype.val)) ∧
      ∫ q : UA σ G.V.J × (AE F E)ˣ, coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f q.1 q.2 y
        ∂((μKi.map Subtype.val).prod (μEi.map Subtype.val)) =
        coneInfFun B G.M om ei K μKi μEi (shiftA H H') X.ν ((b + 2 - a') / 2) f y := by
  intro F E _ _ _ _ _ σ hPr B b a' G G₁ H H' hC e he ei ev hE K hK μKv _ μEv _ μKi hKi μEi hEi X om om' hT hG₁ f y
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI := hKi.1
  haveI : IsProbabilityMeasure μKi := ⟨hKi.2⟩
  haveI : IsFiniteMeasure μKi := inferInstance
  haveI : SigmaFinite μKi := @IsFiniteMeasure.toSigmaFinite _ _ μKi ‹_›
  haveI : SFinite μKi := @instSFiniteOfSigmaFinite _ _ μKi ‹_›
  set z := (b + 2 - a') / 2 with hz
  have hz1 : 1 ≤ z := by
    obtain ⟨k, hk⟩ := hT.geo.even
    have h1 := hT.geo.lt
    have h2 := hT.geo.eBig
    omega

  set h : KAt K (evI F) × idelesAt E (evI F) → ℂ :=
    fun p => coneInfInt B G.M om ei (shiftA H H') X.ν z f p.1.1 p.2.1 y with hh
  have hmeas : Measurable h := GlobalTheory.T.seesaw_type_a_archimedean_evaluation F E σ hPr B b a' G G₁ H H' hC e he ei ev hE K hK X om om' hT hG₁ f y
  obtain ⟨N, hN⟩ := GlobalTheory.ArchIdeleDecay.integrable_absE_pow_div F E σ B hT.base μEi hEi z hz1
  obtain ⟨C, hCb⟩ := GlobalTheory.T.seesaw_type_a_archimedean_second F E σ hPr B b a' G G₁ H H' hC e he ei ev hE K hK X om om' hT hG₁ f y N
  have hint : Integrable h (μKi.prod μEi) := by
    have hg : Integrable (fun p : KAt K (evI F) × idelesAt E (evI F) => (1 : ℝ) *
        (C * ((GlobalTheory.Doubling.absE F E p.2.1 : ℝ) ^ z / (1 + ∑ w, ‖piInf (B.emb w) (p.2.1 : AE F E)‖) ^ N)))
        (μKi.prod μEi) := (integrable_const (1 : ℝ)).mul_prod (hN.const_mul C)
    refine hg.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    have hn : ‖(X.ν p.2.1 : ℂ)‖ = 1 := Circle.norm_coe _
    have hb := hCb p.1.1 p.1.2 p.2.1 p.2.2
    have hpos : 0 < (1 + ∑ w, ‖piInf (B.emb w) (p.2.1 : AE F E)‖) ^ N := by positivity
    simp only [hh, coneInfInt_apply, norm_mul, hn, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      NNReal.abs_eq, one_mul]
    calc _ ≤ C / (1 + ∑ w, ‖piInf (B.emb w) (p.2.1 : AE F E)‖) ^ N * ((GlobalTheory.Doubling.absE F E p.2.1 : ℝ) ^ z) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  have hmK : MeasurableEmbedding (Subtype.val : KAt K (evI F) → UA σ G.V.J) := by
    refine MeasurableEmbedding.subtype_coe (IsClosed.measurableSet ?_)
    have hKe : K = GlobalTheory.StabHaar.stabK B G.V := by
      ext g
      exact hK g
    have h1 : IsClosed (K : Set (UA σ G.V.J)) := by
      rw [hKe]
      exact GlobalTheory.StabHaar.isClosed_stabK B G.V (GlobalTheory.LatHatClosed.isClosed_latHat F E _ G.V hT.geo.hV.lat)
    exact h1.inter (isClosed_UAtSub G.V (evI F))
  have hmE : MeasurableEmbedding (Subtype.val : idelesAt E (evI F) → (AE F E)ˣ) :=
    MeasurableEmbedding.subtype_coe (isClosed_idelesAt (evI F)).measurableSet
  have hprod : (μKi.map Subtype.val).prod (μEi.map Subtype.val) = (μKi.prod μEi).map (Prod.map Subtype.val Subtype.val) :=
    Measure.map_prod_map μKi μEi hmK.measurable hmE.measurable
  rw [hprod]
  refine ⟨(hmK.prodMap hmE).integrable_map_iff.2 hint, ?_⟩
  rw [(hmK.prodMap hmE).integral_map]
  exact integral_prod h hint

end GlobalTheory.ThK.ConeEulerInf
