import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleNormIntegralFractionalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBStabilizerEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBStabilizerSecondStatement
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped Classical nonZeroDivisors
open GlobalTheory.Doubling (absE)
open GlobalTheory.LocIdeal (locId)

noncomputable section

namespace GlobalTheory.ConeConv

theorem intOK_pure : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (μK : Measure K) (μ : Measure (AE F E)ˣ), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))) (φ : ∀ v : Pl F, (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ),
    (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
    IntOK B G.M' om' e' K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (pure f φ) := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hpe μK μ hμK hμ f φ hφ hφv y
  obtain ⟨g, 𝔞, h𝔞, hgm, hinv, hint, hb⟩ :=
    GlobalTheory.T.seesaw_type_b_stabilizer_evaluation hP B G G₁ H H' hC e' he' K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hpe f φ hφ hφv y
  have hM := GlobalTheory.T.seesaw_type_b_stabilizer_second hP B G G₁ H H' hC e' he' K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hpe f φ hφ hφv y
  have hz : 2 ≤ (a - (b + 2)) / 2 + 1 := by have := hT.geo.eBig; omega
  obtain ⟨μi, hμi⟩ := exists_haar_idelesAt E (evI F)
  have hTate := GlobalTheory.T.idele_norm_integral_fractional_ideal μ hμ μi hμi _ hz g hgm hinv (hint μi hμi) 𝔞 h𝔞

  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := eh.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := eh.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI := hμ
  haveI := hμK
  haveI : SigmaFinite μ := inferInstance

  obtain ⟨K₀, -, -, hK₀, hc, -, -⟩ := GlobalTheory.StabHaar.stabEx hP F E σ B (b + 2) G.V' G.q (b + 2 - G.q) hT.base hT.geo.hV'
  have eK : K = K₀ := Subgroup.ext fun x => (hK x).trans (hK₀ x).symm
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 (eK ▸ hc)
  haveI : IsFiniteMeasure μK := inferInstance
  refine ⟨fun k => ?_, ?_⟩
  · exact hTate.mono' (hM.comp_measurable measurable_prodMk_left).aestronglyMeasurable
      (ae_of_all _ (hb k))
  · refine (integrable_const (∫ l, g l * (if ∀ v : Pl F, compFin F E v (l : AE F E) ∈ locId v 𝔞 then (1 : ℝ) else 0) *
        (absE F E l : ℝ) ^ ((a - (b + 2)) / 2 + 1) ∂μ)).mono' hM.integral_prod_right'.aestronglyMeasurable
      (ae_of_all _ fun k => norm_integral_le_of_norm_le hTate (ae_of_all _ (hb k)))

end GlobalTheory.ConeConv
