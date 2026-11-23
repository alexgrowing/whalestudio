import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExistsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeFubini

theorem iter_eq {K L Y : Type} [MeasurableSpace K] [MeasurableSpace L] [MeasurableSpace Y]
    (μK : Measure K) (μ : Measure L) (μY : Measure Y) [SFinite μK] [SFinite μ] [SFinite μY]
    (g : K → L → Y → ℂ) (hg : Integrable (fun p : K × (L × Y) => g p.1 p.2.1 p.2.2) (μK.prod (μ.prod μY))) :
    ∫ y, ∫ k, ∫ l, g k l y ∂μ ∂μK ∂μY = ∫ k, ∫ l, ∫ y, g k l y ∂μY ∂μ ∂μK := by
  set h : K × (L × Y) → ℂ := fun p => g p.1 p.2.1 p.2.2 with hh

  have hR : ∫ k, ∫ l, ∫ y, g k l y ∂μY ∂μ ∂μK = ∫ p, h p ∂(μK.prod (μ.prod μY)) := by
    rw [integral_prod h hg]
    refine integral_congr_ae ?_
    filter_upwards [hg.prod_right_ae] with k hk
    exact (integral_prod (fun q : L × Y => g k q.1 q.2) hk).symm

  let e : Y × (K × L) ≃ᵐ K × (L × Y) := MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc
  have he : MeasurePreserving e (μY.prod (μK.prod μ)) (μK.prod (μ.prod μY)) :=
    (measurePreserving_prodAssoc μK μ μY).comp (Measure.measurePreserving_swap)
  have hg' : Integrable (h ∘ e) (μY.prod (μK.prod μ)) := (he.integrable_comp_emb e.measurableEmbedding).2 hg
  have hL : ∫ y, ∫ k, ∫ l, g k l y ∂μ ∂μK ∂μY = ∫ p, h p ∂(μK.prod (μ.prod μY)) := by
    rw [← he.integral_comp e.measurableEmbedding h, integral_prod (fun x => h (e x)) hg']
    refine integral_congr_ae ?_
    filter_upwards [hg'.prod_right_ae] with y hy
    exact (integral_prod (fun q : K × L => g q.1 q.2 y) hy).symm
  rw [hL, hR]

open GlobalTheory.ThK in

theorem coneFub : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      ∀ φ ∈ schA F (Fin b × Fin (b + a')),
      letI : MeasurableSpace (Fin b × Fin (b + a') → AF F) := borel _
      ∀ μY : Measure (Fin b × Fin (b + a') → AF F), μY.IsAddHaarMeasure →
      Integrable (fun p : K × ((AE F E)ˣ × (Fin b × Fin (b + a') → AF F)) => e (G.M.co.rho B.ψ (shiftA H H' p.2.1) (om (p.1.1, 1) Ψ)) p.2.2 * (X.ν p.2.1 : ℂ) *
          ((absE F E p.2.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2) * starRingEnd ℂ (φ p.2.2)) (μK.prod (μ.prod μY)) →
      ∫ y, cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Ψ y * starRingEnd ℂ (φ y) ∂μY =
        ∫ k, ∫ l, (∫ y, e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) y * starRingEnd ℂ (φ y) ∂μY) * (X.ν l : ℂ) *
          ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ ∂μK := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ φ hφ μY hμY hint

  haveI := hμK
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  obtain ⟨K', μK', μ', hK', hKc, -, -⟩ := GlobalTheory.T.theta_stabilizer_exists hKP.base F E σ B (b + 2) G.V (b + 2 - G.p) G.p hT.base hT.geo.hV
  have hKK : K = K' := by ext g; rw [hK g, hK' g]
  have hKc' : IsCompact (K : Set (UA σ G.V.J)) := hKK ▸ hKc
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc'
  haveI : IsFiniteMeasure μK := ⟨IsFiniteMeasureOnCompacts.lt_top_of_isCompact isCompact_univ⟩
  haveI : SFinite μK := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ μK this)

  haveI := hμ
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨eq⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := eq.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := eq.secondCountableTopology
  haveI : T2Space (AE F E) := eq.isEmbedding.t2Space
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SigmaCompactSpace (AE F E)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite μ := @instSFiniteOfSigmaFinite _ _ _ (SigmaFinite.of_isFiniteMeasureOnCompacts μ)

  letI : MeasurableSpace (Fin b × Fin (b + a') → AF F) := borel _
  haveI := hμY
  haveI : SigmaCompactSpace (Fin b × Fin (b + a') → AF F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite μY := @instSFiniteOfSigmaFinite _ _ _ (SigmaFinite.of_isFiniteMeasureOnCompacts μY)
  have key := GlobalTheory.ConeFubini.iter_eq μK μ μY (fun k l y => e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) y * (X.ν l : ℂ) *
    ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) * starRingEnd ℂ (φ y)) hint
  refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans (key.trans ?_)
  · show (∫ k, ∫ l, _ ∂μ ∂μK) * _ = _
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    exact (integral_mul_const _ _).symm
  · refine integral_congr_ae (Eventually.of_forall fun k => integral_congr_ae (Eventually.of_forall fun l => ?_))
    show _ = (∫ y, _ ∂μY) * _ * _
    rw [mul_assoc, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring

end GlobalTheory.ConeFubini
