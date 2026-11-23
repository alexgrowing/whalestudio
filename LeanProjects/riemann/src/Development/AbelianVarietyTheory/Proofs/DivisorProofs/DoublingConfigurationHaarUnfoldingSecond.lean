import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureIwasawaQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedBisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviConjugationHaarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerLeviCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentStatement

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.IwasawaLine

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem iwasawa_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    ∃ (μN : Measure (unip σ G.V H)) (c : ENNReal), μN.IsHaarMeasure ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ φ : UA σ G.V.J → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂G.M.μ = c * ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ∫⁻ n, φ (n.1 * m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂μN ∂G₁.M.μ ∂μ ∂μK := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ K μK μ hK hμK hμ m hm
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : SecondCountableTopology (AE F E) := e.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (AE F E)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (AE F E)ˣ := Units.isEmbedding_embedProduct.t2Space
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.T.adelic_unitary_locally_compact_hausdorff F E σ (b + 2) G.V.J
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.T.adelic_unitary_locally_compact_hausdorff F E σ b G₁.V.J
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : BorelSpace (UA σ G₁.V.J) := ⟨rfl⟩
  haveI := hμ
  haveI := hG₁.hM.haar
  haveI := hG.hM.haar
  haveI := hμK
  haveI : SigmaFinite μ := inferInstance
  haveI : SigmaFinite G₁.M.μ := inferInstance
  haveI : (μ.prod G₁.M.μ).IsHaarMeasure := inferInstance
  have hKc : IsCompact (K : Set (UA σ G.V.J)) := by
    have hKe : (K : Set (UA σ G.V.J)) = (GlobalTheory.StabHaar.stabK (σ := σ) B G.V : Set _) := by
      ext g; exact (hK g).trans (GlobalTheory.StabHaar.isStab_stabK B G.V g).symm
    obtain ⟨C, hC1, hC2⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B (b + 2) G.V _ _ hB hG.hV
    rw [hKe]
    exact hC1.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B G.V
      (GlobalTheory.LatHatClosed.isClosed_latHat F E _ G.V hG.hV.lat)) hC2
  obtain ⟨hmul, hcont⟩ := GlobalTheory.T.levi_section_multiplicative F E σ B b a' G G₁ H H' hC hB hG hG₁ m hm
  have h11 : m 1 1 = 1 := by
    have h := hmul 1 1 1 1
    rw [one_mul, one_mul] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  let j : ((AE F E)ˣ × UA σ G₁.V.J) →* UA σ G.V.J :=
    { toFun := fun x => m x.1 x.2, map_one' := h11, map_mul' := fun x y => hmul _ _ _ _ }
  let δ : ((AE F E)ˣ × UA σ G₁.V.J) →* ℝ≥0 := (powMonoidHom (b + 1)).comp ((absE F E).comp (MonoidHom.fst _ _))
  have hδc : Continuous δ :=
    (continuous_pow (b + 1)).comp (GlobalTheory.Doubling.continuous_absE.comp continuous_fst)
  have hδ : ∀ x, δ x = absE F E x.1 ^ (b + 1) := fun x => rfl
  obtain ⟨hNc, hemb⟩ := GlobalTheory.T.unipotent_radical_closed_bis F E σ B b a' G G₁ H H' hC hB hG hG₁ m hm
  haveI : LocallyCompactSpace (unip σ G.V H) := hNc.locallyCompactSpace
  let μN : Measure (unip σ G.V H) := Measure.haar
  obtain ⟨c, hc0, hcT, hform⟩ := GlobalTheory.T.haar_measure_iwasawa_quotient (UA σ G.V.J) ((AE F E)ˣ × UA σ G₁.V.J) (unip σ G.V H) K j δ
    G.M.μ μN μK (μ.prod G₁.M.μ) hG.hM.haar inferInstance hμK inferInstance hKc hcont hδc
    (fun x n hn => GlobalTheory.T.levi_normalizes_unipotent F E σ B b a' G G₁ H H' hC hB hG hG₁ x.1 x.2 (m x.1 x.2) (hm _ _) n hn) hemb
    (fun x f hf => by
      rw [hδ x, ENNReal.coe_pow]
      exact GlobalTheory.T.levi_conjugation_haar F E σ B b a' G G₁ H H' hC hB hG hG₁ μN inferInstance x.1 x.2 (m x.1 x.2) (hm _ _) f hf)
    (fun g => by
      obtain ⟨n, hn, l, g₀, k, hk, rfl⟩ := GlobalTheory.T.stabilizer_levi_compatible F E σ B b a' G G₁ H H' hC hB hG hG₁ K hK m hm g
      exact ⟨n, hn, (l, g₀), k, hk, rfl⟩)
  refine ⟨μN, c, inferInstance, hc0, hcT, fun φ hφ => ?_⟩
  rw [hform φ hφ]
  congr 1
  refine lintegral_congr fun k => ?_
  have hmeas : Measurable fun p : ((AE F E)ˣ × UA σ G₁.V.J) × unip σ G.V H =>
      φ (p.2.1 * j p.1 * k.1) * ((δ p.1 : ℝ≥0) : ℝ≥0∞)⁻¹ := by
    refine (hφ.comp (Continuous.measurable ?_)).mul (Continuous.measurable ?_).inv
    · exact ((continuous_subtype_val.comp continuous_snd).mul (hcont.comp continuous_fst)).mul continuous_const
    · exact ENNReal.continuous_coe.comp (hδc.comp continuous_fst)
  rw [lintegral_prod _ hmeas.lintegral_prod_right'.aemeasurable]
  refine lintegral_congr fun l => lintegral_congr fun g₀ => lintegral_congr fun n => ?_
  have hne : absE F E l ≠ 0 := by
    intro h0
    have h := (absE F E).map_mul l l⁻¹
    rw [mul_inv_cancel, map_one, h0, zero_mul] at h
    exact one_ne_zero h
  have hpos : (0 : ℝ) < (absE F E l : ℝ) := by
    rw [NNReal.coe_pos]; exact pos_iff_ne_zero.2 hne
  show φ (n.1 * m l g₀ * k.1) * ((δ (l, g₀) : ℝ≥0) : ℝ≥0∞)⁻¹ = _
  congr 1
  rw [hδ, show (1 - ((b + 2 : ℕ) : ℝ)) = -((b + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hpos.le,
    Real.rpow_natCast, ENNReal.ofReal_inv_of_pos (by positivity), ← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.IwasawaLine
