import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteAndIsInvInvariantOfContinuousIntegrab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralIdeleMajorantFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarMeasureUnfoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEvaluationTripleCaseA

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThetaSumCone

theorem tsum_lintegral_le' {α ι : Type} [MeasurableSpace α] (μ : Measure α) (g : ι → α → ENNReal) :
    ∑' i, ∫⁻ a, g i a ∂μ ≤ ∫⁻ a, ∑' i, g i a ∂μ := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => le_trans ?_ (lintegral_mono fun a => ENNReal.sum_le_tsum s)
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact le_trans (add_le_add le_rfl ih) (le_lintegral_add _ _)

theorem tsum_integral_integral_mul {K L ι : Type} [MeasurableSpace K] [MeasurableSpace L] [Countable ι]
    (μK : Measure K) (μ : Measure L) [SFinite μK] [SFinite μ]
    (f : K → L → ι → ℂ) (w : L → ℂ)
    (hf : ∀ i, AEStronglyMeasurable (fun p : K × L => f p.1 p.2 i) (μK.prod μ))
    (hw : AEStronglyMeasurable w μ)
    (hs : ∑' i, ∫⁻ k, ∫⁻ l, ‖f k l i‖ₑ * ‖w l‖ₑ ∂μ ∂μK ≠ ⊤) :
    ∑' i, ∫ k, ∫ l, f k l i * w l ∂μ ∂μK = ∫ k, ∫ l, w l * ∑' i, f k l i ∂μ ∂μK := by
  let g : ι → K × L → ℂ := fun i p => f p.1 p.2 i * w p.2
  have hw2 : AEStronglyMeasurable (fun p : K × L => w p.2) (μK.prod μ) := by
    first
    | exact hw.comp_snd
    | exact hw.snd
    | exact hw.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_snd)
  have hgm : ∀ i, AEStronglyMeasurable (g i) (μK.prod μ) := fun i => (hf i).mul hw2
  have hlin : ∀ i, ∫⁻ p, ‖g i p‖ₑ ∂(μK.prod μ) = ∫⁻ k, ∫⁻ l, ‖f k l i‖ₑ * ‖w l‖ₑ ∂μ ∂μK := by
    intro i
    rw [lintegral_prod _ (hgm i).enorm]
    simp only [g, enorm_mul]
  have hsum : ∑' i, ∫⁻ p, ‖g i p‖ₑ ∂(μK.prod μ) ≠ ⊤ := by simpa only [hlin] using hs
  have hint : ∀ i, Integrable (g i) (μK.prod μ) := fun i =>
    ⟨hgm i, lt_of_le_of_lt (ENNReal.le_tsum i) (lt_top_iff_ne_top.2 hsum)⟩
  have hGm : AEStronglyMeasurable (fun p => ∑' i, g i p) (μK.prod μ) :=
    (AEMeasurable.tsum fun i => (hgm i).aemeasurable).aestronglyMeasurable
  have hG : Integrable (fun p => ∑' i, g i p) (μK.prod μ) := by
    refine ⟨hGm, ?_⟩
    calc ∫⁻ p, ‖∑' i, g i p‖ₑ ∂(μK.prod μ) ≤ ∫⁻ p, ∑' i, ‖g i p‖ₑ ∂(μK.prod μ) :=
          lintegral_mono fun p => enorm_tsum_le_tsum_enorm
      _ = ∑' i, ∫⁻ p, ‖g i p‖ₑ ∂(μK.prod μ) := lintegral_tsum fun i => (hgm i).enorm
      _ < ⊤ := lt_top_iff_ne_top.2 hsum
  calc ∑' i, ∫ k, ∫ l, f k l i * w l ∂μ ∂μK = ∑' i, ∫ p, g i p ∂(μK.prod μ) :=
        tsum_congr fun i => (integral_prod _ (hint i)).symm
    _ = ∫ p, ∑' i, g i p ∂(μK.prod μ) := (integral_tsum hgm hsum).symm
    _ = ∫ k, ∫ l, ∑' i, g i (k, l) ∂μ ∂μK := integral_prod _ hG
    _ = _ := by
        congr 1; funext k; congr 1; funext l
        simp only [g]; rw [tsum_mul_right, mul_comm]

theorem ideleTop' (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsTopologicalGroup (AE F E)ˣ ∧ LocallyCompactSpace (AE F E)ˣ ∧ SecondCountableTopology (AE F E)ˣ ∧
    T2Space (AE F E)ˣ := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact ⟨inferInstance, Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology, inferInstance⟩

theorem thetaSum_cone_exch : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ x : UA σ G₁.V.J × UA σ G₁.W.J,
      thetaSum F (fun y => ∫ k, ∫ l, om₁ x (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ))) y * (X.ν l : ℂ) *
          ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ ∂μK) =
        ∫ k, ∫ l, (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) *
          thetaSum F (om₁ x (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)))) ∂μ ∂μK := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Ψ hΨ x
  haveI := hμ
  haveI := hμK

  obtain ⟨v1, v2, v3, v4⟩ := ideleTop' F E
  haveI := v1; haveI := v2; haveI := v3; haveI := v4
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩

  obtain ⟨g, hg1, -, hgc, -⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := (1 : (AE F E)ˣ)))
    isClosed_empty (Set.disjoint_empty _)
  have hgcont : Continuous fun y => ((g y : ℝ) : ℂ) := Complex.continuous_ofReal.comp g.continuous
  have hgint : Integrable (fun y => ((g y : ℝ) : ℂ)) μ :=
    hgcont.integrable_of_hasCompactSupport (hgc.comp_left Complex.ofReal_zero)
  have hg1' : ((g 1 : ℝ) : ℂ) ≠ 0 := by rw [hg1 rfl]; simp
  obtain ⟨hσ, hinv⟩ := GlobalTheory.sigmaFinite_and_isInvInvariant_of_continuous_integrable _ μ _ hgcont hg1' hgint

  have hKeq : K = GlobalTheory.StabHaar.stabK (σ := σ) B G.V :=
    Subgroup.ext fun g => (hK g).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B G.V g).symm
  have hKc : IsCompact (K : Set (UA σ G.V.J)) := by
    have hX := hT.geo.hV
    obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B (b + 2) G.V _ _ hT.base hX
    rw [hKeq]
    exact hCc.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B G.V (GlobalTheory.T.isClosed_adelic_lattice_closure F E (b + 2) G.V hX.lat)) hsub
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  haveI : IsFiniteMeasure μK := ⟨isCompact_univ.measure_lt_top⟩
  haveI : SigmaFinite μK := inferInstance
  haveI : SFinite μK := by
    first
    | exact MeasureTheory.instSFiniteOfSigmaFinite
    | exact @MeasureTheory.instSFiniteOfSigmaFinite _ _ μK _
  haveI := hσ
  haveI := hinv
  haveI : SFinite μ := by
    first
    | exact MeasureTheory.instSFiniteOfSigmaFinite
    | exact @MeasureTheory.instSFiniteOfSigmaFinite _ _ μ _
  haveI : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

  have hab : 1 < (b + 2 - a') / 2 := by have := hT.geo.eBig; omega
  set s : ℝ := (((b + 2 - a') / 2 : ℕ) : ℝ) with hs_def
  have hs : 1 < s := by rw [hs_def]; exact_mod_cast hab

  set w : (AE F E)ˣ → ℂ := fun l => (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) with hw_def
  have hνc : Continuous fun l : (AE F E)ˣ => (X.ν l : ℂ) := by
    have h : Continuous fun l : (AE F E)ˣ => X.ν l := by
      have : Continuous fun l : (AE F E)ˣ => X.α l * (X.β l)⁻¹ :=
        hT.chars.heckeα.1.mul hT.chars.heckeβ.1.inv
      convert this using 2 with l
      simp [Chars.ν, div_eq_mul_inv]
    exact continuous_subtype_val.comp h
  have hwc : Continuous w :=
    hνc.mul ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow _)
  have hwn : ∀ l, ‖w l‖ₑ = ENNReal.ofReal ((absE F E l : ℝ) ^ s) := by
    intro l
    rw [← ofReal_norm_eq_enorm, hw_def]
    congr 1
    rw [norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (NNReal.coe_nonneg _), hs_def, Real.rpow_natCast]

  obtain ⟨U, hU, hbd⟩ := GlobalTheory.T.stabilizer_evaluation_triple_case_a hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' om₁ om₁' hT hT₁ Ψ hΨ x
  obtain ⟨N, hN⟩ := GlobalTheory.T.lintegral_idele_majorant_finite F E μ hμ s hs U hU
  obtain ⟨C, hCt, hCb⟩ := hbd N

  have hTate : ∫⁻ l, GlobalTheory.XTermMaj.maj F E N U (l : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ s) ∂μ < ⊤ := by
    rw [← lintegral_inv_eq_self (μ := μ)]
    convert hN using 3 with l
    congr 2
    rw [map_inv, NNReal.coe_inv, Real.inv_rpow (NNReal.coe_nonneg _), Real.rpow_neg (NNReal.coe_nonneg _)]
  set f : K → (AE F E)ˣ → (Fin b × Fin (b + a') → F) → ℂ := fun k l ξ =>
    om₁ x (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ))) (fun i => algebraMap F (AF F) (ξ i)) with hf_def
  have hsum : ∑' ξ, ∫⁻ k, ∫⁻ l, ‖f k l ξ‖ₑ * ‖w l‖ₑ ∂μ ∂μK ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.mul_lt_top hCt.lt_top hTate)
      (measure_lt_top μK Set.univ)))
    calc ∑' ξ, ∫⁻ k, ∫⁻ l, ‖f k l ξ‖ₑ * ‖w l‖ₑ ∂μ ∂μK
        ≤ ∫⁻ k, ∑' ξ, ∫⁻ l, ‖f k l ξ‖ₑ * ‖w l‖ₑ ∂μ ∂μK := tsum_lintegral_le' _ _
      _ ≤ ∫⁻ k, ∫⁻ l, ∑' ξ, ‖f k l ξ‖ₑ * ‖w l‖ₑ ∂μ ∂μK :=
          lintegral_mono fun k => tsum_lintegral_le' _ _
      _ = ∫⁻ k, ∫⁻ l, (∑' ξ, ‖f k l ξ‖ₑ) * ‖w l‖ₑ ∂μ ∂μK := by
          simp_rw [ENNReal.tsum_mul_right]
      _ ≤ ∫⁻ k : K, ∫⁻ l, C * (GlobalTheory.XTermMaj.maj F E N U (l : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ s)) ∂μ ∂μK := by
          refine lintegral_mono fun k => lintegral_mono fun l => ?_
          rw [hwn, ← mul_assoc]
          exact mul_le_mul' (hCb k.1 k.2 l) le_rfl
      _ = (C * ∫⁻ l, GlobalTheory.XTermMaj.maj F E N U (l : AE F E) * ENNReal.ofReal ((absE F E l : ℝ) ^ s) ∂μ) * μK Set.univ := by
          rw [lintegral_const_mul' _ _ hCt, lintegral_const]
  have key := tsum_integral_integral_mul μK μ f w
    (fun ξ => GlobalTheory.T.config_A_haar_measure_unfold hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Ψ hΨ x ξ)
    hwc.aestronglyMeasurable hsum
  simp only [thetaSum]
  simpa only [f, w, mul_assoc] using key

end GlobalTheory.ThetaSumCone

end
