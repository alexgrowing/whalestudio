import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueHaarDensityAtIdentityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralBigCellHaarDensityConstantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankOneUnitaryIntegrationFormulaExactConstantStatement
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal NNReal

namespace GlobalTheory.DoubleCosetMeasure

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings

variable {k r : ℕ}

attribute [local fun_prop] In.mulM_meas R1.invM_meas In.sgF_meas

theorem map_inv_prod {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)} [SFinite μW] [SFinite μN]
    (hW : B.IsHaarOn (UWset k r z) μW) (hN : B.IsHaarOn (Nset k r) μN)
    (hc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN) :
    ((μW.prod μN).map B2.mulM).map B2.invM = (μW.prod μN).map B2.mulM := by
  have iW := haar_measure_inversion k r _ μW (weyl_subgroup_closed k r z) hW
  have iN := haar_measure_inversion k r _ μN (unipotent_radical_closed k r) hN
  have e : (B2.invM ∘ B2.mulM : Mt k r × Mt k r → Mt k r) = In.m1 ∘ Prod.map B2.invM B2.invM := by
    funext p
    exact Matrix.mul_inv_rev (Matrix.of p.1 : Mat k r) (Matrix.of p.2)
  rw [Measure.map_map R1.invM_meas In.mulM_meas, e,
    ← Measure.map_map In.first_coordinate_map_measurable (R1.invM_meas.prodMap R1.invM_meas),
    ← Measure.map_prod_map _ _ R1.invM_meas R1.invM_meas, iW, iN, In.swap_meas hW hc]

theorem orbital_eq {z z' : Fin (2 * r + k + 1) → ℂ} {μW μN μW' : Measure (Mt k r)}
    [SFinite μW] [SFinite μN] [SFinite μW']
    (hW : B.IsHaarOn (UWset k r z) μW) (hW' : B.IsHaarOn (UWset k r z') μW') (hN : B.IsHaarOn (Nset k r) μN)
    (hc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN) (hc' : ∀ h ∈ UWset k r z', μN.map (conjM h) = μN)
    (g : Mt k r) (f : Mt k r → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p : B.SS k r, f (In.sgF (p, g)) ∂((μW.prod μN).prod (μW'.prod μN)) =
      ∫⁻ p, f (act2 (Matrix.of g) p) ∂((muProd μW μN).prod (muProd μW' μN)) := by
  let Δ : Mt k r × Mt k r → ℝ≥0∞ := fun ab => f (B2.mulM (B2.mulM (ab.1, g), ab.2))
  have hΔ : Measurable Δ := by
    show Measurable fun ab : Mt k r × Mt k r => f (B2.mulM (B2.mulM (ab.1, g), ab.2))
    fun_prop
  have hi := (R1.invM_meas (k := k) (r := r))
  have hm := (In.first_coordinate_map_measurable (k := k) (r := r))
  have r1 : ∫⁻ p : B.SS k r, f (In.sgF (p, g)) ∂((μW.prod μN).prod (μW'.prod μN)) =
      ∫⁻ p : B.SS k r, Δ (Prod.map B2.invM id (Prod.map In.m1 In.m1 p)) ∂((μW.prod μN).prod (μW'.prod μN)) := by
    refine lintegral_congr fun p => congrArg f ?_
    show (Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * (Matrix.of g : Mat k r) *
        Matrix.of p.2.2 * Matrix.of p.2.1 =
      ((Matrix.of p.1.2 : Mat k r) * Matrix.of p.1.1)⁻¹ * (Matrix.of g : Mat k r) *
        ((Matrix.of p.2.2 : Mat k r) * Matrix.of p.2.1)
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc _ (Matrix.of p.2.2 : Mat k r)]
  have r2 : ∫⁻ p, f (act2 (Matrix.of g) p) ∂((muProd μW μN).prod (muProd μW' μN)) =
      ∫⁻ p, Δ (Prod.map id B2.invM p) ∂(((μW.prod μN).map B2.mulM).prod ((μW'.prod μN).map B2.mulM)) := rfl
  rw [r1, r2, ← lintegral_map (f := fun p => Δ (Prod.map B2.invM id p)) (hΔ.comp (hi.prodMap measurable_id))
      (hm.prodMap hm), ← Measure.map_prod_map _ _ hm hm, In.swap_meas hW hc, In.swap_meas hW' hc',
    ← lintegral_map hΔ (hi.prodMap measurable_id), ← lintegral_map hΔ (measurable_id.prodMap hi),
    ← Measure.map_prod_map _ _ hi measurable_id, ← Measure.map_prod_map _ _ measurable_id hi,
    map_inv_prod hW hN hc, map_inv_prod hW' hN hc', Measure.map_id, Measure.map_id]

theorem continuous_dmin (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    Continuous fun g : Mat k r => Dmin k r z z' g l := by
  unfold Dmin
  refine Continuous.matrix_det (Continuous.matrix_submatrix (continuous_matrix fun a b => ?_) _ _)
  unfold Formalism.QuantumDeterminants.Zhat herm
  exact Continuous.dotProduct continuous_const
    (Continuous.matrix_mulVec continuous_const (Continuous.matrix_mulVec continuous_id continuous_const))

theorem measurableSet_greg (z z' : Fin (2 * r + k + 1) → ℂ) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ Greg k r z z'} := by
  have h1 : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := (unitary_group_closed k r).closed
  have hD : ∀ l, Continuous fun x : Mt k r => Dmin k r z z' (Matrix.of x) l := fun l => continuous_dmin z z' l
  have hG : Continuous fun x : Mt k r => Gf k r z z' (Matrix.of x) := by
    unfold Gf
    exact (Complex.continuous_normSq.comp (hD _)).sub (continuous_const.mul (Complex.continuous_normSq.comp (hD _)))
  have h2 : MeasurableSet {x : Mt k r | ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' (Matrix.of x) l ≠ 0} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter fun l => ?_
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun _ => (isOpen_ne_fun (hD l) continuous_const).measurableSet
  exact h1.measurableSet.inter (h2.inter (isOpen_ne_fun hG continuous_const).measurableSet)

theorem bigCell_mem_regular {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') (hs : IsSection k r z z' μsec) {c : Fin r → ℂ} {ζ : ℂ}
    (hc : ∀ a, c a ≠ 0) (hζ : ζ ∈ R1.Om k r z z') : bigCell k r c (μsec ζ) ∈ Greg k r z z' := by
  have hsec := hs.2 ζ hζ
  have hmin := bigCellMinors k r z z' c (μsec ζ) hz hz'
  have hD : ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' (bigCell k r c (μsec ζ)) l ≠ 0 := by
    intro l hl
    have h := hmin.1 ⟨l.val, by omega⟩
    have hl' : (⟨(⟨l.val, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 2)) = l := Fin.ext rfl
    rw [← hl', h]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  refine ⟨bigCellMem k r c _ hc hsec.1, hD, ?_⟩
  have h0 := hD ⟨r, by omega⟩ le_rfl
  have h1 := hmin.2.2 hc
  rw [BigCellHermitian.herm_bigCell _ _ hz hz', hsec.2] at h1
  rw [gFactor k r z z' _ h0]
  unfold GGf
  rw [h1]
  have h2 : Tz k r z * Tz k r z' < Complex.normSq ζ := hζ
  exact mul_ne_zero (Complex.normSq_pos.2 h0).ne' (sub_pos.2 h2).ne'

theorem measurable_weight (T T' : ℝ) :
    Measurable fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal (bcWeight k r T T' q) := by
  simp only [weight_factorization k r T T']
  exact ((In.cW_cont.measurable.comp measurable_fst).mul ((R1.zW_meas k T T').comp measurable_snd)).ennreal_ofReal

theorem ae_dom (z z' : Fin (2 * r + k + 1) → ℂ) :
    ∀ᵐ q ∂(volume.withDensity fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q)),
      (∀ a, q.1 a ≠ 0) ∧ q.2 ∈ R1.Om k r z z' := by
  rw [ae_withDensity_iff (measurable_weight _ _)]
  have hae : ∀ᵐ q : (Fin r → ℂ) × ℂ, q.2 ∈ R1.Om k r z z' ∨ B2.zWeight k (Tz k r z) (Tz k r z') q.2 = 0 := by
    rw [Measure.volume_eq_prod]
    exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin r → ℂ))) (ν := (volume : Measure ℂ))).ae
      (R1.ae_Om z z')
  filter_upwards [hae] with q hq h0
  rw [weight_factorization k r] at h0
  refine ⟨fun a ha => h0 ?_, hq.resolve_right fun h => h0 (by rw [h]; simp)⟩
  have : B2.cWeight k r q.1 = 0 := by
    unfold B2.cWeight
    refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
    rw [ha, norm_zero]
    refine zero_pow ?_
    have := a.isLt
    unfold Mdim
    omega
  rw [this]; simp

theorem isDis_bigCell : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (μG μW μW' : Measure (Mt k r)) (c κ : ℝ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec → 0 < c → 0 < κ → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 → IsHaarOn (UWset k r z') μW' → μW' Set.univ = 1 → AEMeasurable (fun q : (Fin r → ℂ) × ℂ => (Matrix.of.symm (bigCell k r q.1 (μsec q.2)) : Mt k r)) (volume.withDensity fun q => ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q)) ∧ IsDis (Greg k r z z') μG (muProd μW (haarLie (Nset k r) (ENNReal.ofReal κ))) (muProd μW' (haarLie (Nset k r) (ENNReal.ofReal κ))) (ENNReal.ofReal (c * 2 ^ (r + 1) * volUn k ^ 2 / volUn (k - 1) / (Tz k r z * Tz k r z') ^ k / κ ^ 2) • (volume.withDensity fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q)).map fun q => (Matrix.of.symm (bigCell k r q.1 (μsec q.2)) : Mt k r)) := by
  intro k r z z' μsec μG μW μW' c κ hk hz hz' hT hT' hsec hc hκ hG hd hW hW1 hW' hW1'
  have hWb : B.IsHaarOn (UWset k r z) μW := ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW).2.2 z hz hT hk).1 hW
  have hWb' : B.IsHaarOn (UWset k r z') μW' := ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW').2.2 z' hz' hT' hk).1 hW'
  have hN := GlobalTheory.T.haarLie_isHaarOn_unipotentRadical k r (ENNReal.ofReal κ) (ENNReal.ofReal_pos.2 hκ) ENNReal.ofReal_lt_top
  have hN1 := GlobalTheory.T.haarLie_isHaarOn_unipotentRadical k r 1 one_pos ENNReal.one_lt_top
  have hsm : haarLie (Nset k r) (ENNReal.ofReal κ) = ENNReal.ofReal κ • haarLie (Nset k r) 1 := by
    unfold haarLie; rw [one_smul]
  set μN := haarLie (Nset k r) (ENNReal.ofReal κ) with hμN
  have hNb : B.IsHaarOn (Nset k r) μN := (GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μN).2.1.1 hN
  obtain ⟨μb, hbb⟩ := opposite_weyl_haar_exists k r
  have hcl := opposite_weyl_subgroup_closed k r
  have := R1.haar_sigmaFinite hbb
  have := hW.1
  have := hW'.1
  have := hN.1
  have := hN1.1
  have hb : IsHaarOn (B2.UWb k r) μb := ⟨inferInstance, hbb.ne_zero, hbb.conc, hbb.left⟩
  obtain ⟨cb, hcb, hdb, -⟩ := GlobalTheory.T.exists_unique_haarDensity_at_identity _ (B2.UWb k r) μb
    ⟨hcl.closed, hcl.one_mem, hcl.mul_mem, fun a ha => ⟨hcl.inv_mem a ha, Matrix.mul_nonsing_inv a (hcl.unit a ha)⟩⟩ hb
  have hsec' := R1.secF_section hsec
  have hsmm := R1.secF_meas hsec
  have h1 := GlobalTheory.T.lintegral_bigCell_haar_density_constant k r μG μb c cb hc hcb hG hd hb hdb
  have h2 := GlobalTheory.T.rank_one_unitary_integration_formula_exact_constant k r z z' (R1.secF k r z z' μsec) μb μW μW' cb hk hz hz' hT hT' hsec' hcb hb hdb hW hW1 hW' hW1'
  have hconj := b2_conjInvRaw_proof k r z μN hz hT hNb
  have hconj' := b2_conjInvRaw_proof k r z' μN hz' hT' hNb
  have UF := unipotent_weyl_properties
  have h1' : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG =
      ((c / cb * 2 ^ r / κ ^ 2).toNNReal : ℝ≥0∞) * ∫⁻ x : Fin r → ℂ,
      ENNReal.ofReal (B2.cWeight k r x) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f (B2.mulM (B2.mulM (B2.mulM (B2.invM p.1.1, In.bc1 k r x), p.2), p.1.2)) ∂((μN.prod μN).prod μb) := by
    intro f hf
    rw [h1 f hf, hsm]
    simp only [Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure, smul_eq_mul]
    have e : ∀ (x : Fin r → ℂ) (I : ℝ≥0∞), ENNReal.ofReal (B2.cWeight k r x) * (ENNReal.ofReal κ * (ENNReal.ofReal κ * I)) =
        ENNReal.ofReal (κ ^ 2) * (ENNReal.ofReal (B2.cWeight k r x) * I) := by
      intro x I
      rw [pow_two, ENNReal.ofReal_mul hκ.le]; ring
    simp only [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc]
    congr 1
    show _ = ENNReal.ofReal _ * _
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have h2' : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ m, f m ∂μb =
      ((cb * 2 * volUn k ^ 2 / volUn (k - 1) / (Tz k r z * Tz k r z') ^ k).toNNReal : ℝ≥0∞) * ∫⁻ ζ : ℂ,
      ENNReal.ofReal (B2.zWeight k (Tz k r z) (Tz k r z') ζ) * ∫⁻ p : Mt k r × Mt k r,
        f (B2.mulM (B2.mulM (B2.invM p.1, R1.embF k r (R1.secF k r z z' μsec ζ)), p.2)) ∂(μW.prod μW') := h2
  let ψ : (Fin r → ℂ) × ℂ → Mt k r := fun q => B2.mulM (In.bc1 k r q.1, R1.embF k r (R1.secF k r z z' μsec q.2))
  have hψ : Measurable ψ :=
    In.mulM_meas.comp ((In.big_cell_coordinate_measurable.comp measurable_fst).prodMk ((R1.embS_meas hsmm).comp measurable_snd))
  have hdom := ae_dom (k := k) (r := r) z z'
  have hwm := measurable_weight (k := k) (r := r) (Tz k r z) (Tz k r z')
  set ρ := (volume.withDensity fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q)) with hρ
  have hψe : (fun q : (Fin r → ℂ) × ℂ => (Matrix.of.symm (bigCell k r q.1 (μsec q.2)) : Mt k r)) =ᵐ[ρ] ψ := by
    filter_upwards [hdom] with q hq
    show _ = B2.mulM (In.bc1 k r q.1, R1.embF k r (R1.secF k r z z' μsec q.2))
    rw [R1.secF_on hq.2]
    exact (bruhat_big_cell_factorization k r q.1 (μsec q.2)).1
  have hae : AEMeasurable (fun q : (Fin r → ℂ) × ℂ => (Matrix.of.symm (bigCell k r q.1 (μsec q.2)) : Mt k r)) ρ :=
    hψ.aemeasurable.congr hψe.symm
  refine ⟨hae, ?_, ?_, ?_⟩
  · let φ : Mt k r → (Fin r → ℂ) × ℂ := fun x =>
      (fun a => x (esI k r a) (eI k r a), herm (Hpk k r) (Matrix.of x *ᵥ z') z)
    have hφ : Measurable φ := by
      refine Continuous.measurable (Continuous.prodMk (continuous_pi fun a => continuous_apply_apply _ _) ?_)
      unfold herm
      exact Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_const
        (Continuous.matrix_mulVec (continuous_id (X := Mat k r)) continuous_const))
    have hid : (φ ∘ fun q : (Fin r → ℂ) × ℂ => (Matrix.of.symm (bigCell k r q.1 (μsec q.2)) : Mt k r)) =ᵐ[ρ] id := by
      filter_upwards [hdom] with q hq
      refine Prod.ext (funext fun a => ?_) ?_
      · show bigCell k r q.1 (μsec q.2) (esI k r a) (eI k r a) = q.1 a
        unfold bigCell
        rw [dif_pos (show (eI k r a).val < r from a.isLt)]
        exact if_pos rfl
      · show herm (Hpk k r) (bigCell k r q.1 (μsec q.2) *ᵥ z') z = q.2
        rw [BigCellHermitian.herm_bigCell _ _ hz hz', (hsec.2 q.2 hq.2).2]
    have hσ : SigmaFinite (ρ.map fun q : (Fin r → ℂ) × ℂ => (Matrix.of.symm (bigCell k r q.1 (μsec q.2)) : Mt k r)) := by
      refine SigmaFinite.of_map _ hφ.aemeasurable ?_
      rw [hφ.aemeasurable.map_map_of_aemeasurable hae, Measure.map_congr hid, Measure.map_id, hρ]
      infer_instance
    exact inferInstanceAs (SigmaFinite (Real.toNNReal _ • _))
  · have hms : MeasurableSet {x : Mt k r | Matrix.of x ∉ Greg k r z z'} := (measurableSet_greg z z').compl
    rw [Measure.smul_apply, Measure.map_apply_of_aemeasurable hae hms]
    have : ρ ((fun q : (Fin r → ℂ) × ℂ => (Matrix.of.symm (bigCell k r q.1 (μsec q.2)) : Mt k r)) ⁻¹'
        {x : Mt k r | Matrix.of x ∉ Greg k r z z'}) = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hdom)
      intro q hq h
      exact hq (bigCell_mem_regular hz hz' hsec h.1 h.2)
    rw [this, smul_zero]
  · intro f hf
    have e := In.engine (μG := μG) (μN := μN) (μb := μb) (μW := μW) (μW' := μW') (Tz k r z) (Tz k r z') (In.bc1 k r)
      In.big_cell_coordinate_measurable (fun ζ => R1.embF k r (R1.secF k r z z' μsec ζ)) (R1.embS_meas hsmm) _ _ h1' h2'
      (fun x ζ f hf => In.key UF hWb hWb' hconj hconj' (In.bc1 k r x) _ ((UF k r).2.2 x) f hf) f hf
    have hF : Measurable fun g : Mt k r => ∫⁻ p : B.SS k r, f (In.sgF (p, g)) ∂((μW.prod μN).prod (μW'.prod μN)) := by
      have hm : Measurable fun x : Mt k r × B.SS k r => f (In.sgF (x.2, x.1)) := by fun_prop
      exact hm.lintegral_prod_right'
    simp only [← orbital_eq hWb hWb' hNb hconj hconj' _ f hf]
    rw [e, lintegral_smul_measure, Measure.map_congr hψe, lintegral_map hF hψ, hρ,
      lintegral_withDensity_eq_lintegral_mul _ hwm
        (g := fun a => ∫⁻ p : B.SS k r, f (In.sgF (p, ψ a)) ∂((μW.prod μN).prod (μW'.prod μN))) (hF.comp hψ), smul_eq_mul]
    have v1 : ∀ j, 0 < volUn j := fun j => Finset.prod_pos fun i _ => by have := Real.pi_pos; positivity
    have v2 := v1 k
    have v3 := v1 (k - 1)
    congr 1
    · rw [← Real.toNNReal_mul (by positivity)]
      show ENNReal.ofReal _ = _
      congr 1
      field_simp
      ring
    · refine lintegral_congr fun q => ?_
      rw [← weight_factorization k r]
      rfl

end GlobalTheory.DoubleCosetMeasure
