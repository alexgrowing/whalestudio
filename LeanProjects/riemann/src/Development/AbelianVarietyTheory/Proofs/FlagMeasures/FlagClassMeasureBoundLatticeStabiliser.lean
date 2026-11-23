import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsSatFlagOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryIwasawaIntegrationFormulaRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalIntegralPointsCovolumeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSaturatedIsotropicFlagOfAdaptedBasisStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTotallyIsotropicFlagComplexifiedSaturatedFlagStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGaugeMeasuresIsotropicFlagParabolicStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRankStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlagStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorIntegralModIntegralPointsLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GradedPieceSizesUnipotentLeviCompactMoveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableCosetSectionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetIwasawaSliceOfTransversalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaSliceIndicatorLintegralLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNMKIntegrationPiProductStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagLocalSizesUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRiemannianHaarOnSubgroupMapMulRightUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeepsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroupsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGradedPieceSizesStabiliserMulStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLatticeStabiliserRealGroupMulMemStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLayerProductMeasureMulProdLocalStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagBase.OneClass

theorem covol_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] (N M K : Subgroup G) (hN : IsClosed (N : Set G)) (hM : IsClosed (M : Set G))
    (hK : IsClosed (K : Set G)) (hnorm : ∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N)
    (huniq : ∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1) (hdec : ∀ g, ∃ u ∈ N, ∃ m ∈ M, ∃ k ∈ K, g = u * m * k)
    (μ μN μM μK : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] (δ w : G → ENNReal) (hδ : Measurable δ)
    (h1 : μN (N : Set G)ᶜ = 0) (h2 : μM (M : Set G)ᶜ = 0) (h3 : μK (K : Set G)ᶜ = 0) (h4 : μK Set.univ = 1)
    (hr : ∀ l ∈ K ⊓ M, μM.map (fun g => g * l) = μM) (hδr : ∀ l ∈ K ⊓ M, ∀ m ∈ M, δ (m * l) = δ m)
    (C c R t : ENNReal) (hc0 : c ≠ 0) (hc : c ≠ ⊤) (hR0 : R ≠ 0) (hR : R ≠ ⊤) (ht0 : t ≠ 0) (ht : t ≠ ⊤)
    (hform : ∀ φ : G → ENNReal, Measurable φ →
      C * ∫⁻ g, φ g ∂μ = c * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) ∂μK ∂μM ∂μN)
    (Γ ΓN ΓM A Z : Set G) (hZ : MeasurableSet Z) (hmul : ∀ x ∈ Γ, ∀ y ∈ Γ, x * y ∈ Γ)
    (hΓN : ∀ x ∈ ΓN, x ∈ Γ) (hΓM : ∀ m ∈ ΓM, m ∈ M ∧ ∃ g ∈ Γ, ∃ u ∈ N, g = u * m)
    (hΓN' : ∀ x ∈ ΓN, x ∈ N)
    (hA : ∀ γ ∈ Γ, ∀ g ∈ A, γ * g ∈ A) (hAZ : ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, u * m * k ∈ A → m ∈ Z)
    (hw : ∀ m ∈ M, m ∈ Z → t * δ m ≤ w m) (hcN : covol ΓN μN N ≤ R * t) :
    C * covol Γ μ A ≤ c * R * covol ΓM (μM.withDensity w) M := by
  obtain ⟨σ, hσ, hσ1, hσ2⟩ := GlobalTheory.T.exists_measurable_coset_section' G (K ⊓ M) (by rw [Subgroup.coe_inf]; exact hK.inter hM)
  have hκ : ∀ k, k * (σ k)⁻¹ ∈ K ⊓ M := fun k => by simpa using (K ⊓ M).inv_mem (hσ1 k)
  have key : ∀ DN DM : Set G, MeasurableSet DN → MeasurableSet DM → (∀ x ∈ (N : Set G), ∃ γ ∈ ΓN, γ * x ∈ DN) →
      (∀ x ∈ (M : Set G), ∃ γ ∈ ΓM, γ * x ∈ DM) → C * covol Γ μ A ≤ c * (μN DN * ∫⁻ m in DM ∩ Z, δ m ∂μM) := by
    intro DN DM hDN hDM cN cM
    obtain ⟨D, hD, hiff⟩ := GlobalTheory.T.measurableSet_iwasawa_slice_of_transversal G N M K σ hN.measurableSet hM.measurableSet hK.measurableSet hσ hσ1 hσ2
      hnorm huniq DN (DM ∩ Z) hDN (hDM.inter hZ)
    have hcov : ∀ x ∈ A, ∃ γ ∈ Γ, γ * x ∈ D := by
      intro x hx
      obtain ⟨u, hu, m, hm, k, hk, rfl⟩ := hdec x
      obtain ⟨γM, hγM, hγD⟩ := cM (m * (k * (σ k)⁻¹)) (M.mul_mem hm (hκ k).2)
      obtain ⟨hγM', γ, hγ, u₀, hu₀, rfl⟩ := hΓM γM hγM
      have hu' : u₀ * (γM * u * γM⁻¹) ∈ N := N.mul_mem hu₀ (hnorm _ hγM' _ hu)
      obtain ⟨γN, hγN, hγD'⟩ := cN _ hu'
      have hγ' := hmul _ (hΓN _ hγN) _ hγ
      refine ⟨_, hγ', ?_⟩
      have e : γN * (u₀ * γM) * (u * m * k) = γN * (u₀ * (γM * u * γM⁻¹)) * (γM * m) * k := by group
      have e' : γN * (u₀ * γM) * (u * m * k) =
          γN * (u₀ * (γM * u * γM⁻¹)) * (γM * m * (k * (σ k)⁻¹)) * σ k := by group
      have hσK : σ k ∈ K := by simpa using K.mul_mem (hσ1 k).1 hk
      have hZ' := hA _ hγ' _ hx
      rw [e'] at hZ'
      have hN' := N.mul_mem (hΓN' _ hγN) hu'
      have hM' := M.mul_mem hγM' hm
      rw [e, hiff _ hN' _ hM' _ hk]
      exact ⟨hγD', by rwa [mul_assoc], hAZ _ hN' _ (M.mul_mem hM' (hκ k).2) _ hσK hZ'⟩
    calc C * covol Γ μ A ≤ C * μ D := by
          gcongr
          exact iInf_le_of_le D (iInf_le_of_le hD (iInf_le _ hcov))
      _ = C * ∫⁻ g, D.indicator 1 g ∂μ := by rw [lintegral_indicator_one hD]
      _ ≤ _ := by
          rw [hform _ (measurable_one.indicator hD)]
          gcongr
          exact GlobalTheory.T.iwasawa_slice_indicator_lintegral_le G N M K μN μM μK δ (fun k => k * (σ k)⁻¹) D DN (DM ∩ Z) hδ
            (measurable_id.mul hσ.inv) hDN (hDM.inter hZ) h1 h2 h3 h4 (fun k _ => hκ k) hr hδr
            (fun u hu m hm k hk h => (hiff u hu m hm k hk).1 h)
  have hcR0 : c * R ≠ 0 := mul_ne_zero hc0 hR0
  have hcR : c * R ≠ ⊤ := ENNReal.mul_ne_top hc hR
  rw [show covol ΓM (μM.withDensity w) M = ⨅ (D : Set G) (_ : MeasurableSet D)
    (_ : ∀ x ∈ (M : Set G), ∃ γ ∈ ΓM, γ * x ∈ D), μM.withDensity w D from rfl]
  simp only [ENNReal.mul_iInf_of_ne hcR0 hcR, le_iInf_iff]
  intro DM hDM cM
  have hX : t * ∫⁻ m in DM ∩ Z, δ m ∂μM ≤ μM.withDensity w DM := by
    rw [withDensity_apply _ hDM, ← lintegral_const_mul _ hδ]
    refine le_trans (lintegral_mono_ae ?_) (lintegral_mono_set (μ := μM) (f := w) (Set.inter_subset_left (t := Z)))
    filter_upwards [ae_restrict_mem (hDM.inter hZ), ae_restrict_of_ae (mem_ae_iff.2 h2)] with m hm hm'
    exact hw m hm' hm.2
  by_cases hT : ∫⁻ m in DM ∩ Z, δ m ∂μM = ⊤
  · rw [hT, ENNReal.mul_top ht0, top_le_iff] at hX
    rw [hX, ENNReal.mul_top hcR0]
    exact le_top
  by_cases h0 : ∫⁻ m in DM ∩ Z, δ m ∂μM = 0
  · have hne : covol ΓN μN N ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hR ht) hcN
    have hlt := hne.lt_top
    simp only [covol, iInf_lt_iff] at hlt
    obtain ⟨DN, hDN, cN, -⟩ := hlt
    have := key DN DM hDN hDM cN cM
    rw [h0, mul_zero, mul_zero] at this
    exact this.trans (zero_le)
  calc C * covol Γ μ A ≤ (c * ∫⁻ m in DM ∩ Z, δ m ∂μM) * covol ΓN μN N := by
        rw [show covol ΓN μN N = ⨅ (D : Set G) (_ : MeasurableSet D)
          (_ : ∀ x ∈ (N : Set G), ∃ γ ∈ ΓN, γ * x ∈ D), μN D from rfl]
        simp only [ENNReal.mul_iInf_of_ne (mul_ne_zero hc0 h0) (ENNReal.mul_ne_top hc hT), le_iInf_iff]
        intro DN hDN cN
        refine (key DN DM hDN hDM cN cM).trans_eq (by ring)
    _ ≤ (c * ∫⁻ m in DM ∩ Z, δ m ∂μM) * (R * t) := by gcongr
    _ = c * R * (t * ∫⁻ m in DM ∩ Z, δ m ∂μM) := by ring
    _ ≤ _ := by gcongr

theorem size_nonneg (I : AutInst) (x : I.GA) (A B : Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    0 ≤ Formalism.HN.sizeQ (bas I) (frm I x) A B := by
  unfold Formalism.HN.sizeQ Formalism.HN.htQ Formalism.F.covol
  refine Real.rpow_nonneg ?_ _
  split_ifs <;> positivity

theorem gauge_pos {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) : 0 < c := by
  have hp : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  obtain ⟨r, hr, hr0⟩ := ((h.eventually (lt_mem_nhds hp)).and self_mem_nhdsWithin).exists
  by_contra hc
  exact absurd hr (not_lt.2 (div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hc) ENNReal.toReal_nonneg) (pow_nonneg (le_of_lt hr0) _)))

theorem layerProd_pos (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) {τ : Fin a → ℝ} (h : ∀ i, 0 < τ i) :
    0 < layerProd n f j τ id := by
  unfold layerProd
  simp only [id]
  refine mul_pos (Finset.prod_pos fun i _ => Finset.prod_pos fun k _ => ?_) (Finset.prod_pos fun i _ => ?_)
  · have := h i
    have := h k
    positivity
  · have := h i
    positivity

theorem layerProd_nonneg (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) {τ : Fin a → ℝ} (h : ∀ i, 0 ≤ τ i) :
    0 ≤ layerProd n f j τ id := by
  unfold layerProd
  simp only [id]
  refine mul_nonneg (Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun k _ => ?_)
    (Finset.prod_nonneg fun i _ => ?_)
  · have := h i
    have := h k
    positivity
  · have := h i
    positivity

theorem measurable_layerProd (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) :
    Measurable fun τ : Fin a → ℝ => layerProd n f j τ id := by
  unfold layerProd
  simp only [id]
  refine Measurable.mul (Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun k _ => ?_)
    (Finset.measurable_prod _ fun i _ => ?_) <;> fun_prop

theorem locSize_nonneg {n a : ℕ} (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (g : Matrix (Fin n) (Fin n) ℂ) (i : Fin a) : 0 ≤ locSize j W g i := by
  have h : ∀ V, 0 ≤ detOn g V := fun V => by
    unfold detOn
    split_ifs <;> positivity
  exact Real.rpow_nonneg (div_nonneg (h _) (h _)) _

theorem pi_compl {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)]
    (μ : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] (H : ∀ i, Subgroup (G i))
    (h : ∀ i, μ i (H i : Set (G i))ᶜ = 0) :
    Measure.pi μ (Subgroup.pi Set.univ H : Set (∀ i, G i))ᶜ = 0 := by
  rw [← mem_ae_iff]
  have : ∀ᵐ x ∂(Measure.pi μ), ∀ i, x i ∈ (H i : Set (G i)) :=
    ae_all_iff.2 fun i => Measure.tendsto_eval_ae_ae.eventually (mem_ae_iff.2 (h i))
  filter_upwards [this] with x hx i _ using hx i

theorem bound : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (p q : ℕ), HasSig I p q → ∀ (c : InfinitePlace I.F → ℝ) (c₀ : InfinitePlace I₀.F → ℝ), IsGaugeAll I c → IsGaugeAll I₀ c₀ → ∀ B : Set (Fin a → ℝ), MeasurableSet B → B ⊆ simplexH a → ENNReal.ofReal (∏ v, c v) * covol (flagGroup I xf S) (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) {g | sizesAt I xf S g ∈ B} ≤ ENNReal.ofReal (cIw p q j ^ I.f * (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ ((I.f : ℝ) * dimN I.n j / 2)) * (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2)) * slabVol I.E (j i) (Λ i)) * (ENNReal.ofReal (∏ v, c₀ v) * covol (latGroup I₀ x₀) (Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) Set.univ) * ∫⁻ τ in B, ENNReal.ofReal (dens I.n I.f j τ) := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hj had p q hsig c c₀ hc hc₀ B hB hBs
  by_cases hA : {g | sizesAt I xf S g ∈ B} = ∅
  · have : covol (flagGroup I xf S) (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) {g | sizesAt I xf S g ∈ B} = 0 := by
      rw [hA]
      refine le_antisymm (iInf_le_of_le ∅ (iInf_le_of_le MeasurableSet.empty (iInf_le_of_le (by simp) ?_))) zero_le
      simp
    rw [this, mul_zero]
    exact zero_le
  obtain ⟨g₀, hg₀⟩ := Set.nonempty_iff_ne_empty.2 hA
  have hsat := GlobalTheory.T.isSaturatedIsotropicFlag_of_adaptedBasis I I₀ e xf a j S Λ x₀ T T' T₀ hj had
  have hiso := GlobalTheory.T.isTotallyIsotropicFlag_complexified_saturatedFlag I _ a j S hsat
  obtain ⟨-, hrd, hrd1, hf, hcard, -⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I
  have hf0 : I.f ≠ 0 := by omega
  have hex := fun v => GlobalTheory.T.exists_gauge_measures_isotropicFlag_parabolic I.n (I.ε v) a j _ hj (hiso v)
  choose μN hσN hμN using fun v => (hex v).1
  choose μM hσM hμM using fun v => (hex v).2.1
  choose μK hK0 hK1 hKl using fun v => (hex v).2.2
  haveI : ∀ v, IsProbabilityMeasure (μK v) := fun v => ⟨hK1 v⟩
  have hgN := fun v => GlobalTheory.T.isotropicFlagUnipotentRadical_closed_subgroup_keeps I.n (I.ε v) a j _ (hiso v)
  have hgM := fun v => GlobalTheory.T.isotropicFlagLevi_maxCompact_closed_subgroups I.n (I.ε v) a (flagAt I S v)
  choose N hN using fun v => (hgN v).1
  choose M hM using fun v => (hgM v).1
  choose K hK using fun v => (hgM v).2.2.1
  have mN : ∀ x : I.Ginf, x ∈ Subgroup.pi Set.univ N ↔ ∀ v, x v ∈ flagN (I.ε v) (flagAt I S v) := fun x => by
    simp only [Subgroup.mem_pi, Set.mem_univ, true_imp_iff, ← hN, SetLike.mem_coe]
  have mM : ∀ x : I.Ginf, x ∈ Subgroup.pi Set.univ M ↔ ∀ v, x v ∈ flagM (I.ε v) (flagAt I S v) := fun x => by
    simp only [Subgroup.mem_pi, Set.mem_univ, true_imp_iff, ← hM, SetLike.mem_coe]
  have mK : ∀ x : I.Ginf, x ∈ Subgroup.pi Set.univ K ↔ ∀ v, x v ∈ maxK (I.ε v) := fun x => by
    simp only [Subgroup.mem_pi, Set.mem_univ, true_imp_iff, ← hK, SetLike.mem_coe]
  haveI : ∀ v, PolishSpace (Formalism.REAL.UJ (I.ε v)) := fun v => by
    haveI : PolishSpace (Matrix (Fin I.n) (Fin I.n) ℂ) := inferInstanceAs (PolishSpace (Fin I.n → Fin I.n → ℂ))
    exact (Formalism.REAL.isClosedEmbeddingMatrix I.n (I.ε v)).1.polishSpace
  have hiw := fun v => GlobalTheory.T.iwasawa_decomposition_unitary_isotropicFlag I.n (I.ε v) a j _ (hiso v)
  have hdec : ∀ g : I.Ginf, ∃ u ∈ Subgroup.pi Set.univ N, ∃ m ∈ Subgroup.pi Set.univ M,
      ∃ k ∈ Subgroup.pi Set.univ K, g = u * m * k := by
    intro g
    choose u hu m hm k hk he using fun v => (hiw v).1 (g v)
    exact ⟨u, (mN _).2 hu, m, (mM _).2 hm, k, (mK _).2 hk, funext he⟩
  have hmove : ∀ u ∈ Subgroup.pi Set.univ N, ∀ m ∈ Subgroup.pi Set.univ M, ∀ k ∈ Subgroup.pi Set.univ K, ∀ i,
      sizesAt I xf S (u * m * k) i ^ I.f = sizesAt I xf S 1 i ^ I.f * ∏ v, locSize j (flagAt I S v) (uMat (m v)) i :=
    fun u hu m hm k hk i => GlobalTheory.T.gradedPieceSizes_unipotent_levi_compact_move I xf a j hj S hsat u m k ((mN _).1 hu) ((mM _).1 hm) ((mK _).1 hk) i
  have hs0 : ∀ g i, 0 ≤ sizesAt I xf S g i := fun g i => size_nonneg I _ _ _
  have hm1 : ∀ m ∈ Subgroup.pi Set.univ M, ∀ i,
      sizesAt I xf S m i ^ I.f = sizesAt I xf S 1 i ^ I.f * ∏ v, locSize j (flagAt I S v) (uMat (m v)) i := by
    intro m hm i
    simpa using hmove 1 (one_mem _) m hm 1 (one_mem _) i
  have hs1 : ∀ i, 0 < sizesAt I xf S 1 i := by
    intro i
    obtain ⟨u, hu, m, hm, k, hk, rfl⟩ := hdec g₀
    refine (hs0 1 i).lt_of_ne' fun h0 => ?_
    have h := hmove u hu m hm k hk i
    rw [h0, zero_pow hf0, zero_mul] at h
    exact ((hBs hg₀).2 i).1.ne' (pow_eq_zero_iff hf0 |>.1 h)
  let s : I.Ginf → Fin a → ℝ := fun m i =>
    (sizesAt I xf S 1 i ^ I.f * ∏ v, locSize j (flagAt I S v) (uMat (m v)) i) ^ ((I.f : ℝ)⁻¹)
  have hloc : ∀ v, Measurable fun (g : Formalism.REAL.UJ (I.ε v)) (i : Fin a) => locSize j (flagAt I S v) (uMat g) i :=
    fun v => measurable_pi_iff.2 fun i => GlobalTheory.T.measurable_flagLocalSizes_unitary _ _ _ _ _ i
  have hsm : Measurable s := measurable_pi_iff.2 fun i =>
    (measurable_const.mul (Finset.measurable_prod _ fun v _ =>
      (GlobalTheory.T.measurable_flagLocalSizes_unitary _ _ _ _ _ i).comp (measurable_pi_apply v))).pow_const _
  have hs : ∀ u ∈ Subgroup.pi Set.univ N, ∀ m ∈ Subgroup.pi Set.univ M, ∀ k ∈ Subgroup.pi Set.univ K,
      s m = sizesAt I xf S (u * m * k) := by
    intro u hu m hm k hk
    funext i
    simp only [s]
    rw [← hmove u hu m hm k hk i, Real.pow_rpow_inv_natCast (hs0 _ i) hf0]
  have hsM : ∀ m ∈ Subgroup.pi Set.univ M, s m = sizesAt I xf S m := fun m hm => by
    simpa using hs 1 (one_mem _) m hm 1 (one_mem _)
  let δ : ∀ v, Formalism.REAL.UJ (I.ε v) → ENNReal := fun v m =>
    ENNReal.ofReal (layerProd I.n 1 j (locSize j (flagAt I S v) (uMat m)) id)
  have hδ : ∀ v, Measurable (δ v) := fun v => ((measurable_layerProd I.n 1 j).comp (hloc v)).ennreal_ofReal
  have hL1 := layerProd_pos I.n I.f j hs1
  have htδ : ∀ m ∈ Subgroup.pi Set.univ M, ENNReal.ofReal (layerProd I.n I.f j (sizesAt I xf S 1) id) *
      ∏ v, δ v (m v) = ENNReal.ofReal (layerProd I.n I.f j (sizesAt I xf S m) id) := by
    intro m hm
    rw [GlobalTheory.T.flagLayerProductMeasure_mul_prod_local _ I.n I.f a j _ _ (fun v => locSize j (flagAt I S v) (uMat (m v))) (hm1 m hm),
      ENNReal.ofReal_mul hL1.le,
      ENNReal.ofReal_prod_of_nonneg fun v _ => layerProd_nonneg _ _ _ (locSize_nonneg _ _ _)]
  have ht0 : ENNReal.ofReal (layerProd I.n I.f j (sizesAt I xf S 1) id) ≠ 0 := by simpa using hL1
  have hcp := fun v => gauge_pos (hc v)
  have hIw := SatModel.cIw_pos p q j
  have hR : 0 < (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ ((I.f : ℝ) * dimN I.n j / 2) :=
    Real.rpow_pos_of_pos (by rw [hrd]; linarith) _
  let F : (Fin a → ℝ) → ENNReal := B.indicator fun τ => ENNReal.ofReal (layerProd I.n I.f j τ id)
  have hF : Measurable F := (measurable_layerProd I.n I.f j).ennreal_ofReal.indicator hB
  have hform := GlobalTheory.T.iwasawaNMKIntegration_pi_product _ (fun v => Formalism.REAL.UJ (I.ε v)) (fun v => Formalism.REAL.muG (I.ε v)) μN μM μK
    (fun v => ENNReal.ofReal (c v)) (fun _ => ENNReal.ofReal (cIw p q j)) δ (fun v => by simpa using hcp v)
    (fun v => ENNReal.ofReal_ne_top) hδ (fun v φ hφ => GlobalTheory.T.unitary_iwasawa_integration_formula_real_place I.n (I.ε v) p q (hsig v).1 (hsig v).2 a j hj _
      (hiso v) (c v) (μN v) (μM v) (μK v) (hc v) (hμN v) (hμM v) (hK0 v) (hK1 v) (hKl v) φ hφ)
  rw [← ENNReal.ofReal_prod_of_nonneg fun v _ => (hcp v).le, Finset.prod_const, Finset.card_univ, hcard,
    ← ENNReal.ofReal_pow hIw.le] at hform
  have hrad := GlobalTheory.T.unipotentRadical_integral_points_covolume I xf a j hj S hsat μN hμN
  rw [ENNReal.ofReal_mul hR.le] at hrad
  have hlevi := GlobalTheory.T.levi_factor_integral_mod_integral_points_le I I₀ e xf a j S Λ x₀ T T' T₀ hj had μM c₀ hμM hc₀ F hF
  have eN : {g : I.Ginf | ∀ v, g v ∈ flagN (I.ε v) (flagAt I S v)} =
      ((Subgroup.pi Set.univ N : Subgroup I.Ginf) : Set I.Ginf) := Set.ext fun x => (mN x).symm
  have eM : {g : I.Ginf | ∀ v, g v ∈ flagM (I.ε v) (flagAt I S v)} =
      ((Subgroup.pi Set.univ M : Subgroup I.Ginf) : Set I.Ginf) := Set.ext fun x => (mM x).symm
  rw [eN] at hrad
  rw [eM] at hlevi
  have hmain := covol_le (G := I.Ginf) (Subgroup.pi Set.univ N) (Subgroup.pi Set.univ M) (Subgroup.pi Set.univ K)
    (isClosed_set_pi fun v _ => (show IsClosed (N v : Set (Formalism.REAL.UJ (I.ε v))) by
      rw [hN]; exact (hgN v).2.1))
    (isClosed_set_pi fun v _ => (show IsClosed (M v : Set (Formalism.REAL.UJ (I.ε v))) by
      rw [hM]; exact (hgM v).2.1))
    (isClosed_set_pi fun v _ => (show IsClosed (K v : Set (Formalism.REAL.UJ (I.ε v))) by
      rw [hK]; exact (hgM v).2.2.2.1))
    (fun m hm u hu => (mN _).2 fun v => (hgM v).2.2.2.2 _ ((mM _).1 hm v) _ ((mN _).1 hu v))
    (fun u hu m hm h => funext fun v => (hiw v).2 _ ((mN _).1 hu v) _ ((mM _).1 hm v) ((mK _).1 h v)) hdec
    (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) (Measure.pi μN) (Measure.pi μM) (Measure.pi μK)
    (fun m => ∏ v, δ v (m v)) (fun m => F (sizesAt I xf S m))
    (Finset.measurable_prod _ fun v _ => (hδ v).comp (measurable_pi_apply v))
    (pi_compl _ _ fun v => by rw [hN]; exact (hμN v).1) (pi_compl _ _ fun v => by rw [hM]; exact (hμM v).1)
    (pi_compl _ _ fun v => by rw [hK]; exact hK0 v) measure_univ
    (fun l hl => (measurePreserving_pi μM μM (f := fun v g => g * l v) fun v => ⟨measurable_mul_const _,
      GlobalTheory.T.isRiemannianHaarOnSubgroup_map_mul_right_unitary I.n (I.ε v) (M v) _ (μM v) (by rw [hM]; exact (hgM v).2.1) (by rw [hM]; exact hμM v) (l v)
        (hl.2 v trivial) ((mK _).1 hl.1 v)⟩).map_eq)
    (fun l hl m hm => by
      refine (ENNReal.mul_right_inj ht0 ENNReal.ofReal_ne_top).1 ?_
      rw [htδ _ hm, htδ _ (mul_mem hm hl.2), ← hsM m hm, hs 1 (one_mem _) m hm l hl.1, one_mul])
    _ _ _ _ (by simpa using pow_pos hIw _) ENNReal.ofReal_ne_top (by simpa using hR) ENNReal.ofReal_ne_top ht0
    ENNReal.ofReal_ne_top hform (flagGroup I xf S)
    {g : I.Ginf | ∃ γ ∈ I.GFset, γ.1 = g ∧ xf⁻¹ * γ.2 * xf ∈ I.Kset ∧ ∀ v, g v ∈ flagN (I.ε v) (flagAt I S v)}
    (leviGroup I xf S) {g | sizesAt I xf S g ∈ B} (s ⁻¹' B)
    (hsm hB) (GlobalTheory.T.flagLatticeStabiliserRealGroup_mul_mem I xf a S)
    (fun x ⟨γ, h1, h2, h3, h4⟩ => ⟨⟨γ, h1, h2, h3⟩, fun v => (hgN v).2.2 _ (h4 v)⟩)
    (fun m ⟨h1, g, hg, u, hu, h2⟩ => ⟨(mM _).2 h1, g, hg, u, (mN _).2 hu, h2⟩)
    (fun x ⟨γ, h1, h2, h3, h4⟩ => (mN _).2 h4)
    (fun γ hγ g hg => by
      rw [Set.mem_setOf_eq, GlobalTheory.T.flagGradedPieceSizes_stabiliser_mul I xf a j S hsat γ hγ g]
      exact hg)
    (fun u hu m hm k hk h => by
      rw [Set.mem_preimage, hs u hu m hm k hk]
      exact h)
    (fun m hm hZ => by
      rw [Set.mem_preimage, hsM m hm] at hZ
      rw [htδ m hm]
      simp only [F, Set.indicator_of_mem hZ, le_refl]) hrad
  have hint : ∫⁻ τ in {τ : Fin a → ℝ | ∀ i, 0 < τ i}, F τ * ENNReal.ofReal (∏ i, 2 * (I.f : ℝ) * j i / τ i) ≤
      ∫⁻ τ in B, ENNReal.ofReal (dens I.n I.f j τ) := by
    rw [← lintegral_indicator hB]
    refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun τ => ?_)
    by_cases hτ : τ ∈ B
    · simp only [F, Set.indicator_of_mem hτ, FlagMeas.dens]
      rw [ENNReal.ofReal_mul (layerProd_pos _ _ _ fun i => ((hBs hτ).2 i).1).le]
    · simp only [F, Set.indicator_of_notMem hτ, zero_mul, le_refl]
  refine hmain.trans ?_
  rw [ENNReal.ofReal_mul (pow_pos hIw _).le, mul_assoc _ (∏ i, _), mul_assoc _ (_ * _) (∫⁻ τ in B, _)]
  gcongr
  refine hlevi.trans ?_
  gcongr

end GlobalTheory.FlagBase.OneClass
