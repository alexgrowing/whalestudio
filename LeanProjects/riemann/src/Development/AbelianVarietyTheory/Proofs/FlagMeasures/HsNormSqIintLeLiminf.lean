import Mathlib
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOrbitalIntegralEqInvDegSmulStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IintEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FolnerLower

section LinAlg

variable {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

omit [FiniteDimensional ℂ G] in
theorem hs_eq_sum (A : H →L[ℂ] G) : hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ H i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hs_adjoint [CompleteSpace H] [CompleteSpace G] (A : H →L[ℂ] G) :
    hsNormSq (ContinuousLinearMap.adjoint A) = hsNormSq A := by
  rw [hs_eq_sum, hs_eq_sum]
  have h1 : ∀ j, ‖ContinuousLinearMap.adjoint A (stdOrthonormalBasis ℂ G j)‖ ^ 2 =
      ∑ i, ‖⟪stdOrthonormalBasis ℂ H i, ContinuousLinearMap.adjoint A (stdOrthonormalBasis ℂ G j)⟫_ℂ‖ ^ 2 :=
    fun j => ((stdOrthonormalBasis ℂ H).sum_sq_norm_inner_right _).symm
  have h2 : ∀ i, ‖A (stdOrthonormalBasis ℂ H i)‖ ^ 2 =
      ∑ j, ‖⟪A (stdOrthonormalBasis ℂ H i), stdOrthonormalBasis ℂ G j⟫_ℂ‖ ^ 2 :=
    fun i => ((stdOrthonormalBasis ℂ G).sum_sq_norm_inner_left _).symm
  simp_rw [h1, h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]

omit [FiniteDimensional ℂ G] in
theorem hs_isom_comp (U : G →L[ℂ] G) (hU : ∀ v, ‖U v‖ = ‖v‖) (A : H →L[ℂ] G) :
    hsNormSq (U.comp A) = hsNormSq A := by
  rw [hs_eq_sum, hs_eq_sum]
  simp [hU]

theorem hs_unitary [CompleteSpace H] [CompleteSpace G] (U : G →L[ℂ] G) (hU : ∀ v, ‖U v‖ = ‖v‖)
    (V : H →L[ℂ] H) (hV : ∀ v, ‖ContinuousLinearMap.adjoint V v‖ = ‖v‖) (A : H →L[ℂ] G) :
    hsNormSq (U.comp (A.comp V)) = hsNormSq A := by
  rw [hs_isom_comp U hU, ← hs_adjoint, ContinuousLinearMap.adjoint_comp, hs_isom_comp _ hV, hs_adjoint]

omit [FiniteDimensional ℂ G] in
theorem hs_continuous : Continuous (hsNormSq : (H →L[ℂ] G) → ℝ) := by
  have : (hsNormSq : (H →L[ℂ] G) → ℝ) = fun A => ∑ i, ‖A (stdOrthonormalBasis ℂ H i)‖ ^ 2 :=
    funext hs_eq_sum
  rw [this]
  fun_prop

end LinAlg

theorem exists_compact_approx {X E : Type} [PseudoMetricSpace X] [ProperSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ μ' : Measure X) [SFinite μ] [SFinite μ'] (S S' : Set X) (hS : IsClosed S) (hS' : IsClosed S')
    (h0 : μ Sᶜ = 0) (h0' : μ' S'ᶜ = 0) (F : X × X → E) (hF : Integrable F (μ.prod μ')) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ C C' : Set X, IsCompact C ∧ C ⊆ S ∧ IsCompact C' ∧ C' ⊆ S' ∧
      ∀ A A' : Set X, MeasurableSet A → MeasurableSet A' → C ⊆ A → C' ⊆ A' →
        ‖∫ p, F p ∂((μ.restrict A).prod (μ'.restrict A')) - ∫ p, F p ∂(μ.prod μ')‖ < δ := by
  obtain ⟨o⟩ := ‹Nonempty X›
  let K : ℕ → Set (X × X) := fun n =>
    ((S ∩ Metric.closedBall o n) ×ˢ (S' ∩ Metric.closedBall o n))ᶜ
  have hKm : ∀ n, MeasurableSet (K n) := fun n =>
    ((hS.inter Metric.isClosed_closedBall).measurableSet.prod
      (hS'.inter Metric.isClosed_closedBall).measurableSet).compl
  have hKa : Antitone K := by
    intro m n hmn
    have hb : Metric.closedBall o (m : ℝ) ⊆ Metric.closedBall o n :=
      Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
    exact Set.compl_subset_compl.2
      (Set.prod_mono (Set.inter_subset_inter_right _ hb) (Set.inter_subset_inter_right _ hb))
  have hlim := tendsto_setIntegral_of_antitone (f := fun p => ‖F p‖) (μ := μ.prod μ') hKm hKa
    ⟨0, hF.norm.integrableOn⟩
  have hnull : (μ.prod μ') (⋂ n, K n) = 0 := by
    have hsub : (⋂ n, K n) ⊆ (Sᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ S'ᶜ) := by
      intro p hp
      by_contra hc
      simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true, true_and,
        not_or, not_not] at hc
      obtain ⟨n, hn⟩ := exists_nat_ge (max (dist p.1 o) (dist p.2 o))
      exact Set.mem_iInter.1 hp n ⟨⟨hc.1, (le_max_left _ _).trans hn⟩, hc.2, (le_max_right _ _).trans hn⟩
    refine measure_mono_null hsub (measure_union_null ?_ ?_) <;> rw [Measure.prod_prod]
    · rw [h0, zero_mul]
    · rw [h0', mul_zero]
  rw [setIntegral_measure_zero _ hnull] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  refine ⟨S ∩ Metric.closedBall o n, S' ∩ Metric.closedBall o n,
    (isCompact_closedBall o n).inter_left hS, Set.inter_subset_left,
    (isCompact_closedBall o n).inter_left hS', Set.inter_subset_left, fun A A' hA hA' hCA hCA' => ?_⟩
  rw [Measure.prod_restrict, ← integral_add_compl (hA.prod hA') hF, sub_add_cancel_left, norm_neg]
  refine (norm_integral_le_integral_norm _).trans_lt (lt_of_le_of_lt ?_ hn)
  refine setIntegral_mono_set hF.norm.integrableOn (Eventually.of_forall fun p => norm_nonneg _)
    (HasSubset.Subset.eventuallyLE ?_)
  exact Set.compl_subset_compl.2 (Set.prod_mono hCA hCA')

theorem le_liminf_of_ratio (b : ENNReal) (hb : b ≠ ⊤) (u m m' n n' : ℕ → ENNReal)
    (hn : ∀ j, 0 < n j ∧ n j < ⊤) (hn' : ∀ j, 0 < n' j ∧ n' j < ⊤)
    (h : Tendsto (fun j => m j / n j) atTop (𝓝 1)) (h' : Tendsto (fun j => m' j / n' j) atTop (𝓝 1))
    (hu : ∀ j, b * (m j * m' j) ≤ u j) : b ≤ liminf (fun j => u j / (n j * n' j)) atTop := by
  have ht : Tendsto (fun j => b * (m j / n j * (m' j / n' j))) atTop (𝓝 (b * (1 * 1))) :=
    ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul h (Or.inl one_ne_zero) h' (Or.inl one_ne_zero))
      (Or.inr hb)
  rw [mul_one, mul_one] at ht
  rw [← ht.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun j => ?_)
  have e : b * (m j / n j * (m' j / n' j)) = b * (m j * m' j) / (n j * n' j) := by
    simp only [div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl (hn j).1.ne') (Or.inl (hn j).2.ne)]
    ring
  rw [e]
  exact ENNReal.div_le_div_right (hu j) _

variable {k r : ℕ}

theorem measurableSet_rmul_image {t : Mat k r} (ht : IsUnit t.det) {A : Set (Mt k r)}
    (hA : MeasurableSet A) : MeasurableSet (rmulM t '' A) := by
  have : rmulM t '' A = rmulM t⁻¹ ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have : rmulM t⁻¹ (rmulM t y) = y := Matrix.mul_nonsing_inv_cancel_right t (Matrix.of y) ht
      rw [Set.mem_preimage, this]; exact hy
    · intro hx
      exact ⟨_, hx, Matrix.nonsing_inv_mul_cancel_right t (Matrix.of x) ht⟩
  rw [this]
  exact (continuous_rmulM _).measurable hA

theorem subset_rmul_image {t : Mt k r} (ht : IsUnit (Matrix.of t : Mat k r).det) {C Oc Om : Set (Mt k r)}
    (h : ∀ c ∈ C, ∀ x ∈ Oc, lmulM (Matrix.of c) x ∈ Om) (hO : invM t ∈ Oc) :
    C ⊆ rmulM (Matrix.of t) '' Om := fun c hc =>
  ⟨_, h c hc _ hO, Matrix.nonsing_inv_mul_cancel_right (Matrix.of t) (Matrix.of c) ht⟩

theorem hsNormSq_Iint_le_liminf : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ Om Om' : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om → IsFolner (Sset k r z') μS' Om' → ∀ x ∈ DD σ w, ∀ y ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∀ γ ∈ Greg k r z z', ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' γ)) ≤ Filter.liminf (fun j => (∫⁻ p, ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' (Matrix.of (act2 γ p)))) ∂(μS.prod μS')) / (μS (Om j) * μS' (Om' j))) Filter.atTop := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hS hS' Om Om' hF hF'
    x hx y hy ξ ξ' γ hγ
  have hint := (GlobalTheory.T.besselOrbitalIntegral_eq_inv_deg_smul k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' y hy x hx ξ ξ' γ hγ).1
  have hcl := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hS.1 hS.2.1).2.2.2.1
  have hcl' := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z' hS'.1 hS'.2.1).2.2.2.1
  have hP := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hS.1 hS.2.1 hS.2.2.1
  have hP' := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z' c' π' hS'.1 hS'.2.1 hS'.2.2.1
  have hinv := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hS.1 hS.2.1 μS).1 hS.2.2.2.1).2
  have hinv' := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z' hS'.1 hS'.2.1 μS').1 hS'.2.2.2.1).2
  haveI := hS.2.2.2.1.1
  haveI := hS'.2.2.2.1.1
  have h0 := hS.2.2.2.1.2.2.1
  have h0' := hS'.2.2.2.1.2.2.1
  refine ENNReal.le_of_forall_nnreal_lt fun b hb => ?_
  have hb' : (b : ℝ) < hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' γ) := by
    rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg b.coe_nonneg] at hb
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    ((hs_continuous (H := Wq) (G := Wp)).continuousAt.eventually (lt_mem_nhds hb'))
  obtain ⟨C, C', hC, hCS, hC', hCS', happ⟩ := exists_compact_approx μS μS'
    {x | Matrix.of x ∈ Sset k r z} {x | Matrix.of x ∈ Sset k r z'} hcl.2.1 hcl'.2.1 h0 h0' _ hint hδ
  obtain ⟨Oc, hOc, hlim⟩ := hF.2 C hC hCS
  obtain ⟨Oc', hOc', hlim'⟩ := hF'.2 C' hC' hCS'
  refine le_liminf_of_ratio b ENNReal.coe_ne_top _ _ _ _ _ (fun j => (hF.1 j).2.2.2)
    (fun j => (hF'.1 j).2.2.2) hlim hlim' fun j => ?_
  have e1 : μS (Oc j) = μS (invM ⁻¹' Oc j) := by
    rw [← Measure.map_apply measurable_invM (hOc j).1, hinv]
  have e2 : μS' (Oc' j) = μS' (invM ⁻¹' Oc' j) := by
    rw [← Measure.map_apply measurable_invM (hOc' j).1, hinv']
  rw [e1, e2, ← Measure.prod_prod, ← lintegral_indicator_const
    ((measurable_invM (hOc j).1).prod (measurable_invM (hOc' j).1))]
  have hae : ∀ᵐ p ∂(μS.prod μS'), Matrix.of p.1 ∈ Sset k r z ∧ Matrix.of p.2 ∈ Sset k r z' :=
    (Measure.quasiMeasurePreserving_fst.ae (p := fun x => Matrix.of x ∈ Sset k r z) h0).and
      (Measure.quasiMeasurePreserving_snd.ae (p := fun x => Matrix.of x ∈ Sset k r z') h0')
  refine lintegral_mono_ae (hae.mono fun p hp => ?_)
  by_cases hm : p ∈ (invM ⁻¹' Oc j) ×ˢ (invM ⁻¹' Oc' j)
  swap
  · rw [Set.indicator_of_notMem hm]; exact zero_le
  rw [Set.indicator_of_mem hm, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hu : IsUnit (Matrix.of p.1 : Mat k r).det := WeylGroupFacts.isUnit_of_uh (hcl.1 hp.1)
  have hu' : IsUnit (Matrix.of p.2 : Mat k r).det := WeylGroupFacts.isUnit_of_uh (hcl'.1 hp.2)
  have heq := GlobalTheory.T.Iint_equivariant_alt k r σ w a μG d z c π μS z' c' π' μS' hStd hS hS' x y ξ ξ' (Om j) (Om' j)
    (hF.1 j).1 (hF'.1 j).1 γ hγ.1 _ hp.1 _ hp.2
  have ha : (Matrix.of (act2 γ p) : Mat k r) = Matrix.of p.1 * γ * (Matrix.of p.2)⁻¹ := rfl
  rw [ha, heq, hs_unitary _ (hP.2.1.2.1 _ hp.1)]
  · refine (hball ?_).le
    rw [dist_eq_norm]
    exact happ _ _ (measurableSet_rmul_image hu (hF.1 j).1) (measurableSet_rmul_image hu' (hF'.1 j).1)
      (subset_rmul_image hu (hOc j).2.2 hm.1) (subset_rmul_image hu' (hOc' j).2.2 hm.2)
  · rw [← (hP'.2.2.1 _ hp.2).2, ContinuousLinearMap.adjoint_adjoint]
    exact hP'.2.1.2.1 _ hp.2

end GlobalTheory.SgInf.FolnerLower
