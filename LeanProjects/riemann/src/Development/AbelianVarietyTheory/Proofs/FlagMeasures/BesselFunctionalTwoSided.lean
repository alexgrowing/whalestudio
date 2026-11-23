import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.TruncNorm

section Abstract

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
variable {Wq : Type*} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

omit [CompleteSpace H] in

theorem integrable_inner_prod {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {F : α → H} {G : β → H} (hF : Integrable F μ) (hG : Integrable G ν) :
    Integrable (fun p : α × β => ⟪F p.1, G p.2⟫_ℂ) (μ.prod ν) := by
  refine (hF.norm.mul_prod hG.norm).mono' (hF.1.comp_fst.inner hG.1.comp_snd) ?_
  exact Filter.Eventually.of_forall fun p => norm_inner_le_norm _ _

theorem inner_integral_integral {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {F : α → H} {G : β → H} (hF : Integrable F μ) (hG : Integrable G ν) :
    ⟪∫ s, F s ∂μ, ∫ t, G t ∂ν⟫_ℂ = ∫ p, ⟪F p.1, G p.2⟫_ℂ ∂(μ.prod ν) := by
  rw [integral_prod _ (integrable_inner_prod hF hG)]
  simp_rw [integral_inner hG]
  rw [← inner_conj_symm, ← integral_inner hF, ← integral_conj]
  simp_rw [inner_conj_symm]

omit [CompleteSpace H] in

theorem integrable_coord_smul {μ : Measure α} [IsFiniteMeasure μ] {u : α → H} {a : α → Wp} {C D : ℝ}
    (hu : AEStronglyMeasurable u μ) (ha : AEStronglyMeasurable a μ)
    (huC : ∀ᵐ s ∂μ, ‖u s‖ ≤ C) (haD : ∀ᵐ s ∂μ, ‖a s‖ ≤ D) (η : Wp) :
    Integrable (fun s => ⟪a s, η⟫_ℂ • u s) μ := by
  refine Integrable.of_bound ((ha.inner aestronglyMeasurable_const).smul hu) (D * ‖η‖ * C) ?_
  filter_upwards [huC, haD] with s h1 h2
  rw [norm_smul]
  have h3 : ‖⟪a s, η⟫_ℂ‖ ≤ D * ‖η‖ := (norm_inner_le_norm _ _).trans (by gcongr)
  exact mul_le_mul h3 h1 (norm_nonneg _) ((norm_nonneg _).trans h3)

theorem continuous_rankOneOperator : Continuous fun p : Wp × Wq => rk1 p.1 p.2 := by
  have : (fun p : Wp × Wq => rk1 p.1 p.2) =
      fun p => ContinuousLinearMap.smulRightL ℂ Wq Wp (innerSL ℂ p.2) p.1 := by
    funext p; ext η; simp [rk1]
  rw [this]
  fun_prop

theorem entry_eq [CompleteSpace Wp] {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {u : α → H} {a : α → Wp} {v : β → H} {b : β → Wq} {C D C' D' : ℝ}
    (hu : AEStronglyMeasurable u μ) (ha : AEStronglyMeasurable a μ)
    (huC : ∀ᵐ s ∂μ, ‖u s‖ ≤ C) (haD : ∀ᵐ s ∂μ, ‖a s‖ ≤ D)
    (hv : AEStronglyMeasurable v ν) (hb : AEStronglyMeasurable b ν)
    (hvC : ∀ᵐ s ∂ν, ‖v s‖ ≤ C') (hbD : ∀ᵐ s ∂ν, ‖b s‖ ≤ D') (T : H →L[ℂ] H) (η : Wp) (η' : Wq) :
    ⟪η, (∫ p, ⟪u p.1, T (v p.2)⟫_ℂ • rk1 (a p.1) (b p.2) ∂(μ.prod ν)) η'⟫_ℂ =
      ⟪∫ s, ⟪a s, η⟫_ℂ • u s ∂μ, T (∫ t, ⟪b t, η'⟫_ℂ • v t ∂ν)⟫_ℂ := by
  have hF := integrable_coord_smul hu ha huC haD η
  have hG := integrable_coord_smul hv hb hvC hbD η'
  have hI : Integrable (fun p : α × β => ⟪u p.1, T (v p.2)⟫_ℂ • rk1 (a p.1) (b p.2)) (μ.prod ν) := by
    refine Integrable.of_bound ?_ (C * (‖T‖ * C') * (D * D')) ?_
    · refine (hu.comp_fst.inner (𝕜 := ℂ) (T.continuous.comp_aestronglyMeasurable hv.comp_snd)).smul ?_
      exact continuous_rankOneOperator.comp_aestronglyMeasurable (ha.comp_fst.prodMk hb.comp_snd)
    · filter_upwards [Measure.quasiMeasurePreserving_fst.ae huC, Measure.quasiMeasurePreserving_fst.ae haD,
        Measure.quasiMeasurePreserving_snd.ae hvC, Measure.quasiMeasurePreserving_snd.ae hbD]
        with p h1 h2 h3 h4
      rw [norm_smul, norm_rankOneInnerOperator]
      have hC : 0 ≤ C := (norm_nonneg _).trans h1
      have hD : 0 ≤ D := (norm_nonneg _).trans h2
      have hC' : 0 ≤ C' := (norm_nonneg _).trans h3
      have h5 : ‖⟪u p.1, T (v p.2)⟫_ℂ‖ ≤ C * (‖T‖ * C') := by
        refine (norm_inner_le_norm _ _).trans ?_
        have := T.le_opNorm_of_le h3
        gcongr
      gcongr
  rw [← T.integral_comp_comm hG, inner_integral_integral hF (T.integrable_comp hG),
    ContinuousLinearMap.integral_apply hI, ← integral_inner (hI.apply_continuousLinearMap η')]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [ContinuousLinearMap.smul_apply, rankOneInnerOperator_apply, map_smul, inner_smul_left, inner_smul_right,
    inner_conj_symm]
  ring

theorem sum_inner_self {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ Wp)
    {μ : Measure α} [IsFiniteMeasure μ] {u : α → H} {a : α → Wp} {C D : ℝ}
    (hu : AEStronglyMeasurable u μ) (ha : AEStronglyMeasurable a μ)
    (huC : ∀ᵐ s ∂μ, ‖u s‖ ≤ C) (haD : ∀ᵐ s ∂μ, ‖a s‖ ≤ D) :
    ∑ i, ⟪∫ s, ⟪a s, e i⟫_ℂ • u s ∂μ, ∫ s, ⟪a s, e i⟫_ℂ • u s ∂μ⟫_ℂ =
      ∫ p, ⟪u p.1, u p.2⟫_ℂ * ⟪a p.2, a p.1⟫_ℂ ∂(μ.prod μ) := by
  have hF := fun i => integrable_coord_smul hu ha huC haD (e i)
  simp_rw [fun i => inner_integral_integral (hF i) (hF i)]
  rw [← integral_finset_sum _ fun i _ => integrable_inner_prod (hF i) (hF i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [inner_smul_left, inner_smul_right, inner_conj_symm]
  rw [← e.sum_inner_mul_inner (a p.2) (a p.1), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem eq_sum_entries {ι κ : Type*} [Fintype ι] [Fintype κ] (e : OrthonormalBasis ι ℂ Wp)
    (f : OrthonormalBasis κ ℂ Wq) (A : Wq →L[ℂ] Wp) :
    A = ∑ j, ∑ i, ⟪e i, A (f j)⟫_ℂ • rk1 (e i) (f j) := by
  ext η
  conv_lhs => rw [← f.sum_repr' η, map_sum]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, rankOneInnerOperator_apply, map_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [← e.sum_repr' (A (f j)), Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem hsNormSq_eq [FiniteDimensional ℂ Wq] {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ Wp)
    (A : Wq →L[ℂ] Wp) :
    ((hsNormSq A : ℝ) : ℂ) = ∑ j, ∑ i, ⟪e i, A (stdOrthonormalBasis ℂ Wq j)⟫_ℂ *
      star ⟪e i, A (stdOrthonormalBasis ℂ Wq j)⟫_ℂ := by
  have h : hsInner A A = ((hsInner A A).re : ℂ) := by
    unfold hsInner
    rw [Complex.re_sum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => (inner_self_ofReal_re (𝕜 := ℂ) _).symm
  unfold hsNormSq
  rw [← h]
  unfold hsInner
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← e.sum_inner_mul_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, RCLike.star_def, inner_conj_symm]

end Abstract

section Group

variable {k r : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem isUnit_det_of_mem {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((uHGroup _ (Hpk k r) (Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1)).2.2 g hg).1

theorem ae_mem {S : Set (Mat k r)} {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ) :
    ∀ᵐ s ∂μ, (Matrix.of s : Mat k r) ∈ S := hμ.2.2.1

theorem integral_sub_var {S : Set (Mat k r)} (hS : IsClosedSub k r S) {μ : Measure (Mt k r)}
    (hμ : IsHaarOn S μ) (hU : IsUnimod S μ) {Om : Set (Mt k r)} (hO : MeasurableSet Om) (hfin : μ Om < ⊤)
    {f : Mt k r → ℂ} (hf : Integrable f μ) :
    ∫ t in Om, ∫ s in Om, f (rmulM (Matrix.of t : Mat k r)⁻¹ s) ∂μ ∂μ =
      ∫ p, ((μ {s | s ∈ Om ∧ lmulM (Matrix.of p) s ∈ Om}).toReal : ℂ) * f p ∂μ := by
  haveI := hμ.1
  haveI : IsFiniteMeasure (μ.restrict Om) := isFiniteMeasure_restrict.2 hfin.ne
  have hc : Continuous fun q : Mt k r × Mt k r => lmulM (Matrix.of q.1) q.2 :=
    Continuous.matrix_mul (X := Mt k r × Mt k r) continuous_fst continuous_snd
  have hE : MeasurableSet {q : Mt k r × Mt k r | lmulM (Matrix.of q.1) q.2 ∈ Om} := hc.measurable hO
  have hK : Integrable (fun q : Mt k r × Mt k r =>
      {q : Mt k r × Mt k r | lmulM (Matrix.of q.1) q.2 ∈ Om}.indicator (fun q => f q.1) q)
      (μ.prod (μ.restrict Om)) := (hf.comp_fst _).indicator hE
  have h1 : ∀ᵐ t ∂(μ.restrict Om), ∫ s in Om, f (rmulM (Matrix.of t : Mat k r)⁻¹ s) ∂μ =
      ∫ p, {q : Mt k r × Mt k r | lmulM (Matrix.of q.1) q.2 ∈ Om}.indicator (fun q => f q.1) (p, t) ∂μ := by
    filter_upwards [ae_restrict_of_ae (ae_mem hμ)] with t ht
    have hm : ∀ a ∈ S, MeasurePreserving (rmulM a) μ μ :=
      fun a ha => ⟨(continuous_rmulM a).measurable, hU.1 a ha⟩
    have hg : Integrable (Om.indicator fun s => f (rmulM (Matrix.of t : Mat k r)⁻¹ s)) μ :=
      ((hm _ (hS.2.2.2.2 _ ht)).integrable_comp_of_integrable hf).indicator hO
    rw [← integral_indicator hO]
    conv_lhs => rw [← hU.1 _ ht]
    rw [integral_map (hm _ ht).aemeasurable (by rw [hU.1 _ ht]; exact hg.1)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    have h2 : rmulM (Matrix.of t : Mat k r)⁻¹ (rmulM (Matrix.of t : Mat k r) p) = p :=
      Matrix.mul_nonsing_inv_cancel_right (Matrix.of t : Mat k r) (Matrix.of p : Mat k r)
        (isUnit_det_of_mem (hS.1 ht))
    have h3 : rmulM (Matrix.of t : Mat k r) p = lmulM (Matrix.of p) t := rfl
    simp only [Set.indicator, h2]
    rw [h3]
    rfl
  rw [integral_congr_ae h1, ← integral_integral_swap hK]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have hE' : MeasurableSet {t : Mt k r | lmulM (Matrix.of p) t ∈ Om} := measurable_prodMk_left hE
  have h4 : (fun t => {q : Mt k r × Mt k r | lmulM (Matrix.of q.1) q.2 ∈ Om}.indicator
      (fun q => f q.1) (p, t)) = {t : Mt k r | lmulM (Matrix.of p) t ∈ Om}.indicator fun _ => f p := by
    funext t; rfl
  simp only
  rw [h4, integral_indicator_const _ hE', Measure.real, Measure.restrict_apply hE', Complex.real_smul,
    Set.inter_comm]
  rfl

theorem inner_inv_left {S : Set (Mat k r)} (hS : IsClosedSub k r S) {σ : Mat k r → (H →L[ℂ] H)}
    (hσ : IsURepOn S σ) {s : Mat k r} (hs : s ∈ S) (u v : H) :
    ⟪σ s⁻¹ u, v⟫_ℂ = ⟪u, σ s v⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(σ s : H →ₗ[ℂ] H), hσ.2.1 s hs⟩
  have h1 : σ s (σ s⁻¹ u) = u := by
    have := hσ.1.2 s hs _ (hS.2.2.2.2 s hs)
    rw [Matrix.mul_nonsing_inv _ (isUnit_det_of_mem (hS.1 hs)), hσ.1.1] at this
    exact (congrArg (fun T : H →L[ℂ] H => T u) this).symm
  have h2 := L.inner_map_map (σ s⁻¹ u) v
  change ⟪σ s (σ s⁻¹ u), σ s v⟫_ℂ = _ at h2
  rw [← h2, h1]

theorem rep_mul_apply {S : Set (Mat k r)} {σ : Mat k r → (H →L[ℂ] H)}
    (hσ : IsURepOn S σ) {s t : Mat k r} (hs : s ∈ S) (ht : t ∈ S) (u : H) :
    σ (s * t) u = σ s (σ t u) := by rw [hσ.1.2 s hs t ht]; rfl

theorem IsURepOn_mono {S G : Set (Mat k r)} (h : S ⊆ G) {σ : Mat k r → (H →L[ℂ] H)}
    (hσ : IsURepOn G σ) : IsURepOn S σ :=
  ⟨⟨hσ.1.1, fun a ha b hb => hσ.1.2 a (h ha) b (h hb)⟩, fun g hg => hσ.2.1 g (h hg),
    fun v => (hσ.2.2 v).mono h⟩

theorem aesm_of_continuousOn {X : Type*} [NormedAddCommGroup X] {S : Set (Mat k r)}
    (hS : IsClosedSub k r S) {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ) {F : Mat k r → X}
    (hF : ContinuousOn F S) : AEStronglyMeasurable (fun s : Mt k r => F (Matrix.of s)) μ := by
  have hcl : IsClosed (X := Mt k r) S := hS.2.1
  have hF' : ContinuousOn (X := Mt k r) (fun s : Mt k r => F (Matrix.of s)) S := hF
  have := hF'.aestronglyMeasurable (μ := μ) hcl.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_mem hμ)] at this

theorem continuousOn_rep_inv {S : Set (Mat k r)} (hS : IsClosedSub k r S) {σ : Mat k r → (H →L[ℂ] H)}
    (hσ : IsURepOn S σ) (u : H) : ContinuousOn (fun s : Mat k r => σ s⁻¹ u) S := by
  refine (hσ.2.2 u).comp (f := fun s : Mat k r => s⁻¹) (fun s hs => ?_) hS.2.2.2.2
  obtain ⟨d, hd⟩ := isUnit_det_of_mem (hS.1 hs)
  exact (continuousAt_matrix_inv s (hd ▸ NormedRing.inverse_continuousAt d)).continuousWithinAt

theorem aesm_rep_inv {S : Set (Mat k r)} (hS : IsClosedSub k r S) {μ : Measure (Mt k r)}
    (hμ : IsHaarOn S μ) {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn S σ) (u : H) (Om : Set (Mt k r)) :
    AEStronglyMeasurable (fun s : Mt k r => σ (Matrix.of s)⁻¹ u) (μ.restrict Om) :=
  (aesm_of_continuousOn hS hμ (continuousOn_rep_inv hS hσ u)).restrict

theorem ae_norm_rep_inv {S : Set (Mat k r)} (hS : IsClosedSub k r S) {μ : Measure (Mt k r)}
    (hμ : IsHaarOn S μ) {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn S σ) (u : H) (Om : Set (Mt k r)) :
    ∀ᵐ s ∂(μ.restrict Om), ‖σ (Matrix.of s)⁻¹ u‖ ≤ ‖u‖ := by
  filter_upwards [ae_restrict_of_ae (ae_mem hμ)] with s hs
  exact (hσ.2.1 _ (hS.2.2.2.2 _ hs) u).le

variable {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem sum_norm_side [CompleteSpace H] {S : Set (Mat k r)} (hS : IsClosedSub k r S) {μ : Measure (Mt k r)}
    (hμ : IsHaarOn S μ) (hU : IsUnimod S μ) {Om : Set (Mt k r)} (hO : MeasurableSet Om) (hfin : μ Om < ⊤)
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn S σ) {P : Mat k r → (Wp →L[ℂ] Wp)} (hP : IsURepOn S P)
    (y : H) (ξ : Wp) (hy : Integrable (fun p : Mt k r => coef σ y y (Matrix.of p)) μ)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ Wp) :
    ∑ i, ⟪∫ s in Om, ⟪P (Matrix.of s)⁻¹ ξ, e i⟫_ℂ • σ (Matrix.of s)⁻¹ y ∂μ,
        ∫ s in Om, ⟪P (Matrix.of s)⁻¹ ξ, e i⟫_ℂ • σ (Matrix.of s)⁻¹ y ∂μ⟫_ℂ =
      ∫ p, ((μ {s | s ∈ Om ∧ lmulM (Matrix.of p) s ∈ Om}).toReal : ℂ) *
        (coef σ y y (Matrix.of p) * ⟪ξ, P (Matrix.of p)⁻¹ ξ⟫_ℂ) ∂μ := by
  haveI := hμ.1
  haveI : IsFiniteMeasure (μ.restrict Om) := isFiniteMeasure_restrict.2 hfin.ne
  have hu := aesm_rep_inv hS hμ hσ y Om
  have ha := aesm_rep_inv hS hμ hP ξ Om
  have huC := ae_norm_rep_inv hS hμ hσ y Om
  have haD := ae_norm_rep_inv hS hμ hP ξ Om
  have hf : Integrable (fun p : Mt k r => coef σ y y (Matrix.of p) * ⟪ξ, P (Matrix.of p)⁻¹ ξ⟫_ℂ) μ := by
    refine hy.mul_bdd (c := ‖ξ‖ * ‖ξ‖) (aestronglyMeasurable_const.inner
      (aesm_of_continuousOn hS hμ (continuousOn_rep_inv hS hP ξ))) ?_
    filter_upwards [ae_mem hμ] with s hs
    refine (norm_inner_le_norm _ _).trans ?_
    rw [hP.2.1 _ (hS.2.2.2.2 _ hs)]
  rw [sum_inner_self e hu ha huC haD, ← integral_sub_var hS hμ hU hO hfin hf, integral_prod_symm]
  · refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (ae_mem hμ)] with t ht
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (ae_mem hμ)] with s hs
    have hti := hS.2.2.2.2 _ ht
    have hsi := hS.2.2.2.2 _ hs
    rw [of_rmulM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem (hS.1 ht)),
      coef, rep_mul_apply hσ hs hti, rep_mul_apply hP ht hsi, inner_inv_left hS hσ hs,
      inner_inv_left hS hP ht]
  · refine Integrable.of_bound ((hu.comp_fst.inner (𝕜 := ℂ) hu.comp_snd).mul
      (ha.comp_snd.inner (𝕜 := ℂ) ha.comp_fst)) (‖y‖ * ‖y‖ * (‖ξ‖ * ‖ξ‖)) ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae huC, Measure.quasiMeasurePreserving_fst.ae haD,
        Measure.quasiMeasurePreserving_snd.ae huC, Measure.quasiMeasurePreserving_snd.ae haD]
        with p h1 h2 h3 h4
    rw [norm_mul]
    gcongr
    · exact (norm_inner_le_norm _ _).trans (by gcongr)
    · exact (norm_inner_le_norm _ _).trans (by gcongr)

end Group

theorem truncated_norm_sq : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ (x y : H) (ξ : Wp) (ξ' : Wq) (Om Om' : Set (Mt k r)), MeasurableSet Om → MeasurableSet Om' → μS Om < ⊤ → μS' Om' < ⊤ → Integrable (fun p : Mt k r => coef σ y y (Matrix.of p)) μS → Integrable (fun p : Mt k r => coef σ x x (Matrix.of p)) μS' → ContinuousOn (Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict Om) (μS'.restrict Om') σ x y ξ ξ') (GG k r) ∧ Integrable (fun g : Mt k r => hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict Om) (μS'.restrict Om') σ x y ξ ξ' (Matrix.of g))) μG ∧ ((∫ g, hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict Om) (μS'.restrict Om') σ x y ξ ξ' (Matrix.of g)) ∂μG : ℝ) : ℂ) = (d : ℂ)⁻¹ * (∫ p, ((μS {s | s ∈ Om ∧ lmulM (Matrix.of p) s ∈ Om}).toReal : ℂ) * (coef σ y y (Matrix.of p) * ⟪ξ, PiS (psiGen k r z c) π (Matrix.of p)⁻¹ ξ⟫_ℂ) ∂μS) * (∫ p, ((μS' {s | s ∈ Om' ∧ lmulM (Matrix.of p) s ∈ Om'}).toReal : ℂ) * (coef σ x x (Matrix.of p) * ⟪ξ', PiS (psiGen k r z' c') π' (Matrix.of p)⁻¹ ξ'⟫_ℂ) ∂μS') := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hstd hs hs' x y ξ ξ' Om Om'
    hO hO' hfin hfin' hy hx
  obtain ⟨-, hσ, -, -, hμG, ⟨-, hSch⟩, -⟩ := hstd
  obtain ⟨hz, hT, hπ, hμ, -⟩ := hs
  obtain ⟨hz', hT', hπ', hμ', -⟩ := hs'
  have hS := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT).2.2.2.1
  have hS' := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z' hz' hT').2.2.2.1
  have hG := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT).1
  have hP := (GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ).2.1
  have hP' := (GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z' c' π' hz' hT' hπ').2.1
  have hU := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hμ
  have hU' := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z' hz' hT' μS').1 hμ'
  have hσS := IsURepOn_mono hS.1 hσ
  have hσS' := IsURepOn_mono hS'.1 hσ
  haveI : IsFiniteMeasure (μS.restrict Om) := isFiniteMeasure_restrict.2 hfin.ne
  haveI : IsFiniteMeasure (μS'.restrict Om') := isFiniteMeasure_restrict.2 hfin'.ne
  set I := Iint (psiGen k r z c) (psiGen k r z' c') π π' (μS.restrict Om) (μS'.restrict Om') σ x y ξ ξ'
    with hI
  set e := stdOrthonormalBasis ℂ Wp
  set f := stdOrthonormalBasis ℂ Wq
  have hY := sum_norm_side hS hμ hU hO hfin hσS hP y ξ hy e
  have hX := sum_norm_side hS' hμ' hU' hO' hfin' hσS' hP' x ξ' hx f
  set Y := fun i => ∫ s in Om, ⟪PiS (psiGen k r z c) π (Matrix.of s)⁻¹ ξ, e i⟫_ℂ • σ (Matrix.of s)⁻¹ y ∂μS
    with hYdef
  set X := fun j => ∫ s in Om', ⟪PiS (psiGen k r z' c') π' (Matrix.of s)⁻¹ ξ', f j⟫_ℂ •
    σ (Matrix.of s)⁻¹ x ∂μS' with hXdef
  have hent : ∀ g ∈ GG k r, ∀ i j, ⟪e i, I g (f j)⟫_ℂ = coef σ (X j) (Y i) g := by
    intro g hg i j
    rw [coef, hXdef, hYdef]
    simp only
    rw [← entry_eq (aesm_rep_inv hS hμ hσS y Om) (aesm_rep_inv hS hμ hP ξ Om)
      (ae_norm_rep_inv hS hμ hσS y Om) (ae_norm_rep_inv hS hμ hP ξ Om)
      (aesm_rep_inv hS' hμ' hσS' x Om') (aesm_rep_inv hS' hμ' hP' ξ' Om')
      (ae_norm_rep_inv hS' hμ' hσS' x Om') (ae_norm_rep_inv hS' hμ' hP' ξ' Om') (σ g) (e i) (f j), hI, Iint]
    congr 2
    refine integral_congr_ae ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_of_ae (s := Om) (ae_mem hμ)),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_of_ae (s := Om') (ae_mem hμ'))] with p h1 h2
    have h3 := hS'.1 (hS'.2.2.2.2 _ h2)
    rw [matrix_of_besselTwoSidedAction, of_invM, coef, rep_mul_apply hσ (hG.2.2.2.1 _ (hS.1 h1) _ hg) h3,
      rep_mul_apply hσ (hS.1 h1) hg, inner_inv_left hS hσS h1]
  have hhs : ∀ᵐ g ∂μG, ((hsNormSq (I (Matrix.of g)) : ℝ) : ℂ) =
      ∑ j, ∑ i, coef σ (X j) (Y i) (Matrix.of g) * star (coef σ (X j) (Y i) (Matrix.of g)) := by
    filter_upwards [ae_mem hμG] with g hg
    rw [hsNormSq_eq e]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [hent _ hg i j]
  have hint : ∀ j, Integrable (fun g : Mt k r =>
      ∑ i, coef σ (X j) (Y i) (Matrix.of g) * star (coef σ (X j) (Y i) (Matrix.of g))) μG :=
    fun j => integrable_finset_sum _ fun i _ => (hSch _ _ _ _).1
  refine ⟨?_, ?_, ?_⟩
  · have hc : ContinuousOn (fun g => ∑ j, ∑ i, coef σ (X j) (Y i) g • rk1 (e i) (f j)) (GG k r) :=
      continuousOn_finset_sum _ fun j _ => continuousOn_finset_sum _ fun i _ =>
        (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (hσ.2.2 (X j))).smul continuousOn_const
    refine hc.congr fun g hg => ?_
    rw [eq_sum_entries e f (I g)]
    simp only [hent g hg]
  · have h1 : Integrable (fun g : Mt k r => ((hsNormSq (I (Matrix.of g)) : ℝ) : ℂ)) μG :=
      (integrable_finset_sum _ fun j _ => hint j).congr (Filter.EventuallyEq.symm hhs)
    exact h1.re
  · rw [← integral_complex_ofReal, integral_congr_ae hhs, integral_finset_sum _ fun j _ => hint j, ← hX, ← hY,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finset_sum _ fun i _ => (hSch _ _ _ _).1, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hSch _ _ _ _).2]
    ring

end GlobalTheory.SgInf.TruncNorm
