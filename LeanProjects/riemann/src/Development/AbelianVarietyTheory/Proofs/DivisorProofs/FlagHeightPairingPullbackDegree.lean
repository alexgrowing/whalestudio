import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartPreimageOfFiniteLiftedChartCovering
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleChartCoveringComplexPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottChernMatrixIsFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixIsFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetPartitionNullStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixDensPull

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem chernMat_pull (π : Y ⟶ X) (hπ : π ≫ p = q) {B : LB X} {φ : Weight p σ B} (hφ : φ.IsCInf)
    (c : AlgChart p σ D) (c' : AlgChart q σ D)
    (H : ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧
      c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) {z : CxPts q σ} (hz : z ∈ c'.e.source) :
    chernMat (φ.pull π hπ) c' z = chernMat φ c (PtsOver.map π hπ (spMap σ) z) := by
  have hz' := (H z hz).1
  have hj := mem_of_mem_linComb (m := fun _ => PtsOver.map π hπ _ z) (fun _ => rfl)
    (mem_pick (φ.pull π hπ).isLB z) PUnit.unit
  rw [chernMat, chernMat, c.hess_eq hφ hz' hj (mem_pick _ _), AlgChart.hess,
    AlgChart.hess, ← (H z hz).2, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr]
  filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hz)] with v hv
  have hw := c'.e.map_target hv
  obtain ⟨h₁, h₂⟩ := H _ hw
  rw [c'.e.right_inv hv] at h₂
  have e₁ : c.e.symm v = PtsOver.map π hπ (spMap σ) (c'.e.symm v) := by
    exact (congrArg c.e.symm h₂).trans (c.e.left_inv h₁)
  rw [e₁]
  exact congrArg _ (φ.pull_φ π hπ _ _)

theorem bcMat_eq_of_gram {S : ShortComplex X.Modules} {S' : ShortComplex Y.Modules}
    {r s : ℕ} {h : Met p σ S.X₂ (r + s)} {h' : Met q σ S'.X₂ (r + s)} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r)
    (h₃' : IsVB S'.X₃ s) (H : h.IsCInf) (H' : h'.IsCInf) (a : VBExt.AdaptedChart S r s)
    (a' : VBExt.AdaptedChart S' r s) (c : AlgChart p σ D) (c' : AlgChart q σ D) {y : CxPts p σ}
    {z : CxPts q σ} (hy : y ∈ c.e.source) (hz : z ∈ c'.e.source) (ha : y ∈ ptsIn p σ a.U)
    (ha' : z ∈ ptsIn q σ a'.U) (he : c'.e z = c.e y)
    (hg : ∀ᶠ v in 𝓝 (c'.e z), h'.gram a'.frame (c'.e.symm v) = h.gram a.frame (c.e.symm v)) :
    bcMat h' hS' h₁' h₃' c' z = bcMat h hS h₁ h₃ c y := by
  rw [bcMat, bcMat,
    Met.bcForm_eq hS' a' _ c' H' hz ha' (Met.exists_adapted hS' h₁' h₃' z).choose_spec,
    Met.bcForm_eq hS a _ c H hy ha (Met.exists_adapted hS h₁ h₃ y).choose_spec]
  unfold Met.bcForm
  rw [extTrace_congr hg, he]

variable {E : X.Modules} {r : ℕ} {h : VMetric p E r}

theorem flagMat_pull (H : h.IsCInf) (fl : Vert.Flag E r) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (c : AlgChart p σ D) (c' : AlgChart q σ D)
    (he : ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧
      c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) {z : CxPts q σ} (hz : z ∈ c'.e.source) :
    flagMat (h.pull π hπ) (fl.pull π) σ c' z = flagMat h fl σ c (PtsOver.map π hπ (spMap σ) z) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨a, ha⟩ := Met.exists_adapted (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc)
    (fl.isVB_gr i) (PtsOver.map π hπ (spMap σ) z)
  have ha' : z ∈ ptsIn q σ (π ⁻¹ᵁ a.U) := ha
  have H₁ : (h.stepMet fl i).IsCInf := H.restrict _ _
  have H₂ : ((h.pull π hπ).stepMet (fl.pull π) i).IsCInf := (H.pull π hπ).restrict _ _
  have hS : IsOpen (c'.e.source ∩ ptsIn q σ (π ⁻¹ᵁ a.U)) := c'.e.open_source.inter (isOpen_ptsIn _)
  have hn := (ChartGlue.isOpen_over c'.e hS).mem_nhds (ChartGlue.mem_over c'.e hz (S := _) ⟨hz, ha'⟩)
  refine bcMat_eq_of_gram _ _ _ _ _ _ (H₁ σ) (H₂ σ) a (VMetric.pullStep fl π i a) c c' (he z hz).1 hz ha ha'
    (he z hz).2 ?_
  filter_upwards [hn] with v hv
  obtain ⟨h₁, h₃⟩ := hv.2
  have e₁ : c.e.symm v = PtsOver.map π hπ _ (c'.e.symm v) := by
    obtain ⟨h₂, this⟩ := he _ h₁
    rw [c'.e.right_inv hv.1] at this
    exact (congrArg c.e.symm this).trans (c.e.left_inv h₂)
  rw [e₁]
  exact VMetric.gram_pullStep h hπ a h₃

theorem isDens_flagDens (H : h.IsCInf) (fl : Vert.Flag E r) (N : HermLB p) (d : ℕ) (σ : k →+* ℂ) :
    IsDens (flagDens h fl N d σ) :=
  IsForm.isDens_mix (GlobalTheory.T.chern_matrix_is_form k X p σ (d + 1) _ _ (N.cInf σ))
    (IsForm.sum Finset.univ fun i => GlobalTheory.T.bott_chern_matrix_is_form k X p σ (d + 1) _ _ _ _
      (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i)
      ((show (h.stepMet fl i).IsCInf from H.restrict _ _) σ))

theorem isDens_neg {τ : AlgChart p σ D → CxPts p σ → ℝ} (hτ : IsDens τ) : IsDens fun c y => -τ c y :=
  ⟨fun c c' y hy hy' => by beta_reduce; rw [hτ.1 c c' y hy hy', mul_neg], fun c => (hτ.2 c).neg⟩

theorem part_univ [IsIntegral X] [IsIntegral Y] (hX : IsArithVar p D) (hY : IsArithVar q D)
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hη : π (genericPoint Y) = genericPoint X)
    (hδ : π.residueDegree (genericPoint Y) ≠ 0) {τ : AlgChart p σ D → CxPts p σ → ℝ}
    {τ' : AlgChart q σ D → CxPts q σ → ℝ} (hτ : IsDens τ) (hτ' : IsDens τ')
    (he : ∀ (c : AlgChart p σ D) (c' : AlgChart q σ D),
      (∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧
        c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) →
      ∀ w ∈ c'.e.source, τ' c' w = τ c (PtsOver.map π hπ (spMap σ) w)) :
    part τ' Set.univ = (π.residueDegree (genericPoint Y) : ℝ≥0∞) * part τ Set.univ := by
  obtain ⟨U, hUη, hU⟩ := GlobalTheory.T.exists_open_etaleChart_covering_complexPoints hX hY π hπ hη hδ
  obtain ⟨hcard, hchart, hlift⟩ := hU σ
  have := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hX.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (σ := σ) hY.isProjOver
  have hpre : PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ U = ptsIn q σ (π ⁻¹ᵁ U) := by
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have hcY : (ptsIn q σ (π ⁻¹ᵁ U))ᶜ =
      {z : CxPts q σ | z.1 (IsLocalRing.closedPoint ℂ) ∈ ((π ⁻¹ᵁ U : Y.Opens) : Set Y)ᶜ} := by
    ext z
    simp [mem_ptsIn]
  have hcX : (ptsIn p σ U)ᶜ =
      {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((U : X.Opens) : Set X)ᶜ} := by
    ext y
    simp [mem_ptsIn]
  have h0Y := GlobalTheory.T.closed_subset_partition_null k Y q D hY ((π ⁻¹ᵁ U : Y.Opens) : Set Y)ᶜ (π ⁻¹ᵁ U).isOpen.isClosed_compl
    (by simp [hη, hUη]) σ τ'
  have h0X := GlobalTheory.T.closed_subset_partition_null k X p D hX ((U : X.Opens) : Set X)ᶜ U.isOpen.isClosed_compl (by simp [hUη]) σ τ
  rw [← hcY] at h0Y
  rw [← hcX] at h0X
  have h3 : part τ' (PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ U) =
      (π.residueDegree (genericPoint Y) : ℝ≥0∞) * part τ (ptsIn p σ U) := by
    unfold part
    refine CoverChern.glueMeas_preimage_of_cover_on (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
      (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ?_)
      (PtsOver.continuous_map π hπ _) (isOpen_ptsIn U) hcard (fun z hz => ?_)
      (isOpen_ptsIn U).measurableSet subset_rfl
    · rw [hτ.1 c c' y hy hy', ENNReal.ofReal_mul (sq_nonneg _)]
    · rw [hτ'.1 c c' y hy hy', ENNReal.ofReal_mul (sq_nonneg _)]
    · obtain ⟨c, hc⟩ := hchart _ hz
      obtain ⟨c', hz', hc'⟩ := hlift z hz c hc
      exact ⟨c, c', hz', hc, fun w hw _ => ⟨(hc' w hw).2, by rw [he c c' hc' w hw]⟩⟩
  rw [hpre] at h3
  rw [← measure_add_measure_compl (isOpen_ptsIn (π ⁻¹ᵁ U)).measurableSet, h0Y, add_zero, h3,
    ← measure_add_measure_compl (isOpen_ptsIn (p := p) (σ := σ) U).measurableSet, h0X, add_zero]

theorem bcPair_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (d : ℕ) (ρ : Y ⟶ X), IsArithVar p (d + 1) → FlagChain.IsCov p (d + 1) ρ → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r), h.IsCInf → ∀ (fl : Vert.Flag E r) (N : HermLB p), bcPair (h.pull ρ rfl) (fl.pull ρ) (N.pull ρ rfl) d = (ρ.residueDegree (genericPoint Y) : ℝ) * bcPair h fl N d := by
  intro k _ X Y _ _ p d ρ hX hρ E r h H fl N
  obtain ⟨hY, hη, hδ⟩ := hρ
  have key : ∀ σ, total (flagDens (h.pull ρ rfl) (fl.pull ρ) (N.pull ρ rfl) d σ) =
      (ρ.residueDegree (genericPoint Y) : ℝ) * total (flagDens h fl N d σ) := by
    intro σ
    have hτ := isDens_flagDens H fl N d σ
    have hτ' := isDens_flagDens (H.pull ρ rfl) (fl.pull ρ) (N.pull ρ rfl) d σ
    have he : ∀ (c : AlgChart p σ (d + 1)) (c' : AlgChart (ρ ≫ p) σ (d + 1)),
        (∀ w ∈ c'.e.source, PtsOver.map ρ rfl (spMap σ) w ∈ c.e.source ∧
          c'.e w = c.e (PtsOver.map ρ rfl (spMap σ) w)) →
        ∀ w ∈ c'.e.source, flagDens (h.pull ρ rfl) (fl.pull ρ) (N.pull ρ rfl) d σ c' w =
          flagDens h fl N d σ c (PtsOver.map ρ rfl (spMap σ) w) := fun c c' hc w hw => by
      rw [flagDens, flagDens, flagMat_pull H fl ρ rfl c c' hc hw, ← chernMat_pull ρ rfl (N.cInf σ) c c' hc hw]
      rfl
    rw [total, total, part_univ hX hY ρ rfl hη hδ hτ hτ' he,
      part_univ hX hY ρ rfl hη hδ (isDens_neg hτ) (isDens_neg hτ') fun c c' hc w hw => by rw [he c c' hc w hw],
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_sub]
  have := hX.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  rw [bcPair, bcPair, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => key σ

end GlobalTheory.MixDensPull

end
