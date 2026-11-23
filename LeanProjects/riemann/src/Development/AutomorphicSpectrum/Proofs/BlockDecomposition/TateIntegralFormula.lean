import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global GroundTheory.Global.IdeleGroup PositivityTheory.Rg.Base1
open scoped ENNReal NNReal NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.TateRes

variable {F : Type} [Field F] [NumberField F]

theorem pr_eq_diagonal (t : Fˣ) : pr t = diagonal F t := rfl

theorem md_pos (a : IdeleGroup F) : 0 < md a := (ideleModule F a).2

theorem md_mul (a b : IdeleGroup F) : md (a * b) = md a * md b := by
  simp [md, map_mul]

theorem md_pr (t : Fˣ) : md (pr t) = 1 := by
  simp [md, pr_eq_diagonal, ideleModule_diagonal]

theorem continuous_md : Continuous (md : IdeleGroup F → ℝ) :=
  continuous_subtype_val.comp continuous_ideleModule

theorem th_pr_mul (f : IdeleGroup F → ℝ≥0∞) (ξ : Fˣ) (a : IdeleGroup F) :
    th f (pr ξ * a) = th f a := by
  unfold th
  rw [← (Equiv.mulRight ξ).tsum_eq (fun t => f (pr t * a))]
  refine tsum_congr fun t => ?_
  simp [pr, mul_assoc]

theorem measurable_th {f : IdeleGroup F → ℝ≥0∞} (hf : Measurable f) : Measurable (th f) := by
  unfold th
  exact Measurable.ennreal_tsum fun t => hf.comp (measurable_const_mul _)

theorem setLIntegral_mul_right (g : normOneSubgroup F → ℝ≥0∞)
    (hg : ∀ (ξ : Fˣ) u, g (diagonalToNormOne F ξ * u) = g u) (b : normOneSubgroup F) :
    ∫⁻ u in normOneFundamentalDomain F, g (u * b) ∂normOneMeasure F =
      ∫⁻ u in normOneFundamentalDomain F, g u ∂normOneMeasure F := by
  have hD := isFundamentalDomain_normOneFundamentalDomain F (normOneMeasure F)
  have hD' := hD.smul_of_comm b
  have hinv : ∀ (γ : (diagonalNormOne F).op) (x : normOneSubgroup F), g (γ • x) = g x := by
    rintro ⟨γ, hγ⟩ x
    obtain ⟨k, hk⟩ := Subgroup.mem_op.1 hγ
    have e : γ.unop = diagonalToNormOne F k := Subtype.ext hk.symm
    change g (x * γ.unop) = g x
    rw [e, mul_comm]
    exact hg k x
  rw [hD.setLIntegral_eq hD' g hinv]
  have := (measurePreserving_mul_left (normOneMeasure F) b).setLIntegral_comp_emb
    (MeasurableEquiv.mulLeft b).measurableEmbedding g (normOneFundamentalDomain F)
  simp_rw [mul_comm _ b]
  exact this

end GlobalTheory.CompanionTheory.TateRes

namespace GlobalTheory.CompanionTheory.TateRes
variable {F : Type} [Field F] [NumberField F]

theorem md_ray (hF : IsTotallyReal F) {θ : ℝ →+* HeckeCharacterZeroLocus.SiegelWeilU.Ainf F} (hθ : Continuous θ) {r : ℝ → IdeleGroup F}
    (hr : IsRay θ r) {δ : ℝ} (hδ : 0 < δ) : md (r δ) = δ ^ Module.finrank ℚ F := by
  have hn : ∀ w : InfinitePlace F, ‖θ δ w‖ = δ := by
    intro w
    have hw : w.IsReal := hF.isReal w
    let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    let ρ : ℝ →+* ℝ := (e : w.Completion →+* ℝ).comp ((Pi.evalRingHom _ w).comp θ)
    have hρ : ρ δ = δ := by
      have : ρ = RingHom.id ℝ := Subsingleton.elim _ _
      rw [this]; rfl
    have hnorm : ‖θ δ w‖ = ‖e (θ δ w)‖ := by
      rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
      exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
          (map_zero _) _).symm
    rw [hnorm]
    change ‖ρ δ‖ = δ
    rw [hρ, Real.norm_of_nonneg hδ.le]
  obtain ⟨h1, h2⟩ := hr δ hδ
  have : md (r δ) = (∏ w : InfinitePlace F, ‖(r δ : 𝔸[F]).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(r δ : 𝔸[F]).2 v‖ := ideleModule_eq _
  rw [this]
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(r δ : 𝔸[F]).2 v‖ = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rw [h2]
    exact norm_one
  rw [hfin, mul_one, h1]
  simp only [hn]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

theorem lintegral_exp_Iic (M : ℝ) :
    ∫⁻ z in Set.Iic M, ENNReal.ofReal (Real.exp z) = ENNReal.ofReal (Real.exp M) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_Iic M)
    (Eventually.of_forall fun z => (Real.exp_pos z).le), integral_exp_Iic]

theorem scale_lintegral {ε : ℝ} (hε : 0 < ε) (J : ℝ → ℝ≥0∞) (hJ : Measurable J) :
    ENNReal.ofReal ε * ∫⁻ y, ENNReal.ofReal (Real.exp (ε * y)) * J y =
      ∫⁻ z, ENNReal.ofReal (Real.exp z) * J (z / ε) := by
  have hK : Measurable fun z : ℝ => ENNReal.ofReal (Real.exp z) * J (z / ε) :=
    (ENNReal.measurable_ofReal.comp Real.measurable_exp).mul (hJ.comp (measurable_id.div_const ε))
  have h := lintegral_map (μ := volume) hK (measurable_const_mul ε)
  rw [Real.map_volume_mul_left hε.ne', lintegral_smul_measure] at h
  have e : ∀ y : ℝ, ε * y / ε = y := fun y => by field_simp
  simp only [e] at h
  rw [← h, abs_of_pos (inv_pos.2 hε), smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hε.le, mul_inv_cancel₀ hε.ne', ENNReal.ofReal_one, one_mul]

theorem abel {J : ℝ → ℝ≥0∞} (hJ : Measurable J) {B L : ℝ≥0∞} (hB : B ≠ ⊤) (hle : ∀ y, J y ≤ B) {y₀ : ℝ}
    (h0 : ∀ y, y₀ < y → J y = 0) (hL : Tendsto J atBot (𝓝 L)) :
    (∀ s : ℝ, 1 < s → ∫⁻ y, ENNReal.ofReal (Real.exp ((s - 1) * y)) * J y ≠ ⊤) ∧
    Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) * ∫⁻ y, ENNReal.ofReal (Real.exp ((s - 1) * y)) * J y)
      (𝓝[>] 1) (𝓝 L) := by
  have hbound : ∀ M : ℝ, ∫⁻ z, (Set.Iic M).indicator (fun z => ENNReal.ofReal (Real.exp z) * B) z ≠ ⊤ := by
    intro M
    rw [lintegral_indicator measurableSet_Iic, lintegral_mul_const' B (fun z => ENNReal.ofReal (Real.exp z)) hB,
      lintegral_exp_Iic]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB
  have hK : ∀ {ε : ℝ} {M : ℝ}, 0 < ε → ε * y₀ ≤ M → ∀ z : ℝ, ENNReal.ofReal (Real.exp z) * J (z / ε) ≤
      (Set.Iic M).indicator (fun z => ENNReal.ofReal (Real.exp z) * B) z := by
    intro ε M hε hM z
    by_cases hz : z ≤ M
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 hz)]
      gcongr
      exact hle _
    · have hz' : M < z := not_le.1 hz
      have : y₀ < z / ε := by
        rw [lt_div_iff₀' hε]
        exact lt_of_le_of_lt hM hz'
      rw [h0 _ this, mul_zero]
      exact zero_le
  have hKm : ∀ ε : ℝ, Measurable fun z : ℝ => ENNReal.ofReal (Real.exp z) * J (z / ε) := fun ε =>
    (ENNReal.measurable_ofReal.comp Real.measurable_exp).mul (hJ.comp (measurable_id.div_const ε))
  constructor
  · intro s hs htop
    have hε : 0 < s - 1 := sub_pos.2 hs
    have h1 := scale_lintegral hε J hJ
    rw [htop, ENNReal.mul_top (by simpa using hε)] at h1
    have h2 := lintegral_mono (μ := volume) (hK hε le_rfl)
    rw [← h1] at h2
    exact hbound _ (top_le_iff.1 h2)
  · have hcongr : ∀ᶠ s in 𝓝[>] (1 : ℝ), ∫⁻ z, ENNReal.ofReal (Real.exp z) * J (z / (s - 1)) =
        ENNReal.ofReal (s - 1) * ∫⁻ y, ENNReal.ofReal (Real.exp ((s - 1) * y)) * J y := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (scale_lintegral (sub_pos.2 hs) J hJ).symm
    refine Tendsto.congr' hcongr ?_
    have hval : ∫⁻ z, (Set.Iic (0 : ℝ)).indicator (fun z => ENNReal.ofReal (Real.exp z) * L) z = L := by
      have hLt : L ≠ ⊤ := ne_top_of_le_ne_top hB (le_of_tendsto' hL hle)
      rw [lintegral_indicator measurableSet_Iic, lintegral_mul_const' L (fun z => ENNReal.ofReal (Real.exp z)) hLt,
        lintegral_exp_Iic, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    have hsub : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub continuous_const).tendsto 1
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact Set.mem_Ioi.2 (sub_pos.2 (Set.mem_Ioi.1 hs))
    have hs : Tendsto (fun s : ℝ => (s - 1)⁻¹) (𝓝[>] 1) atTop := tendsto_inv_nhdsGT_zero.comp hsub
    have hne : ∀ᵐ z : ℝ, z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
    have key := tendsto_lintegral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (1 : ℝ))
      (F := fun s z => ENNReal.ofReal (Real.exp z) * J (z / (s - 1)))
      (f := (Set.Iic (0 : ℝ)).indicator (fun z => ENNReal.ofReal (Real.exp z) * L))
      ((Set.Iic (max y₀ 0)).indicator (fun z => ENNReal.ofReal (Real.exp z) * B))
      (Eventually.of_forall fun s => hKm _) ?_ (hbound _) ?_
    · rwa [hval] at key
    · filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with s hs'
      refine Eventually.of_forall fun z => hK (sub_pos.2 hs'.1) ?_ z
      rcases le_total 0 y₀ with h | h
      · rw [max_eq_left h]
        nlinarith [hs'.1, hs'.2]
      · rw [max_eq_right h]
        nlinarith [hs'.1, hs'.2]
    · filter_upwards [hne] with z hz
      rcases lt_or_gt_of_ne hz with hz | hz
      · rw [Set.indicator_of_mem (Set.mem_Iic.2 hz.le)]
        have h : Tendsto (fun s : ℝ => z / (s - 1)) (𝓝[>] 1) atBot := by
          simpa [div_eq_mul_inv] using hs.const_mul_atTop_of_neg hz
        exact ENNReal.Tendsto.const_mul (hL.comp h) (Or.inr ENNReal.ofReal_ne_top)
      · rw [Set.indicator_of_notMem (by simpa using hz)]
        have h : Tendsto (fun s : ℝ => z / (s - 1)) (𝓝[>] 1) atTop := by
          simpa [div_eq_mul_inv] using hs.const_mul_atTop hz
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [h.eventually (eventually_gt_atTop y₀)] with s hs'
        simp [h0 _ hs']

theorem measurable_fiber (w : InfinitePlace F) {f : IdeleGroup F → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun y : ℝ => ∫⁻ u in normOneFundamentalDomain F,
      th f ((u : IdeleGroup F) * moduleSection w (expPos y)) ∂normOneMeasure F := by
  refine Measurable.lintegral_prod_left (f := fun (u : normOneSubgroup F) (y : ℝ) =>
    th f ((u : IdeleGroup F) * moduleSection w (expPos y))) ?_
  refine (measurable_th hf).comp (Continuous.measurable ?_)
  exact (continuous_subtype_val.comp continuous_fst).mul
    (((continuous_moduleSection w).comp expPosHomeomorph.continuous).comp continuous_snd)

theorem lintegral_normOne_mul (a : IdeleGroup F) {f : IdeleGroup F → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ u, f ((u : IdeleGroup F) * a) ∂normOneMeasure F =
      ∫⁻ u in normOneFundamentalDomain F, th f ((u : IdeleGroup F) * a) ∂normOneMeasure F := by
  have hD := isFundamentalDomain_normOneFundamentalDomain F (normOneMeasure F)
  let e : Fˣ ≃ (diagonalNormOne F).op := (diagonalNormOneEquiv F).trans (diagonalNormOne F).equivOp
  set h : normOneSubgroup F → ℝ≥0∞ := fun u => f ((u : IdeleGroup F) * a) with hh
  have hm : Measurable h := hf.comp (continuous_subtype_val.measurable.mul_const a)
  calc ∫⁻ u, h u ∂normOneMeasure F
      = ∑' γ : (diagonalNormOne F).op, ∫⁻ u in normOneFundamentalDomain F, h (γ • u) ∂normOneMeasure F :=
        hD.lintegral_eq_tsum'' h
    _ = ∫⁻ u in normOneFundamentalDomain F, ∑' γ : (diagonalNormOne F).op, h (γ • u) ∂normOneMeasure F :=
        (lintegral_tsum fun γ => (hm.comp (measurable_const_smul γ)).aemeasurable).symm
    _ = ∫⁻ u in normOneFundamentalDomain F, ∑' ξ : Fˣ, h (e ξ • u) ∂normOneMeasure F := by
        refine lintegral_congr fun u => ?_
        exact (e.tsum_eq (fun γ => h (γ • u))).symm
    _ = _ := by
        refine lintegral_congr fun u => tsum_congr fun ξ => ?_
        change f (((u * diagonalToNormOne F ξ : normOneSubgroup F) : IdeleGroup F) * a) = f (pr ξ * ((u : IdeleGroup F) * a))
        congr 1
        rw [Subgroup.coe_mul, coe_diagonalToNormOne, pr_eq_diagonal, mul_comm (u : IdeleGroup F), mul_assoc]

theorem zi_eq (w : InfinitePlace F) {f : IdeleGroup F → ℝ≥0∞} (hf : Measurable f) (s : ℝ) :
    zi f s = ∫⁻ y, ENNReal.ofReal (Real.exp ((s - 1) * y)) * (ENNReal.ofReal (Real.exp y) *
      ∫⁻ u in normOneFundamentalDomain F,
        th f ((u : IdeleGroup F) * moduleSection w (expPos y)) ∂normOneMeasure F) := by
  have hmp := measurePreserving_normOneSplitting (K := F) w
  set g : normOneSubgroup F × {r : ℝ // 0 < r} → ℝ≥0∞ := fun p =>
    f ((p.1 : IdeleGroup F) * moduleSection w p.2) * ENNReal.ofReal ((p.2 : ℝ) ^ s) with hg
  have hgm : Measurable g := by
    refine (hf.comp (Continuous.measurable ?_)).mul (ENNReal.measurable_ofReal.comp ?_)
    · exact (continuous_subtype_val.comp continuous_fst).mul ((continuous_moduleSection w).comp continuous_snd)
    · exact (measurable_subtype_coe.comp measurable_snd).pow_const s
  have h1 : zi f s = ∫⁻ p, g p ∂(normOneMeasure F).prod posRealMeasure := by
    rw [← hmp.lintegral_comp hgm]
    refine lintegral_congr fun a => ?_
    have e := (normOneSplitting w).symm_apply_apply a
    rw [normOneSplitting_symm_apply] at e
    simp only [hg]
    rw [e, normOneSplitting_apply_snd]
    rfl
  rw [h1, lintegral_prod_symm _ hgm.aemeasurable, posRealMeasure_eq_map_expPos,
    lintegral_map (hgm.lintegral_prod_left') measurable_expPos]
  refine lintegral_congr fun y => ?_
  simp only [hg]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_normOne_mul _ hf, mul_comm, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, coe_expPos, ← Real.exp_mul]
  congr 3
  ring_nf

theorem vol_inter (H : Subgroup (IdeleGroup F)) (hHo : IsOpen (H : Set (IdeleGroup F))) (hHi : H.index ≠ 0)
    (hpr : ∀ t : Fˣ, pr t ∈ H) (hcov : ∀ a : IdeleGroup F, ∃ h ∈ H, a * h⁻¹ ∈ normOneSubgroup F) :
    normOneMeasure F (normOneFundamentalDomain F ∩ {u | (u : IdeleGroup F) ∈ H}) =
      normOneMeasure F (normOneFundamentalDomain F) / (H.index : ℝ≥0∞) := by
  classical
  haveI : H.FiniteIndex := ⟨hHi⟩
  haveI : Fintype (IdeleGroup F ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  set m := (normOneMeasure F).restrict (normOneFundamentalDomain F) with hm
  let A : IdeleGroup F ⧸ H → Set (normOneSubgroup F) :=
    fun q => {u | ((u : IdeleGroup F) : IdeleGroup F ⧸ H) = q}
  set A₀ : Set (normOneSubgroup F) := {u | (u : IdeleGroup F) ∈ H} with hA₀
  have hmemA : ∀ (b : normOneSubgroup F) (u : normOneSubgroup F),
      u ∈ A ((b : IdeleGroup F) : IdeleGroup F ⧸ H) ↔ u * b⁻¹ ∈ A₀ := by
    intro b u
    change ((u : IdeleGroup F) : IdeleGroup F ⧸ H) = ((b : IdeleGroup F) : IdeleGroup F ⧸ H) ↔
      ((u * b⁻¹ : normOneSubgroup F) : IdeleGroup F) ∈ H
    rw [QuotientGroup.eq, Subgroup.coe_mul, Subgroup.coe_inv, mul_comm]
    constructor
    · intro h
      have := H.inv_mem h
      simpa [mul_comm] using this
    · intro h
      have := H.inv_mem h
      simpa [mul_comm] using this
  have hrep : ∀ q : IdeleGroup F ⧸ H, ∃ b : normOneSubgroup F, ((b : IdeleGroup F) : IdeleGroup F ⧸ H) = q := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨h, hh, hb⟩ := hcov a
    refine ⟨⟨_, hb⟩, ?_⟩
    rw [QuotientGroup.eq]
    simpa using hh
  have hA₀m : MeasurableSet A₀ := (hHo.preimage continuous_subtype_val).measurableSet
  have hAm : ∀ q, MeasurableSet (A q) := by
    intro q
    obtain ⟨b, rfl⟩ := hrep q
    have : A ((b : IdeleGroup F) : IdeleGroup F ⧸ H) = (fun u => u * b⁻¹) ⁻¹' A₀ := by
      ext u; exact hmemA b u
    rw [this]
    exact (measurable_mul_const _) hA₀m
  have hinv : ∀ (ξ : Fˣ) (u : normOneSubgroup F),
      A₀.indicator (fun _ => (1 : ℝ≥0∞)) (diagonalToNormOne F ξ * u) = A₀.indicator (fun _ => (1 : ℝ≥0∞)) u := by
    intro ξ u
    have : diagonalToNormOne F ξ * u ∈ A₀ ↔ u ∈ A₀ := by
      change ((diagonal F ξ) * (u : IdeleGroup F)) ∈ H ↔ (u : IdeleGroup F) ∈ H
      exact H.mul_mem_cancel_left (hpr ξ)
    by_cases hu : u ∈ A₀
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (this.2 hu)]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (fun h => hu (this.1 h))]
  have hq : ∀ q, m (A q) = m A₀ := by
    intro q
    obtain ⟨b, rfl⟩ := hrep q
    have h := setLIntegral_mul_right (F := F) (A₀.indicator fun _ => (1 : ℝ≥0∞)) hinv b⁻¹
    have e : (fun u => A₀.indicator (fun _ => (1 : ℝ≥0∞)) (u * b⁻¹)) =
        (A ((b : IdeleGroup F) : IdeleGroup F ⧸ H)).indicator fun _ => (1 : ℝ≥0∞) := by
      funext u
      by_cases hu : u * b⁻¹ ∈ A₀
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem ((hmemA b u).2 hu)]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (fun h => hu ((hmemA b u).1 h))]
    rw [← hm, e, lintegral_indicator_const (hAm _), lintegral_indicator_const hA₀m, one_mul, one_mul] at h
    exact h
  have hunion : (Set.univ : Set (normOneSubgroup F)) = ⋃ q, A q := by
    ext u; simp [A]
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro q q' hne
    refine Set.disjoint_left.2 fun u h h' => hne ?_
    exact h.symm.trans h'
  have htot : m Set.univ = (H.index : ℝ≥0∞) * m A₀ := by
    rw [hunion, measure_iUnion hdisj hAm, tsum_fintype]
    simp only [hq]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hV : m Set.univ = normOneMeasure F (normOneFundamentalDomain F) := Measure.restrict_apply_univ _
  have hA' : m A₀ = normOneMeasure F (normOneFundamentalDomain F ∩ A₀) := by
    rw [hm, Measure.restrict_apply hA₀m, Set.inter_comm]
  rw [← hA', ← hV, htot, ENNReal.eq_div_iff (by exact_mod_cast hHi) (ENNReal.natCast_ne_top _)]

def Phi (f : IdeleGroup F → ℝ≥0∞) (a : IdeleGroup F) : ℝ≥0∞ := ENNReal.ofReal (md a) * th f a

theorem Phi_pr_mul (f : IdeleGroup F → ℝ≥0∞) (ξ : Fˣ) (a : IdeleGroup F) : Phi f (pr ξ * a) = Phi f a := by
  simp only [Phi, th_pr_mul, md_mul, md_pr, one_mul]

theorem measurable_Phi {f : IdeleGroup F → ℝ≥0∞} (hf : Measurable f) : Measurable (Phi f) :=
  (ENNReal.measurable_ofReal.comp continuous_md.measurable).mul (measurable_th hf)

theorem fiber_eq (w : InfinitePlace F) (f : IdeleGroup F → ℝ≥0∞) {t : ℝ} (ht : 0 < t)  :
    ENNReal.ofReal t * ∫⁻ u in normOneFundamentalDomain F,
        th f ((u : IdeleGroup F) * moduleSection w ⟨t, ht⟩) ∂normOneMeasure F =
      ∫⁻ u in normOneFundamentalDomain F, Phi f ((u : IdeleGroup F) * moduleSection w ⟨t, ht⟩) ∂normOneMeasure F := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun u => ?_
  have hu : md (u : IdeleGroup F) = 1 := mem_normOneSubgroup.1 u.2
  have hs : md (moduleSection w ⟨t, ht⟩) = t := by simp [md]
  simp only [Phi, md_mul, hu, hs, one_mul]

theorem fiber_translate {f : IdeleGroup F → ℝ≥0∞} (a b : IdeleGroup F) (hab : md a = md b) :
    ∫⁻ u in normOneFundamentalDomain F, Phi f ((u : IdeleGroup F) * a) ∂normOneMeasure F =
      ∫⁻ u in normOneFundamentalDomain F, Phi f ((u : IdeleGroup F) * b) ∂normOneMeasure F := by
  have hm : a * b⁻¹ ∈ normOneSubgroup F := by
    rw [normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv,
      show ideleModule F a = ideleModule F b from Subtype.ext hab, mul_inv_cancel]
  have := setLIntegral_mul_right (F := F) (fun u => Phi f ((u : IdeleGroup F) * b)) (fun ξ u => ?_) ⟨a * b⁻¹, hm⟩
  · simpa [mul_assoc] using this
  · simp only [Subgroup.coe_mul, coe_diagonalToNormOne, mul_assoc]
    exact Phi_pr_mul f ξ _

theorem tendsto_fiber (hF : IsTotallyReal F) {θ : ℝ →+* HeckeCharacterZeroLocus.SiegelWeilU.Ainf F} (hθ : Continuous θ) {r : ℝ → IdeleGroup F}
    (hr : IsRay θ r) (w : InfinitePlace F) (H : Subgroup (IdeleGroup F)) (hHo : IsOpen (H : Set (IdeleGroup F)))
    (hHi : H.index ≠ 0) (hpr : ∀ t : Fˣ, pr t ∈ H) (hrH : ∀ δ : ℝ, 0 < δ → r δ ∈ H) {f : IdeleGroup F → ℝ≥0∞}
    (hf : Measurable f) {c : ℝ≥0∞} (hA : Asym r H f c) :
    Tendsto (fun y : ℝ => ENNReal.ofReal (Real.exp y) * ∫⁻ u in normOneFundamentalDomain F,
        th f ((u : IdeleGroup F) * moduleSection w (expPos y)) ∂normOneMeasure F) atBot
      (𝓝 (c * (normOneMeasure F (normOneFundamentalDomain F) / (H.index : ℝ≥0∞)))) := by
  obtain ⟨⟨C, hC⟩, -, hoff, hlim⟩ := hA
  set d := Module.finrank ℚ F with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'

  have hcov : ∀ a : IdeleGroup F, ∃ h ∈ H, a * h⁻¹ ∈ normOneSubgroup F := by
    intro a
    have hx : 0 < md a ^ (1 / (d : ℝ)) := Real.rpow_pos_of_pos (md_pos a) _
    refine ⟨r _, hrH _ hx, ?_⟩
    have hm : md (r (md a ^ (1 / (d : ℝ)))) = md a := by
      rw [md_ray hF hθ hr hx, ← Real.rpow_natCast, ← Real.rpow_mul (md_pos a).le,
        one_div_mul_cancel hd0, Real.rpow_one]
    rw [normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv,
      show ideleModule F (r (md a ^ (1 / (d : ℝ)))) = ideleModule F a from Subtype.ext hm, mul_inv_cancel]
  have hvol := vol_inter H hHo hHi hpr hcov

  set A : Set (normOneSubgroup F) := {u | (u : IdeleGroup F) ∈ H} with hAdef
  have hAm : MeasurableSet A := (hHo.preimage continuous_subtype_val).measurableSet

  have hray : Tendsto (fun x : ℝ => ∫⁻ u in normOneFundamentalDomain F, Phi f ((u : IdeleGroup F) * r x) ∂normOneMeasure F)
      (𝓝[>] 0) (𝓝 (∫⁻ u in normOneFundamentalDomain F, A.indicator (fun _ => c) u ∂normOneMeasure F)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => (C : ℝ≥0∞)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun x => ?_
      exact (measurable_Phi hf).comp (continuous_subtype_val.measurable.mul_const _)
    · exact Eventually.of_forall fun x => Eventually.of_forall fun u => hC _
    · rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top (normOneMeasure_normOneFundamentalDomain_lt_top F).ne
    · refine Eventually.of_forall fun u => ?_
      by_cases hu : (u : IdeleGroup F) ∈ H
      · rw [Set.indicator_of_mem (show u ∈ A from hu)]
        exact hlim _ hu
      · rw [Set.indicator_of_notMem (show u ∉ A from hu)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        have : (u : IdeleGroup F) * r x ∉ H := fun h => hu (by
          simpa using H.mul_mem h (H.inv_mem (hrH x hx)))
        simp [Phi, hoff _ this]
  have hval : ∫⁻ u in normOneFundamentalDomain F, A.indicator (fun _ => c) u ∂normOneMeasure F =
      c * (normOneMeasure F (normOneFundamentalDomain F) / (H.index : ℝ≥0∞)) := by
    rw [lintegral_indicator_const hAm, Measure.restrict_apply hAm, Set.inter_comm, hvol]
  rw [hval] at hray
  have hx : Tendsto (fun y : ℝ => Real.exp (y / d)) atBot (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨Real.tendsto_exp_atBot.comp ?_, Eventually.of_forall fun y => Real.exp_pos _⟩
    exact tendsto_id.atBot_div_const (by positivity)
  refine (hray.comp hx).congr fun y => ?_
  have hm : md (moduleSection w (expPos y)) = md (r (Real.exp (y / d))) := by
    rw [md_ray hF hθ hr (Real.exp_pos _), ← Real.exp_nat_mul, mul_div_cancel₀ _ hd0]
    simp [md]
  rw [show expPos y = ⟨Real.exp y, Real.exp_pos y⟩ from rfl, fiber_eq w f (Real.exp_pos y)]
  exact (fiber_translate _ _ hm).symm

theorem tate : Tate := by
  intro F _ _ hF θ hθ r hr
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨normOneMeasure F (normOneFundamentalDomain F),
    (isFundamentalDomain_normOneFundamentalDomain F (normOneMeasure F)).measure_ne_zero (NeZero.ne _),
    (normOneMeasure_normOneFundamentalDomain_lt_top F).ne, ?_⟩
  intro H hHo hHi hpr hrH f c hf hA
  have hf' : Measurable (f : IdeleGroup F → ℝ≥0∞) := by
    have e : (HeckeCharacterZeroLocus.SiegelWeilU.measAF : MeasurableSpace (HeckeCharacterZeroLocus.SiegelWeilU.AF F)) = measurableSpace_adeleRing F :=
      (borelSpace_adeleRing F).measurable_eq.symm
    rw [e] at hf
    exact hf
  have hL := tendsto_fiber hF hθ hr w H hHo hHi hpr hrH hf' hA
  obtain ⟨⟨C, hC⟩, ⟨R, hR⟩, -, -⟩ := hA
  set J : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp y) * ∫⁻ u in normOneFundamentalDomain F,
        th f ((u : IdeleGroup F) * moduleSection w (expPos y)) ∂normOneMeasure F with hJdef
  have hJm : Measurable J :=
    (ENNReal.measurable_ofReal.comp Real.measurable_exp).mul (measurable_fiber w hf')
  have hle : ∀ y, J y ≤ C * normOneMeasure F (normOneFundamentalDomain F) := by
    intro y
    simp only [hJdef]
    rw [show expPos y = ⟨Real.exp y, Real.exp_pos y⟩ from rfl, fiber_eq w f (Real.exp_pos y)]
    calc _ ≤ ∫⁻ u in normOneFundamentalDomain F, (C : ℝ≥0∞) ∂normOneMeasure F := lintegral_mono fun u => hC _
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
  have h0 : ∀ y, Real.log (max R 1) < y → J y = 0 := by
    intro y hy
    have hlt : R < Real.exp y := by
      have := (Real.log_lt_iff_lt_exp (lt_of_lt_of_le one_pos (le_max_right R 1))).1 hy
      exact lt_of_le_of_lt (le_max_left R 1) this
    simp only [hJdef]
    have : ∀ u : normOneSubgroup F, th f ((u : IdeleGroup F) * moduleSection w (expPos y)) = 0 := by
      intro u
      refine hR _ ?_
      have hu : md (u : IdeleGroup F) = 1 := mem_normOneSubgroup.1 u.2
      have hs : md (moduleSection w (expPos y)) = Real.exp y := by simp [md]
      rw [md_mul, hu, hs, one_mul]
      exact hlt
    simp [this]
  have hB : (C : ℝ≥0∞) * normOneMeasure F (normOneFundamentalDomain F) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (normOneMeasure_normOneFundamentalDomain_lt_top F).ne
  obtain ⟨h1, h2⟩ := abel hJm hB hle h0 hL
  refine ⟨fun s hs => ?_, ?_⟩
  · rw [zi_eq w hf' s]
    exact h1 s hs
  · rw [mul_div_assoc]
    refine h2.congr fun s => ?_
    rw [zi_eq w hf' s]

end GlobalTheory.CompanionTheory.TateRes
