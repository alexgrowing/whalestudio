import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.JetProofs.ContinuousIteratedFDerivPartial
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarRightInvariantCompact

noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff InnerProductSpace

namespace GlobalTheory.CompanionTheory.KerUniq

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev UK (n : ℕ) := Matrix.unitaryGroup (Fin n) ℂ

def msK (n : ℕ) : MeasurableSpace (UK n) := borel _

attribute [local instance] msK

local instance : BorelSpace (UK n) := ⟨rfl⟩
local instance : CompactSpace (UK n) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
local instance : SecondCountableTopology (Mat n) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
local instance : LocallyCompactSpace (Mat n) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
local instance : SecondCountableTopology (G n) :=
  have : SecondCountableTopology (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology
local instance : LocallyCompactSpace (G n) := inferInstanceAs (LocallyCompactSpace (Mat n)ˣ)
local instance : SecondCountableTopology (UK n) :=
  (Topology.IsEmbedding.subtypeVal (p := fun x => x ∈ unitaryGroup (Fin n) ℂ)).secondCountableTopology

def emb : UK n →* G n := Unitary.toUnits

theorem emb_val (κ : UK n) : (emb κ).val = κ.1 := rfl

theorem continuous_emb : Continuous (emb : UK n → G n) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_subtype_val, ?_⟩
  show Continuous fun κ : UK n => star κ.1
  exact continuous_subtype_val.star

theorem map_mul_emb {_ : MeasurableSpace (G n)} [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (κ : UK n) : Measure.map (· * emb κ) μ = μ :=
  GlobalTheory.CompactRight.map_mul_right_eq_of_mem_compact μ emb.range
    (by rw [MonoidHom.coe_range]; exact isCompact_range continuous_emb) _ ⟨κ, rfl⟩

theorem integral_mul_emb {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {_ : MeasurableSpace (G n)}
    [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (H : G n → V) (κ : UK n) :
    ∫ y, H (y * emb κ) ∂μ = ∫ y, H y ∂μ := by
  conv_rhs => rw [← map_mul_emb μ κ]
  exact ((MeasurableEquiv.mulRight (emb κ)).measurableEmbedding.integral_map H).symm

theorem val_mem (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne.preimage (continuous_id.matrix_det)

theorem continuousOn_inv : ContinuousOn (fun y : Mat n => y⁻¹) (GLs n) := by
  have : (fun y : Mat n => y⁻¹) = fun y => (y.det)⁻¹ • y.adjugate := by
    funext y; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (continuous_id.matrix_det.continuousOn.inv₀ fun y hy => hy).smul
    continuous_id.matrix_adjugate.continuousOn

theorem continuousOn_lg : ContinuousOn (lg : Mat n → ℝ) (GLs n) := by
  have h : ContinuousOn (fun y : Mat n => 1 + ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2)) (GLs n) := by
    refine continuousOn_const.add (continuousOn_finset_sum _ fun a _ => continuousOn_finset_sum _ fun b _ => ?_)
    refine ContinuousOn.add ?_ ?_
    · exact ((continuous_id.matrix_elem a b).norm.pow 2).continuousOn
    · exact (((continuous_id.matrix_elem a b).comp_continuousOn continuousOn_inv).norm).pow 2
  refine h.log fun y _ => ?_
  have : 0 ≤ ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2) :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  positivity

theorem cpt_of {V : Type} [Zero V] {S : Set (Mat n)} (hS : IsCompact S) (hG : S ⊆ GLs n) {f : Mat n → V}
    (hf : ∀ y ∈ GLs n, y ∉ S → f y = 0) : Cpt f := by
  obtain ⟨R, hR⟩ := hS.bddAbove_image (continuousOn_lg.mono hG)
  refine ⟨R, fun y hy hlt => hf y hy fun hyS => ?_⟩
  exact absurd (hR (Set.mem_image_of_mem _ hyS)) (not_le.2 hlt)

theorem isCompact_preimage_val {C : Set (Mat n)} (hC : IsCompact C) (hs : C ⊆ GLs n) :
    IsCompact {y : G n | y.val ∈ C} := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC
  let φ : C → G n := fun c => Matrix.GeneralLinearGroup.mkOfDetNeZero c.1 (hs c.2)
  have hφ : Continuous φ := by
    rw [Units.continuous_iff]
    refine ⟨continuous_subtype_val, ?_⟩
    have : Continuous fun c : C => (c.1)⁻¹ :=
      continuousOn_iff_continuous_restrict.1 (continuousOn_inv.mono hs)
    refine this.congr fun c => ?_
    exact (Matrix.coe_units_inv (φ c)).symm
  have he : {y : G n | y.val ∈ C} = Set.range φ := by
    ext y
    constructor
    · intro hy
      exact ⟨⟨y.val, hy⟩, Units.ext rfl⟩
    · rintro ⟨c, rfl⟩
      exact c.2
  rw [he]
  exact isCompact_range hφ

theorem mul_inv_val (κ : UK n) : κ.1 * (κ⁻¹ : UK n).1 = 1 := by
  simpa using congrArg Subtype.val (mul_inv_cancel κ)

def nu (n : ℕ) : Measure (UK n) := Measure.haar

local instance : (nu n).IsHaarMeasure := by unfold nu; infer_instance
local instance : IsFiniteMeasure (nu n) := CompactSpace.isFiniteMeasure

section Sec

variable (E : KMod n)

theorem continuous_orbit (v : E.V) : Continuous fun κ : UK n => E.ρ κ v :=
  E.cont.clm_apply continuous_const

def sec (β : Mat n → ℝ) (v : E.V) : Mat n → E.V := fun y => ∫ κ : UK n, β (y * κ.1) • E.ρ κ v ∂nu n

variable {E}
variable {β : Mat n → ℝ} {v : E.V}

theorem contDiff_mul : ContDiff ℝ ∞ fun p : Mat n × Mat n => p.1 * p.2 := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun l _ =>
    (contDiff_pi.1 (contDiff_pi.1 contDiff_fst i) l).mul (contDiff_pi.1 (contDiff_pi.1 contDiff_snd l) j)

theorem contDiff_sec (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (sec E β v) := by
  have hΨ : ContDiff ℝ ∞ (fun z : Mat n × (Mat n × E.V) => β (z.1 * z.2.1) • z.2.2) :=
    (hβ.comp (contDiff_mul.comp (contDiff_fst.prodMk contDiff_snd.fst))).smul contDiff_snd.snd
  exact GlobalTheory.CompanionTheory.ParSmooth.contDiff_integral_comp_compact (nu n) _ hΨ (fun κ : UK n => (κ.1, E.ρ κ v))
    (continuous_subtype_val.prodMk (continuous_orbit E v))

theorem integrable_avg (hβ : Continuous β) (y : Mat n) (a : UK n → E.V) (ha : Continuous a) :
    Integrable (fun κ : UK n => β (y * κ.1) • a κ) (nu n) :=
  ((hβ.comp (continuous_const.matrix_mul continuous_subtype_val)).smul ha).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem sec_mul (hβ : Continuous β) (y : Mat n) (k' : UK n) :
    sec E β v (y * k'.1) = E.ρ k'⁻¹ (sec E β v y) := by
  unfold sec
  have h1 : ∫ κ : UK n, β (y * k'.1 * κ.1) • E.ρ κ v ∂nu n =
      ∫ κ : UK n, (fun κ' : UK n => β (y * κ'.1) • E.ρ (k'⁻¹ * κ') v) (k' * κ) ∂nu n := by
    refine integral_congr_ae (Eventually.of_forall fun κ => ?_)
    simp [mul_assoc]
  rw [h1, integral_mul_left_eq_self (fun κ' : UK n => β (y * κ'.1) • E.ρ (k'⁻¹ * κ') v) k',
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hβ y _ (continuous_orbit E v))]
  refine integral_congr_ae (Eventually.of_forall fun κ => ?_)
  simp [map_mul, ContinuousLinearMap.map_smul_of_tower]

theorem sec_eq_zero {U : Set (Mat n)} (hU : ∀ y ∈ U, ∀ k₂ : UK n, y * k₂.1 ∈ U) (hs : tsupport β ⊆ U)
    {y : Mat n} (hy : y ∉ U) : sec E β v y = 0 := by
  unfold sec
  have : ∀ κ : UK n, β (y * κ.1) = 0 := fun κ => by
    by_contra h
    refine hy ?_
    have h2 := hU _ (hs (subset_tsupport _ h)) κ⁻¹
    rwa [mul_assoc, mul_inv_val, mul_one] at h2
  simp [this]

theorem cpt_sec {U : Set (Mat n)} (hU : ∀ y ∈ U, ∀ k₂ : UK n, y * k₂.1 ∈ U) (hUG : U ⊆ GLs n)
    (hc : HasCompactSupport β) (hs : tsupport β ⊆ U) : Cpt (sec E β v) := by
  let S : Set (Mat n) := (fun p : Mat n × UK n => p.1 * (p.2⁻¹ : UK n).1) '' (tsupport β ×ˢ Set.univ)
  have hcont : Continuous fun p : Mat n × UK n => p.1 * (p.2⁻¹ : UK n).1 :=
    continuous_fst.matrix_mul (continuous_subtype_val.comp (continuous_inv.comp continuous_snd))
  have hS : IsCompact S := (hc.isCompact.prod isCompact_univ).image hcont
  refine cpt_of hS ?_ fun y _ hy => ?_
  · rintro _ ⟨p, ⟨hp, -⟩, rfl⟩
    exact hUG (hU _ (hs hp) _)
  · unfold sec
    have : ∀ κ : UK n, β (y * κ.1) = 0 := fun κ => by
      by_contra h
      refine hy ⟨(y * κ.1, κ), ⟨subset_tsupport _ h, Set.mem_univ _⟩, ?_⟩
      simp only
      rw [mul_assoc, mul_inv_val, mul_one]
    simp [this]

end Sec

section Main

variable {E : KMod n} {β : Mat n → ℝ} {v : E.V} {k : Mat n → (E.V →L[ℂ] E.V)}

def hf (β : Mat n → ℝ) (k : Mat n → (E.V →L[ℂ] E.V)) (v : E.V) : G n → E.V :=
  fun y => β y.val • k y.val v

theorem continuous_hf (hβ : Continuous β) (hk : ContinuousOn k (GLs n)) : Continuous (hf β k v) :=
  (hβ.comp Units.continuous_val).smul
    ((hk.comp_continuous Units.continuous_val val_mem).clm_apply continuous_const)

theorem compact_hf (hc : HasCompactSupport β) (hs : tsupport β ⊆ GLs n) : HasCompactSupport (hf β k v) := by
  refine HasCompactSupport.intro (isCompact_preimage_val hc.isCompact hs) fun y hy => ?_
  have : β y.val = 0 := image_eq_zero_of_notMem_tsupport hy
  simp [hf, this]

theorem apply_sec (hβ : Continuous β)
    (hr : ∀ y ∈ GLs n, ∀ k₂ : UK n, k (y * k₂.1) = k y * E.ρ k₂) (y : G n) :
    k y.val (sec E β v (1 * y.val)) = ∫ κ : UK n, hf β k v (y * emb κ) ∂nu n := by
  unfold sec
  rw [one_mul, ← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hβ y.val _ (continuous_orbit E v))]
  refine integral_congr_ae (Eventually.of_forall fun κ => ?_)
  simp only [hf, Units.val_mul, emb_val]
  rw [hr _ (val_mem y), ContinuousLinearMap.map_smul_of_tower]
  rfl

theorem integrable_prod {_ : MeasurableSpace (G n)} [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {H : G n → E.V} (hH : Continuous H) (hc : HasCompactSupport H) :
    Integrable (Function.uncurry fun (y : G n) (κ : UK n) => H (y * emb κ)) (μ.prod (nu n)) := by
  have hcont : Continuous (Function.uncurry fun (y : G n) (κ : UK n) => H (y * emb κ)) :=
    hH.comp (continuous_fst.mul (continuous_emb.comp continuous_snd))
  refine hcont.integrable_of_hasCompactSupport ?_
  have hm : Continuous fun p : G n × UK n => (p.1 * (emb p.2)⁻¹, p.2) :=
    (continuous_fst.mul ((continuous_emb.comp continuous_snd).inv)).prodMk continuous_snd
  refine HasCompactSupport.intro ((hc.isCompact.prod isCompact_univ).image hm) fun p hp => ?_
  by_contra h
  refine hp ⟨(p.1 * emb p.2, p.2), ⟨subset_tsupport _ h, Set.mem_univ _⟩, ?_⟩
  simp

theorem act_sec {_ : MeasurableSpace (G n)} [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ GLs n)
    (hk : ContinuousOn k (GLs n)) (hr : ∀ y ∈ GLs n, ∀ k₂ : UK n, k (y * k₂.1) = k y * E.ρ k₂) :
    act μ E k (sec E β v) 1 = (nu n).real Set.univ • ∫ y, hf β k v y ∂μ := by
  have hH := continuous_hf (v := v) hβ hk
  have hC := compact_hf (k := k) (v := v) hc hs
  unfold act
  simp_rw [apply_sec hβ hr]
  rw [integral_integral_swap (integrable_prod μ hH hC)]
  simp_rw [integral_mul_emb μ (hf β k v)]
  simp

theorem main : PositivityTheory.RgBcC.KerUniq := by
  intro n _ _ μ _ E k U hU hUG hUK hk hr hact y₀ hy₀
  refine ContinuousLinearMap.ext fun v => ?_
  by_contra hne
  rw [ContinuousLinearMap.zero_apply] at hne
  set w := k y₀ v with hw
  let ℓ : E.V →L[ℝ] ℝ := Complex.reCLM ∘L ((innerSL ℂ w).restrictScalars ℝ)
  have hℓ : ∀ x, ℓ x = (⟪w, x⟫_ℂ).re := fun x => rfl
  have hℓw : 0 < ℓ w := by
    have h2 : (⟪w, w⟫_ℂ).re = ‖w‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) w
    rw [hℓ, h2]
    exact pow_pos (norm_pos_iff.2 hne) 2
  have hg : ContinuousAt (fun y => ℓ (k y v)) y₀ := by
    have h1 : ContinuousAt k y₀ := hk.continuousAt (isOpen_GLs.mem_nhds (hUG hy₀))
    exact ℓ.continuous.continuousAt.comp (h1.clm_apply continuousAt_const)
  have hs : U ∩ {y | 0 < ℓ (k y v)} ∈ 𝓝 y₀ :=
    inter_mem (hU.mem_nhds hy₀) (hg.eventually (lt_mem_nhds hℓw))
  obtain ⟨β, hts, hcs, hsm, hrg, h1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hs
  have hsm' : ContDiff ℝ ∞ β := hsm
  have hβ : Continuous β := hsm'.continuous
  have hsU : tsupport β ⊆ U := hts.trans Set.inter_subset_left
  have hsG := hsU.trans hUG
  have hmem : sec E β v ∈ CE E :=
    ⟨(contDiff_sec hsm').contDiffOn, fun g _ κ => sec_mul hβ g κ⟩
  have h0 := hact _ hmem (cpt_sec hUK hUG hcs hsU) fun y _ hy => sec_eq_zero hUK hsU hy
  rw [act_sec μ hβ hcs hsG hk hr] at h0
  have hνpos : (nu n).real Set.univ ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨(isOpen_univ.measure_pos _ Set.univ_nonempty).ne', measure_ne_top _ _⟩
  have hI : ∫ y, hf β k v y ∂μ = 0 := (smul_eq_zero.1 h0).resolve_left hνpos
  have hH := continuous_hf (v := v) hβ hk
  have hC := compact_hf (k := k) (v := v) hcs hsG
  have hzero : ∫ y, ℓ (hf β k v y) ∂μ = 0 := by
    rw [ContinuousLinearMap.integral_comp_comm _ (hH.integrable_of_hasCompactSupport hC), hI, map_zero]
  have hpos : 0 < ∫ y, ℓ (hf β k v y) ∂μ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := Matrix.GeneralLinearGroup.mkOfDetNeZero y₀ (hUG hy₀)) (ℓ.continuous.comp hH)
      (hC.comp_left (map_zero ℓ)) (fun y => ?_) ?_
    · have e : ℓ (hf β k v y) = β y.val * ℓ (k y.val v) := by
        simp only [hf]
        rw [map_smul, smul_eq_mul]
      show 0 ≤ ℓ (hf β k v y)
      rw [e]
      by_cases hb : β y.val = 0
      · simp [hb]
      · have h2 : 0 ≤ β y.val := (hrg (Set.mem_range_self _)).1
        exact mul_nonneg h2 (hts (subset_tsupport _ hb)).2.le
    · have e : ℓ (hf β k v (Matrix.GeneralLinearGroup.mkOfDetNeZero y₀ (hUG hy₀))) = ℓ w := by
        have hv : (Matrix.GeneralLinearGroup.mkOfDetNeZero y₀ (hUG hy₀)).val = y₀ := rfl
        simp only [hf, hv, h1, one_smul, hw]
      exact e ▸ hℓw.ne'
  exact hpos.ne' hzero

end Main

end GlobalTheory.CompanionTheory.KerUniq
