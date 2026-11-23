import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumAttainedWithBoundsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumContinuousCuspWeightMeasurableStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open GroundTheory.Automorphic

theorem lintegral_logPlus_le_of_mass {X : Type} [MeasurableSpace X] (μ : Measure X) (S : Set X)
    (h0 : μ S ≠ 0) (hT : μ S ≠ ⊤) (lam : X → ℝ) (c : ℝ → X → ℝ≥0∞) (a : ℕ) (ka r : ℝ)
    (lam_meas : Measurable lam) (lam_pos : ∀ z, 0 < lam z) (c_meas : ∀ t, Measurable (c t))
    (ha : 1 ≤ a) (hka : 3 * (a : ℝ) ≤ ka) (hr : 0 < r)
    (fin : ∀ t, 0 < t → ∫⁻ x in S, c t x ∂μ ≠ ⊤)
    (count : ∀ t, 0 < t → t ≤ r → ∀ z, lam z < t → (c t z).toReal ≤ (3 * t / lam z) ^ a)
    (zero : ∀ t, 0 < t → ∀ z, t ≤ lam z → c t z = 0)
    (one : ∀ t, 0 < t → t ≤ r → ∀ z, lam z < t → 1 ≤ (c t z).toReal)
    (scal : ∀ θ t, 0 < θ → 0 < t →
      ∫⁻ x in S, c (θ * t) x ∂μ = ENNReal.ofReal (θ ^ ka) * ∫⁻ x in S, c t x ∂μ) :
    ∫⁻ x in S, ENNReal.ofReal (Real.log (r / lam x)) ∂μ ≤ 3 * μ S := by
  set ν : Measure X := (μ S)⁻¹ • μ.restrict S with hν
  have hprob : IsProbabilityMeasure ν :=
    ⟨by simp [hν, ENNReal.inv_mul_cancel h0 hT]⟩
  have hlin : ∀ f : X → ℝ≥0∞, ∫⁻ x, f x ∂ν = (μ S)⁻¹ * ∫⁻ x in S, f x ∂μ := fun f => by
    rw [hν, lintegral_smul_measure]
    rfl
  have hfin : ∀ t, 0 < t → ∫⁻ x, c t x ∂ν ≠ ⊤ := fun t ht => by
    rw [hlin]
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 h0) (fin t ht)
  have hmean : ∀ t, 0 < t → GroundTheory.Heights₂.Heights.LowerBound.meanCount ν
      (fun t z => (c t z).toReal) t = (∫⁻ x, c t x ∂ν).toReal := fun t ht =>
    integral_toReal (c_meas t).aemeasurable (ae_lt_top (c_meas t) (hfin t ht))
  have H : GroundTheory.Heights₂.Heights.LowerBound.MeanCount.Hyp ν lam (fun t z => (c t z).toReal) a ka r :=
    { isProbability := hprob
      lam_meas := lam_meas
      lam_pos := lam_pos
      cnt_meas := fun t => (c_meas t).ennreal_toReal
      cnt_nonneg := fun _ _ => ENNReal.toReal_nonneg
      one_le_a := ha
      three_a_le_ka := hka
      r_pos := hr
      integrable := fun t ht => integrable_toReal_of_lintegral_ne_top (c_meas t).aemeasurable (hfin t ht)
      count := count
      zero := fun t ht z hz => by simp [zero t ht z hz]
      one := one
      scaling := fun θ t hθ ht => by
        rw [hmean _ (mul_pos hθ ht), hmean t ht, hlin, hlin, scal θ t hθ ht, mul_left_comm,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hθ.le _)] }
  obtain ⟨hint, hle⟩ := GroundTheory.Heights₂.Heights.LowerBound.MeanLogPlus.full X ν lam _ a ka r H
  have e1 : ∫⁻ x, ENNReal.ofReal (Real.log (r / lam x)) ∂ν =
      ENNReal.ofReal (∫ z, max 0 (Real.log (r / lam z)) ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => le_max_left _ _)]
    refine lintegral_congr fun z => ?_
    rcases le_total 0 (Real.log (r / lam z)) with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  have e2 : ∫⁻ x, ENNReal.ofReal (Real.log (r / lam x)) ∂ν ≤ 3 := by
    rw [e1]
    refine (ENNReal.ofReal_le_ofReal hle).trans ?_
    simp
  rw [hlin] at e2
  rw [mul_comm]
  exact (ENNReal.inv_mul_le_iff h0 hT).1 e2

section Card

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ringOfIntegers_hom_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  rw [injective_iff_map_eq_zero]
  have hk : RingHom.ker s = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [eq_bot_iff]
    intro m hm
    have h1 : s (algebraMap ℤ (𝓞 E) m) = 0 := hm
    have h2 : ((m : ℤ) : ℂ) = 0 := by simpa using h1
    simpa using (Int.cast_eq_zero.1 h2)
  intro a ha
  have : a ∈ RingHom.ker s := ha
  rw [hk] at this
  simpa using this

theorem finrank_eq_two_mul_card {Ψ : Type} [Fintype Ψ] {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) :
    Module.finrank ℚ E = 2 * Fintype.card Ψ := by
  classical
  let e : (E →+* ℂ) ≃ (𝓞 E →+* ℂ) :=
    { toFun := fun φ => φ.comp (algebraMap (𝓞 E) E)
      invFun := fun s => IsFractionRing.lift (ringOfIntegers_hom_injective s)
      left_inv := fun φ => by
        apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
        ext x
        simp
      right_inv := fun s => by
        ext x
        simp }
  haveI : Fintype (𝓞 E →+* ℂ) := Fintype.ofEquiv _ e
  have hc : Fintype.card (𝓞 E →+* ℂ) = Module.finrank ℚ E := by
    rw [← Fintype.card_congr e]
    exact NumberField.Embeddings.card E ℂ
  let P : (𝓞 E →+* ℂ) → Prop := fun s => ∃ τ, σ τ = s
  let c : (𝓞 E →+* ℂ) → (𝓞 E →+* ℂ) := fun s => (starRingEnd ℂ).comp s
  have hcc : ∀ s, c (c s) = s := fun s => by
    ext x
    simp [c]
  have hP : ∀ s, P s ↔ ¬ P (c s) := hσ.2
  have e1 : {s // P s} ≃ Ψ := (Equiv.ofInjective σ hσ.1).symm
  have e2 : {s // ¬ P s} ≃ {s // P s} :=
    { toFun := fun s => ⟨c s.1, by
        by_contra hn
        exact s.2 ((hP s.1).2 hn)⟩
      invFun := fun s => ⟨c s.1, (hP s.1).1 s.2⟩
      left_inv := fun s => Subtype.ext (hcc s.1)
      right_inv := fun s => Subtype.ext (hcc s.1) }
  have := Fintype.card_congr (Equiv.sumCompl P)
  rw [Fintype.card_sum, Fintype.card_congr e2, Fintype.card_congr e1, hc] at this
  omega

theorem finrank_real_eq_card {Ψ : Type} [Fintype Ψ] {σ : Ψ → (𝓞 E →+* ℂ)} (hσ : IsCMFam σ) :
    Module.finrank ℚ (maximalRealSubfield E) = Fintype.card Ψ := by
  have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E,
    finrank_eq_two_mul_card hσ] at h1
  omega

end Card

section Count

theorem measurable_countBelow {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] [IsTotallyReal K] [IsTotallyComplex L] {W : Type} [AddCommGroup W]
    [Module L W] [Countable W] {ι : Type} [Fintype ι] [DecidableEq ι] {h : HermitianForm K L W}
    {v : Module.Basis ι L W} (M : Majorant h v) (VV : Set W) (t : ℝ) :
    Measurable fun a => countBelow M VV a t := by
  classical
  have e : (fun a => countBelow M VV a t) = fun a => ∑' x : W,
      ({y ∈ VV | M.len (invApply a (vecAt v y)) < t}).indicator (1 : W → ℝ≥0∞) x := by
    funext a
    rw [countBelow, ← ENNReal.tsum_set_one, tsum_subtype _ (fun _ => (1 : ℝ≥0∞))]
    rfl
  rw [e]
  refine Measurable.ennreal_tsum fun x => ?_
  by_cases hx : x ∈ VV
  · have e2 : (fun a => ({y ∈ VV | M.len (invApply a (vecAt v y)) < t}).indicator (1 : W → ℝ≥0∞) x) =
        ({a | M.len (invApply a (vecAt v x)) < t}).indicator (1 : archUnitary h v → ℝ≥0∞) := by
      funext a
      simp [Set.indicator, hx]
    rw [e2]
    have hopen : IsOpen {a : archUnitary h v | M.len (invApply a (vecAt v x)) < t} :=
      isOpen_lt (continuous_len_invApply M (vecAt v x)) continuous_const
    exact measurable_one.indicator hopen.measurableSet
  · have e2 : (fun a : archUnitary h v =>
        ({y ∈ VV | M.len (invApply a (vecAt v y)) < t}).indicator (1 : W → ℝ≥0∞) x) = fun _ => 0 := by
      funext a
      simp [Set.indicator, hx]
    rw [e2]
    exact measurable_const

theorem toReal_encard_of_finite {α : Type} {s : Set α} (hs : s.Finite) :
    (((s.encard : ℕ∞) : ℝ≥0∞)).toReal = s.ncard := by
  rw [← hs.cast_ncard_eq]
  simp

end Count

section Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ] {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} {F : UnivFam E Ψ j j' n g Λ}

theorem GroupDict.π_mem (Δ : GroupDict F) (a) : Δ.π a ∈ ballDom F.q := by
  rw [← Δ.π_range]
  exact ⟨a, rfl⟩

theorem GroupDict.sqrt_normSq (Δ : GroupDict F) (a) (x : Λ) :
    Real.sqrt ((F.R (Δ.π a)).normSq x) = Real.sqrt Δ.κ *
      Δ.M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (Δ.e x))) := by
  have h0 : 0 ≤ Δ.M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (Δ.e x))) := Real.sqrt_nonneg _
  rw [Δ.len, Real.sqrt_mul Δ.κ_pos.le, Real.sqrt_sq h0]

theorem firstMinimum_le_sqrt_normSq (R : RiemLat E g Λ) {y : Λ} (hy : y ≠ 0) : R.lam1 ≤ Real.sqrt (R.normSq y) := by
  refine csInf_le ⟨0, ?_⟩ ⟨y, hy, rfl⟩
  rintro _ ⟨v, -, rfl⟩
  exact Real.sqrt_nonneg _

def GroupDict.shortSet (Δ : GroupDict F) (C : ℕ) : Set (Fin (j + j') → E) :=
  {x | x ∈ Δ.e.range ∧ x ≠ 0 ∧ Δ.h.toSesq x x = 0 ∧ lineIndex E Δ.e.range x ≤ C}

open scoped Pointwise in
theorem GroupDict.shortSet_stable (Δ : GroupDict F) (C : ℕ) :
    ∀ γ ∈ latticeStab Δ.h Δ.e.range, ∀ x ∈ Δ.shortSet C, γ • x ∈ Δ.shortSet C := by
  rintro γ hγ x ⟨hx, hx0, hiso, hC⟩
  have hs : γ • Δ.e.range = Δ.e.range := MulAction.mem_stabilizer_iff.1 hγ
  refine ⟨?_, fun h => hx0 ((smul_eq_zero_iff_eq γ).1 h), ?_, ?_⟩
  · have h1 : γ • x ∈ γ • Δ.e.range := AddSubgroup.smul_mem_pointwise_smul _ _ _ hx
    rwa [hs] at h1
  · rw [← hiso]
    exact HermitianForm.mem_unitaryGroup.1 γ.2 x x
  · rw [GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane.lineIndex_smul hs]
    exact hC

theorem GroupDict.below_subset (Δ : GroupDict F) (C : ℕ) (a) (t : ℝ) :
    {x ∈ Δ.shortSet C | Δ.M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) x)) < t / Real.sqrt Δ.κ} ⊆
      Δ.e '' {y | y ≠ 0 ∧ Real.sqrt ((F.R (Δ.π a)).normSq y) < t} := by
  have hk : 0 < Real.sqrt Δ.κ := Real.sqrt_pos.2 Δ.κ_pos
  rintro x ⟨⟨⟨y, rfl⟩, hx0, -, -⟩, hlt⟩
  refine ⟨y, ⟨fun h => hx0 (by rw [h, map_zero]), ?_⟩, rfl⟩
  rw [Δ.sqrt_normSq]
  exact (lt_div_iff₀' hk).1 hlt

end Group

section Main

theorem group_mean_logPlus_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F) (μ : Measure (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))) [μ.IsHaarMeasure] (vr : ℝ), 1 ≤ j' → 3 * j' + 1 ≤ j + j' → 0 < vr → (∃ a : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧ ∀ i (s : E →+* ℂ), ‖s (a i)‖ ≤ vr) → ∃ FD : Set (archUnitary Δ.h (Pi.basisFun E (Fin (j + j')))), IsFundamentalDomain (archLatticeGroup Δ.h (Pi.basisFun E (Fin (j + j'))) Δ.e.range) FD μ ∧ μ FD ≠ 0 ∧ μ FD ≠ ⊤ ∧ ∫⁻ a in FD, ENNReal.ofReal (Real.log (vr ^ (-(1 / 2 : ℝ)) / (F.R (Δ.π a)).lam1)) ∂μ ≤ 3 * μ FD := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F Δ μ _ vr hj' hN hvr hfam
  classical
  have hEc : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hcard : Module.finrank ℚ (maximalRealSubfield E) = Fintype.card Ψ := finrank_real_eq_card F.cm
  have hdeg : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [hcard]
    exact finrank_eq_two_mul_card F.cm
  have hfam' : ∃ a : Fin (2 * Module.finrank ℚ (maximalRealSubfield E)) → 𝓞 E,
      LinearIndependent ℚ (fun i => (a i : E)) ∧ ∀ i (s : E →+* ℂ), ‖s (a i)‖ ≤ vr := by
    obtain ⟨a, hli, hb⟩ := hfam
    refine ⟨a ∘ Fin.cast hdeg.symm, hli.comp _ (Fin.cast_injective _), fun i s => hb _ s⟩
  set r : ℝ := vr ^ (-(1 / 2 : ℝ)) with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos hvr _
  have hk : 0 < Real.sqrt Δ.κ := Real.sqrt_pos.2 Δ.κ_pos
  set C : ℕ := ⌊(vr * Real.sqrt (2 * Module.finrank ℚ (maximalRealSubfield E))) ^
    (2 * Module.finrank ℚ (maximalRealSubfield E))⌋₊ with hC
  set VV := Δ.shortSet C with hVV
  have hI := fun a => GlobalTheory.T.first_minimum_attained_with_bounds E Ψ j j' n g Λ (F.R (Δ.π a)) F.σ vr F.cm (F.sig _ (Δ.π_mem a)) hj' hvr hfam
  obtain ⟨FD, hFD, hm⟩ := ScalingLaw.full Δ.h (Pi.basisFun E (Fin (j + j'))) Δ.M μ Δ.Dn Δ.e.range VV Δ.integral (fun x hx => hx.1)
    (fun x hx => ⟨hx.2.1, hx.2.2.1⟩) (Δ.shortSet_stable C) ⟨C, fun x hx => hx.2.2.2⟩
  obtain ⟨FD₂, hFD₂, hlt⟩ := ArithmeticCovolumeFinite.full Δ.h (Pi.basisFun E (Fin (j + j'))) μ Δ.Dn Δ.e.range Δ.integral
  have hcount : Countable (archLatticeGroup Δ.h (Pi.basisFun E (Fin (j + j'))) Δ.e.range) := by
    have : Countable Δ.h.unitaryGroup := countable_unitaryGroup Δ.h (Pi.basisFun E (Fin (j + j')))
    have h1 : ((archLatticeGroup Δ.h (Pi.basisFun E (Fin (j + j'))) Δ.e.range : Subgroup _) : Set (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))).Countable := by
      rw [archLatticeGroup, Subgroup.coe_map]
      exact (Set.to_countable _).image _
    exact h1.to_subtype
  have hT : μ FD ≠ ⊤ := by
    rw [hFD.measure_eq hFD₂]
    exact hlt.ne
  have h0 : μ FD ≠ 0 := by
    intro hz
    have h1 : μ Set.univ = 0 := by
      rw [hFD.measure_eq_tsum Set.univ]
      refine ENNReal.tsum_eq_zero.2 fun γ => ?_
      exact measure_mono_null Set.inter_subset_right hz
    exact (isOpen_univ.measure_ne_zero μ Set.univ_nonempty) h1
  refine ⟨FD, hFD, h0, hT, ?_⟩
  have hcont := (GlobalTheory.T.first_minimum_continuous_cusp_weight_measurable E Ψ j j' n g Λ F hj').1
  have hlamc : Continuous fun a => (F.R (Δ.π a)).lam1 := hcont.comp_continuous Δ.π_cont Δ.π_mem

  have hfinS : ∀ a t, (F.R (Δ.π a)).lam1 < t → t ≤ r →
      {x ∈ VV | Δ.M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) x)) < t / Real.sqrt Δ.κ}.Finite ∧
      ({x ∈ VV | Δ.M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) x)) < t / Real.sqrt Δ.κ}.ncard : ℝ) ≤
        (3 * t / (F.R (Δ.π a)).lam1) ^ (2 * Fintype.card Ψ * j') := by
    intro a t h1 h2
    obtain ⟨-, -, -, h4⟩ := hI a
    obtain ⟨hf, hb⟩ := h4 t h1 h2
    have hsub := Δ.below_subset C a t
    have hfi := hf.image Δ.e
    refine ⟨hfi.subset hsub, le_trans ?_ hb⟩
    have := (Set.ncard_le_ncard hsub hfi).trans (Set.ncard_image_le hf)
    exact_mod_cast this
  refine lintegral_logPlus_le_of_mass μ FD h0 hT (fun a => (F.R (Δ.π a)).lam1)
    (fun t a => countBelow Δ.M VV a (t / Real.sqrt Δ.κ)) (2 * Fintype.card Ψ * j')
    ((2 * Module.finrank ℚ (maximalRealSubfield E) * (Module.finrank E (Fin (j + j') → E) - 1) : ℕ) : ℝ) r
    hlamc.measurable (fun a => (hI a).1) (fun t => measurable_countBelow Δ.M VV _) ?_ ?_ hrpos ?_ ?_ ?_ ?_ ?_
  · have hc : 0 < Fintype.card Ψ := by
      have : 0 < Module.finrank ℚ E := Module.finrank_pos
      omega
    have : 1 ≤ 2 * Fintype.card Ψ := by omega
    exact Nat.mul_le_mul this hj'
  · rw [hcard]
    have e1 : Module.finrank E (Fin (j + j') → E) = j + j' := by simp
    rw [e1]
    have e2 : 3 * j' ≤ j + j' - 1 := by omega
    have e3 : 3 * (2 * Fintype.card Ψ * j') ≤ 2 * Fintype.card Ψ * (j + j' - 1) := by
      calc 3 * (2 * Fintype.card Ψ * j') = 2 * Fintype.card Ψ * (3 * j') := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ e2
    exact_mod_cast e3
  · intro t ht
    exact ((hm _ (div_pos ht hk)).1).ne
  · intro t ht ht' a ha
    obtain ⟨hf, hb⟩ := hfinS a t ha ht'
    simp only [countBelow]
    rw [toReal_encard_of_finite hf]
    exact hb
  · intro t ht a ha
    have hemp : {x ∈ VV | Δ.M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) x)) < t / Real.sqrt Δ.κ} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨y, ⟨hy0, hy⟩, -⟩ := Δ.below_subset C a t hx
      exact absurd (ha.trans (firstMinimum_le_sqrt_normSq _ hy0)) (not_le.2 hy)
    simp [countBelow, hemp]
  · intro t ht ht' a ha
    obtain ⟨hf, -⟩ := hfinS a t ha ht'
    simp only [countBelow]
    rw [toReal_encard_of_finite hf]
    obtain ⟨-, ⟨x, hx0, hxl⟩, horth, -⟩ := hI a
    have hxr : Real.sqrt ((F.R (Δ.π a)).normSq x) < r := by
      rw [hxl]
      exact ha.trans_le ht'
    have hex0 : Δ.e x ≠ 0 := fun h => hx0 (Δ.e_inj (by rw [h, map_zero]))
    have hiso : Δ.h.toSesq (Δ.e x) (Δ.e x) = 0 := by
      refine (Δ.orth x x).2 fun c => ?_
      have := horth x x hxr hxr c
      rwa [(F.form_eq _)] at this
    have hmin : ∀ y ∈ Δ.e.range, y ≠ 0 → Δ.M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (Δ.e x))) ≤
        Δ.M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) y)) := by
      rintro _ ⟨y, rfl⟩ hy
      have hy0 : y ≠ 0 := fun h => hy (by rw [h, map_zero])
      have h1 := firstMinimum_le_sqrt_normSq (F.R (Δ.π a)) hy0
      rw [← hxl, Δ.sqrt_normSq, Δ.sqrt_normSq] at h1
      exact le_of_mul_le_mul_left h1 hk
    have hidx := ShortestVectorIndex.full Δ.h (Pi.basisFun E (Fin (j + j'))) Δ.M vr hfam' Δ.Dn Δ.e.range a (Δ.e x) Δ.integral ⟨x, rfl⟩ hex0 hmin
    have hmem : Δ.e x ∈ {x ∈ VV | Δ.M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) x)) < t / Real.sqrt Δ.κ} := by
      refine ⟨⟨⟨x, rfl⟩, hex0, hiso, Nat.le_floor hidx⟩, ?_⟩
      rw [lt_div_iff₀' hk, ← Δ.sqrt_normSq, hxl]
      exact ha
    have : 0 < {x ∈ VV | Δ.M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) x)) < t / Real.sqrt Δ.κ}.ncard :=
      (Set.ncard_pos hf).2 ⟨_, hmem⟩
    exact_mod_cast this
  · intro θ t hθ ht
    have h1 := ((hm _ (div_pos ht hk)).2 θ hθ)
    simp only [massBelow] at h1
    rw [Real.rpow_natCast, ← h1]
    simp only [mul_div_assoc]

end Main

end GlobalTheory.CompanionTheory.Ar.Cusp
