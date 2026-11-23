import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas.Model

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem sphV_zero : sphV 0 = 1 := by simp [sphV]

theorem volU_one : volU 1 = 2 * Real.pi := by simp [volU, sphV]

theorem volU_two : volU 2 = 8 * Real.pi ^ 3 := by
  have : Finset.Icc 1 2 = {1, 2} := by decide
  simp [volU, sphV, this]; ring

theorem dimN_two : dimN 2 ![1] = 1 := by decide

theorem dimN_test : 9 ^ 2 = (9 - 2 * 3) ^ 2 + 2 * (1 ^ 2 + 2 ^ 2) + 2 * dimN 9 ![1, 2] := by decide

open Pointwise in

theorem covol_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] (D : Set G) (hD : IsFundamentalDomain Γ D μ)
    (hm : MeasurableSet D) (hc : ∀ x, ∃ γ ∈ (Γ : Set G), γ * x ∈ D) :
    covol (Γ : Set G) μ Set.univ = μ D := by
  apply le_antisymm
  · exact iInf_le_of_le D (iInf_le_of_le hm (iInf_le_of_le (fun x _ => hc x) le_rfl))
  · refine le_iInf fun D' => le_iInf fun hm' => le_iInf fun hc' => ?_
    rw [hD.measure_eq_tsum D']
    have : D ⊆ ⋃ g : Γ, (g • D' ∩ D) := by
      intro x hx
      obtain ⟨γ, hγ, h⟩ := hc' x trivial
      refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
      rw [Set.mem_inv_smul_set_iff]
      exact h
    exact (measure_mono this).trans (measure_iUnion_le _)

def e2 : Fin 2 → Bool := ![true, false]

def W2 : Fin 2 → Submodule ℂ (Fin 2 → ℂ) := ![⊥, Submodule.span ℂ {![1, 1]}]

theorem isIsotropicFlag_unitary_one_one : IsIsoFlag e2 ![1] W2 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [W2]
  · intro i
    fin_cases i
    have : (![1, 1] : Fin 2 → ℂ) ≠ 0 := by
      intro h; simpa using congrFun h 0
    change Module.finrank ℂ (Submodule.span ℂ {(![1, 1] : Fin 2 → ℂ)}) =
      Module.finrank ℂ (⊥ : Submodule ℂ (Fin 2 → ℂ)) + 1
    rw [finrank_span_singleton this, finrank_bot]
  · intro x hx y hy
    change x ∈ Submodule.span ℂ {![1, 1]} at hx
    change y ∈ Submodule.span ℂ {![1, 1]} at hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
    simp [Formalism.REAL.Jm, e2, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.diagonal]

def nM (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 + t * Complex.I / 2, -(t * Complex.I / 2); t * Complex.I / 2, 1 - t * Complex.I / 2]

theorem nM_add (s t : ℝ) : nM s * nM t = nM (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem nM_zero : nM 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nM]

def nU (t : ℝ) : Formalism.REAL.UJ e2 :=
  ⟨⟨nM t, nM (-t), by rw [nM_add]; simp [nM_zero], by rw [nM_add]; simp [nM_zero]⟩, by
    change Formalism.REAL.inUJ e2 (nM t)
    unfold Formalism.REAL.inUJ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nM, Formalism.REAL.Jm, e2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.conjTranspose_apply,
        map_ofNat] <;>
      ring⟩

theorem nU_add (s t : ℝ) : nU s * nU t = nU (s + t) :=
  Subtype.ext (Units.ext (nM_add s t))

theorem hs_nU (t : ℝ) : Real.sqrt (Formalism.REAL.hs (uMat (nU t) - 1)) = |t| := by
  have : Formalism.REAL.hs (uMat (nU t) - 1) = t ^ 2 := by
    change Formalism.REAL.hs (nM t - 1) = t ^ 2
    simp [Formalism.REAL.hs, nM, Fin.sum_univ_two, Matrix.one_apply, div_pow]
    ring
  rw [this, Real.sqrt_sq_eq_abs]

theorem continuous_nM : Continuous nM := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [nM] <;> fun_prop

theorem continuous_nU : Continuous nU := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.2 ⟨continuous_nM, ?_⟩
  exact continuous_nM.comp continuous_neg

theorem flagVariety_unitary_one_one : flagN e2 W2 = Set.range nU := by
  ext g
  constructor
  · rintro ⟨h1, -⟩
    have h := h1 0 ![1, 1] (Submodule.subset_span rfl)
    change _ ∈ (⊥ : Submodule ℂ (Fin 2 → ℂ)) at h
    rw [Submodule.mem_bot, sub_eq_zero] at h
    have hu : (uMat g)ᴴ * Formalism.REAL.Jm e2 * uMat g = Formalism.REAL.Jm e2 := g.2
    have a0 := congrFun h 0
    have a1 := congrFun h 1
    have b00 := congrFun (congrFun hu 0) 0
    have b01 := congrFun (congrFun hu 0) 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at a0 a1
    simp [Formalism.REAL.Jm, e2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] at b00 b01
    set a := uMat g 0 0 with ha
    set b := uMat g 0 1 with hb
    set c := uMat g 1 0 with hc
    set d := uMat g 1 1 with hd
    have hb' : b = 1 - a := by linear_combination a0
    have hd' : d = 1 - c := by linear_combination a1
    have hac : (starRingEnd ℂ) a - (starRingEnd ℂ) c = 1 := by
      rw [hb', hd'] at b01
      linear_combination b00 + b01
    have hac' : a = 1 + c := by
      have := congrArg (starRingEnd ℂ) hac
      simp at this
      linear_combination this
    have hre : c.re = 0 := by
      have h3 : c + (starRingEnd ℂ) c = 0 := by
        have h4 : (starRingEnd ℂ) a = 1 + (starRingEnd ℂ) c := by linear_combination hac
        rw [h4, hac'] at b00
        linear_combination b00
      have := congrArg Complex.re h3
      simp at this
      linarith
    have hcI : c = ((2 * c.im : ℝ) : ℂ) * Complex.I / 2 := by
      apply Complex.ext <;> simp [hre]
    refine ⟨2 * c.im, Subtype.ext (Units.ext ?_)⟩
    change nM (2 * c.im) = uMat g
    ext i j
    fin_cases i <;> fin_cases j
    · change 1 + _ = a
      rw [← hcI, hac']
    · change -_ = b
      rw [← hcI, hb', hac']; ring
    · change _ = c
      exact hcI.symm
    · change 1 - _ = d
      rw [← hcI, hd']
  · rintro ⟨t, rfl⟩
    have key : ∀ a : ℂ, uMat (nU t) *ᵥ (a • ![1, 1]) - a • ![1, 1] = 0 := by
      intro a
      change nM t *ᵥ (a • ![1, 1]) - a • ![1, 1] = 0
      ext i
      fin_cases i <;> simp [nM, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
    · fin_cases i
      change y ∈ Submodule.span ℂ {![1, 1]} at hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [key]; exact Submodule.zero_mem _
    · have h := hy ![1, 1] (Submodule.subset_span rfl)
      simp [Formalism.REAL.Jm, e2, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.diagonal] at h
      have : y = y 0 • ![1, 1] := by
        ext i
        fin_cases i
        · simp
        · simp; linear_combination -h
      rw [this, key]; exact Submodule.zero_mem _

theorem isGaugeSub_flagN : IsGaugeSub (flagN e2 W2) (dimN 2 ![1]) (Measure.map nU volume) := by
  have hm : Measurable nU := continuous_nU.measurable
  rw [dimN_two, flagVariety_unitary_one_one]
  refine ⟨?_, ?_, ?_⟩
  · have hinj : Function.Injective nU := by
      intro s t h
      have := congrArg (fun g => (uMat g 1 0).im) h
      change (nM s 1 0).im = (nM t 1 0).im at this
      simpa [nM] using this
    have : MeasurableSet (Set.range nU) := hm.measurableEmbedding hinj |>.measurableSet_range
    rw [Measure.map_apply hm this.compl]
    simp
  · rintro _ ⟨s, rfl⟩
    rw [Measure.map_map (measurable_const_mul _) hm]
    have : ((fun g => nU s * g) ∘ nU) = nU ∘ fun t => s + t := by
      funext t; exact nU_add s t
    rw [this, ← Measure.map_map hm (measurable_const_add s), map_add_left_eq_self]
  · have hb : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) = 2 := by
      rw [EuclideanSpace.volume_ball]
      have : Real.Gamma (1 / 2 + 1) = √Real.pi / 2 := by
        rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
      have hp : √Real.pi ≠ 0 := by positivity
      simp only [Fintype.card_fin, Nat.cast_one, this, pow_one, ENNReal.ofReal_one, one_mul]
      rw [show √Real.pi / (√Real.pi / 2) = 2 by field_simp]
      simp
    rw [hb]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : 0 < r := hr
    have hcl : MeasurableSet {g : Formalism.REAL.UJ e2 | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
      refine (isClosed_le ?_ continuous_const).measurableSet
      have : Continuous fun g : Formalism.REAL.UJ e2 => uMat g :=
        Units.continuous_val.comp continuous_subtype_val
      unfold Formalism.REAL.hs
      fun_prop
    rw [Measure.map_apply hm hcl]
    have : nU ⁻¹' {g : Formalism.REAL.UJ e2 | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} = Set.Icc (-r) r := by
      ext t
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, hs_nU, Set.mem_Icc, abs_le]
    rw [this, Real.volume_Icc, pow_one, ← ENNReal.ofReal_div_of_pos hr']
    rw [show (r - -r) / r = 2 by field_simp; ring]
    simp

def mU : Formalism.REAL.UJ e2 :=
  ⟨⟨!![5 / 4, 3 / 4; 3 / 4, 5 / 4], !![5 / 4, -3 / 4; -3 / 4, 5 / 4],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num,
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num⟩, by
    change Formalism.REAL.inUJ e2 !![5 / 4, 3 / 4; 3 / 4, 5 / 4]
    unfold Formalism.REAL.inUJ
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.REAL.Jm, e2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.conjTranspose_apply,
        map_ofNat] <;> norm_num⟩

theorem mU_act (a : ℂ) : uMat mU *ᵥ (a • ![1, 1]) = (2 * a) • ![1, 1] := by
  change !![5 / 4, 3 / 4; 3 / 4, 5 / 4] *ᵥ (a • ![1, 1]) = _
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem mU_herm : (uMat mU)ᴴ = uMat mU := by
  change (!![5 / 4, 3 / 4; 3 / 4, 5 / 4] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = !![5 / 4, 3 / 4; 3 / 4, 5 / 4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, map_ofNat]

theorem mU_mem : mU ∈ flagM e2 W2 := by
  intro i y hy
  rw [mU_herm, and_self]
  fin_cases i
  · change y ∈ (⊥ : Submodule ℂ (Fin 2 → ℂ)) at hy
    rw [Submodule.mem_bot] at hy
    subst hy
    simp
  · change y ∈ Submodule.span ℂ {![1, 1]} at hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [mU_act]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem locSize_mU : locSize ![1] W2 (uMat mU) 0 = 1 / 2 := by
  have hne : (![1, 1] : Fin 2 → ℂ) ≠ 0 := by
    intro h; simpa using congrFun h 0
  have h0 : detOn (uMat mU) ⊥ = 1 := by
    unfold detOn
    rw [dif_pos (by intro y hy; rw [Submodule.mem_bot] at hy; subst hy; simp)]
    rw [LinearMap.det_eq_one_of_subsingleton]; simp
  have h1 : detOn (uMat mU) (Submodule.span ℂ {![1, 1]}) = 2 := by
    have hs : ∀ y ∈ Submodule.span ℂ {(![1, 1] : Fin 2 → ℂ)},
        Matrix.toLin' (uMat mU) y ∈ Submodule.span ℂ {(![1, 1] : Fin 2 → ℂ)} := fun y hy =>
      (mU_mem 1 y hy).1
    unfold detOn
    rw [dif_pos hs]
    have : (Matrix.toLin' (uMat mU)).restrict hs = (2 : ℂ) • LinearMap.id := by
      ext ⟨y, hy⟩ : 1
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      apply Subtype.ext
      change uMat mU *ᵥ (a • ![1, 1]) = (2 : ℂ) • a • ![1, 1]
      rw [mU_act, mul_smul]
    rw [this, LinearMap.det_smul, finrank_span_singleton hne]
    simp
  change (detOn (uMat mU) (Submodule.span ℂ {![1, 1]}) / detOn (uMat mU) ⊥) ^ (-(1 : ℝ) / ((1 : ℕ) : ℝ)) = 1 / 2
  rw [h0, h1]
  norm_num [Real.rpow_neg_one]

end GlobalTheory.FlagMeas.Model
