import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def flatAtlas (D : ℕ) : FinHolAtlas D (Fin D → ℂ) where
  n := 1
  chart _ := OpenPartialHomeomorph.refl _
  cover _ := ⟨0, by simp⟩
  holo _ _ := by
    intro x _
    simpa [Function.comp_def] using analyticAt_id

instance (D : ℕ) : Subsingleton (Fin (flatAtlas D).n) := inferInstanceAs (Subsingleton (Fin 1))

@[simp] theorem flatAtlas_chart (D : ℕ) (j : Fin (flatAtlas D).n) :
    (flatAtlas D).chart j = OpenPartialHomeomorph.refl _ := rfl

def trivLB {D : ℕ} {U : Type} [TopologicalSpace U] (A : FinHolAtlas D U) : HolLineBundle A where
  g _ _ _ := 1
  holo _ _ := fun _ => by simpa [Function.comp_def] using analyticOnNhd_const
  ne_zero _ _ _ _ := one_ne_zero
  cocycle _ _ _ _ _ := by simp

theorem jac_flat {D : ℕ} (j k : Fin (flatAtlas D).n) (x : Fin D → ℂ) : jac (flatAtlas D) j k x = 1 := by
  have h : ((flatAtlas D).chart k ∘ ((flatAtlas D).chart j).symm) = id := by
    funext y; simp
  simp only [jac, h, fderiv_id]
  exact LinearMap.det_id

theorem mul_mem_topSections {D : ℕ} {U : Type} [TopologicalSpace U] {A : FinHolAtlas D U}
    {L₂ L : HolLineBundle A} {m : ℕ} {w F : Fin A.n → U → ℂ} (hw : w ∈ L.sections 1)
    (hF : F ∈ topSections A L₂ L m) : w * F ∈ topSections A L₂ L (m + 1) := by
  obtain ⟨hwh, hwc, hwz⟩ := hw
  obtain ⟨hFh, hFc, hFz⟩ := hF
  refine ⟨fun j k => ?_, fun j k x hx => ?_, fun j x hx => ?_⟩
  · exact (hwh j k).mul (hFh j k)
  · simp only [Pi.mul_apply, hwc j k x hx, hFc j k x hx]; ring
  · simp [hwz j x hx]

theorem isAlgCover_flat (D : ℕ) : IsAlgCover (flatAtlas D) := by
  refine ⟨univ, id, 1, isOpen_univ, one_ne_zero, fun i => ?_, fun x _ => by simp, ?_, ?_,
    fun j => ⟨fun _ => 1, analyticOnNhd_const, by simp, fun y _ h => absurd (mem_univ _) h⟩⟩
  · intro j x _
    simp only [Function.comp_def, flatAtlas_chart, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, id_eq]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt x
  · have hh : (fun p : (univ : Set (Fin D → ℂ)) => id (p : Fin D → ℂ)) =
        ⇑(Homeomorph.Set.univ (Fin D → ℂ)) := rfl
    rw [hh]
    refine IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
      (Homeomorph.Set.univ (Fin D → ℂ)).isClosedMap (fun y _ => ?_)
      (Homeomorph.Set.univ (Fin D → ℂ)).isLocalHomeomorph.isLocalHomeomorphOn
    exact (Set.finite_singleton y).preimage (Homeomorph.Set.univ (Fin D → ℂ)).injective.injOn
  · intro y _
    exact (Set.finite_singleton y).preimage fun a _ b _ h => Subtype.ext h

theorem mem_sections_flat {D : ℕ} (f : (Fin D → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ) :
    (fun _ => f : Fin (flatAtlas D).n → (Fin D → ℂ) → ℂ) ∈ (trivLB (flatAtlas D)).sections 1 := by
  refine ⟨fun j k => ?_, fun j k x _ => by simp [trivLB], fun j x hx => absurd ?_ hx⟩
  · intro y _
    simpa [Function.comp_def] using hf y (mem_univ _)
  · simp

theorem mem_topSections_flat {D : ℕ} (m : ℕ) (f : (Fin D → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f univ) :
    (fun _ => f : Fin (flatAtlas D).n → (Fin D → ℂ) → ℂ) ∈
      topSections (flatAtlas D) (trivLB (flatAtlas D)) (trivLB (flatAtlas D)) m := by
  refine ⟨fun j k => ?_, fun j k x _ => by simp [trivLB, jac_flat], fun j x hx => absurd ?_ hx⟩
  · intro y _
    simpa [Function.comp_def] using hf y (mem_univ _)
  · simp

def exE : Fin 2 → Fin (flatAtlas 1).n → (Fin 1 → ℂ) → ℂ := ![fun _ _ => 1, fun _ x => x 0]

def exE₂ : Fin 1 → Fin (flatAtlas 1).n → (Fin 1 → ℂ) → ℂ := fun _ _ _ => 1

abbrev exEmb : EmbDatum 1 where
  U := Fin 1 → ℂ
  A := flatAtlas 1
  cover := isAlgCover_flat 1
  L := trivLB _
  L₂ := trivLB _
  N := 2
  N₂ := 1
  e := exE
  e₂ := exE₂
  e_mem i := by
    fin_cases i
    · exact mem_sections_flat (fun _ => 1) analyticOnNhd_const
    · exact mem_sections_flat (fun x => x 0) fun x _ =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt x
  e₂_mem _ := mem_sections_flat (fun _ => 1) analyticOnNhd_const
  gen _ := ⟨0, by simp [exE]⟩
  gen₂ _ := ⟨0, by simp [exE₂]⟩

def exC : Fin 1 → Fin 2 → ℂ := fun _ => ![0, 1]

theorem exS_apply (i : Fin 1) (j : Fin (flatAtlas 1).n) (x : Fin 1 → ℂ) :
    lin exE (exC i) j x = x 0 := by
  simp [lin, exE, exC, Fin.sum_univ_two]

theorem exZero : zeroSet (flatAtlas 1) (fun i => lin exE (exC i)) = {0} := by
  ext x
  simp only [zeroSet, exS_apply, Set.mem_ofPred_eq, mem_singleton_iff]
  constructor
  · intro h; funext i; rw [Subsingleton.elim i 0]; exact h 0
  · intro h _; simp [h]

theorem exSMap (j : Fin (flatAtlas 1).n) :
    (fun (z : Fin 1 → ℂ) (i : Fin 1) => lin exE (exC i) j (((flatAtlas 1).chart j).symm z)) = id := by
  funext z i
  rw [exS_apply, Subsingleton.elim i 0]
  simp

abbrev exZ : ZeroDatum exEmb where
  c := exC
  finite := by
    change (zeroSet (flatAtlas 1) fun i => lin exE (exC i)).Finite
    rw [exZero]; exact finite_singleton 0
  nondeg := by
    change IsNondeg (flatAtlas 1) fun i => lin exE (exC i)
    intro x _
    simp only [sJac, sJacMap, exSMap, fderiv_id]
    rw [ContinuousLinearMap.coe_id, LinearMap.det_id]
    exact one_ne_zero
  fl := by
    change FLBound (flatAtlas 1) exE fun i => lin exE (exC i)
    intro V hV hS
    rw [exZero, singleton_subset_iff] at hS
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 0 hS
    refine ⟨1 + 1 / ε ^ 2, fun x hx => ?_⟩
    have hx' : ε ≤ ‖x 0‖ := by
      by_contra hlt'
      have hlt := not_le.mp hlt'
      apply hx
      apply hball
      rw [Metric.mem_ball, dist_zero_right]
      refine lt_of_le_of_lt ?_ hlt
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
      rw [Subsingleton.elim i 0]
    have hs : ∑ i : Fin 1, ‖lin exE (exC i) (chartIdx (flatAtlas 1) x) x‖ ^ 2 = ‖x 0‖ ^ 2 := by
      simp [exS_apply]
    have he : ∑ k : Fin 2, ‖exE k (chartIdx (flatAtlas 1) x) x‖ ^ 2 = 1 + ‖x 0‖ ^ 2 := by
      simp [exE, Fin.sum_univ_two]
    beta_reduce
    rw [hs, he]
    have hε2 : 0 < ε ^ 2 := by positivity
    have h1 : ε ^ 2 ≤ ‖x 0‖ ^ 2 := by gcongr
    rw [add_mul, one_mul, div_mul_eq_mul_div, one_mul]
    have : 1 ≤ ‖x 0‖ ^ 2 / ε ^ 2 := by rw [le_div_iff₀ hε2]; linarith
    linarith

theorem exp_neg_sq_le (t : ℝ) (ht : 0 ≤ t) : Real.exp (-t ^ 2) ≤ 16 * ((1 + t) ^ 3)⁻¹ := by
  have h1 : 1 + t ^ 2 + (t ^ 2) ^ 2 / 2 ≤ Real.exp (t ^ 2) :=
    Real.quadratic_le_exp_of_nonneg (sq_nonneg t)
  have h4 : (t ^ 2) ^ 2 = t ^ 4 := by ring
  have h2 : (1 + t) ^ 3 ≤ 8 * (1 + t ^ 4) := by
    nlinarith [sq_nonneg (t - 1), sq_nonneg (t ^ 2 - 1), sq_nonneg t, mul_nonneg ht (sq_nonneg (t - 1)),
      mul_nonneg ht (sq_nonneg t), mul_nonneg (mul_nonneg ht ht) (sq_nonneg (t - 1))]
  have h3 : (1 + t) ^ 3 ≤ Real.exp (t ^ 2) * 16 := by nlinarith [sq_nonneg t]
  have hpos : 0 < (1 + t) ^ 3 := by positivity
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos, inv_mul_le_iff₀ (Real.exp_pos _)]
  exact h3

theorem lintegral_gaussian_complex_line_lt_top (c : ℝ) : ∫⁻ y : Fin 1 → ℂ, ENNReal.ofReal (c * Real.exp (-‖y 0‖ ^ 2)) < ⊤ := by
  have hfin : (Module.finrank ℝ (Fin 1 → ℂ) : ℝ) < 3 := by
    rw [Module.finrank_pi_fintype]; simp; norm_num
  have hI := finite_integral_one_add_norm (E := Fin 1 → ℂ) (μ := volume) hfin
  have hpt : ∀ y : Fin 1 → ℂ, ENNReal.ofReal (c * Real.exp (-‖y 0‖ ^ 2)) ≤
      ENNReal.ofReal (16 * |c|) * ENNReal.ofReal ((1 + ‖y‖) ^ (-(3 : ℝ))) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hy : ‖y‖ ≤ ‖y 0‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
      rw [Subsingleton.elim i 0]
    have hr : (1 + ‖y‖) ^ (-(3 : ℝ)) = ((1 + ‖y‖) ^ 3)⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      norm_cast
    rw [hr]
    have he := exp_neg_sq_le ‖y 0‖ (norm_nonneg _)
    have hmono : ((1 + ‖y 0‖) ^ 3)⁻¹ ≤ ((1 + ‖y‖) ^ 3)⁻¹ := by
      apply inv_anti₀ (by positivity)
      gcongr
    calc c * Real.exp (-‖y 0‖ ^ 2) ≤ |c| * Real.exp (-‖y 0‖ ^ 2) := by
          gcongr; exact le_abs_self c
      _ ≤ |c| * (16 * ((1 + ‖y 0‖) ^ 3)⁻¹) := by gcongr
      _ ≤ |c| * (16 * ((1 + ‖y‖) ^ 3)⁻¹) := by gcongr
      _ = 16 * |c| * ((1 + ‖y‖) ^ 3)⁻¹ := by ring
  calc ∫⁻ y : Fin 1 → ℂ, ENNReal.ofReal (c * Real.exp (-‖y 0‖ ^ 2))
      ≤ ∫⁻ y : Fin 1 → ℂ, ENNReal.ofReal (16 * |c|) * ENNReal.ofReal ((1 + ‖y‖) ^ (-(3 : ℝ))) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (16 * |c|) * ∫⁻ y : Fin 1 → ℂ, ENNReal.ofReal ((1 + ‖y‖) ^ (-(3 : ℝ))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI

theorem contDiff_normSq0 :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin 1 → ℂ => ‖x 0‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0).contDiff

def exPhiA : TwistWeight exEmb.A exEmb.L₂ exEmb.L 1 where
  φ _ x := ‖x 0‖ ^ 2
  smooth _ k := by
    exact contDiff_normSq0.contDiffOn
  compat _ _ _ _ := by simp [exEmb, trivLB]
  psh j y _ w := by
    have h := (ReciprocityTheory.AnForm.A.isPshInhabit_thm 1).2.2.1.2 y (mem_univ y) w
    have he : ((fun x : Fin 1 → ℂ => ‖x 0‖ ^ 2) ∘ ((flatAtlas 1).chart j).symm) =
        fun z : Fin 1 → ℂ => ∑ i, ‖z i‖ ^ 2 := by
      funext z; simp only [Function.comp_apply, Fin.sum_univ_one]; rfl
    change 0 ≤ levi ((fun x : Fin 1 → ℂ => ‖x 0‖ ^ 2) ∘ ((flatAtlas 1).chart j).symm) y w
    rw [he]; exact h

def exOne : Fin (flatAtlas 1).n → (Fin 1 → ℂ) → ℂ := fun _ _ => 1

def exV (j : ℕ) : Submodule ℂ (Fin (flatAtlas 1).n → (Fin 1 → ℂ) → ℂ) :=
  if j = 0 then Submodule.span ℂ {exOne}
  else topSections (flatAtlas 1) (trivLB _) (trivLB _) (1 + j)

theorem exV_le (j : ℕ) : exV j ≤ topSections (flatAtlas 1) (trivLB _) (trivLB _) (1 + j) := by
  unfold exV
  split_ifs with h
  · subst h
    rw [Submodule.span_le, singleton_subset_iff]
    exact mem_topSections_flat _ (fun _ => 1) analyticOnNhd_const
  · exact le_rfl

theorem mem_natural_sections_of_degree_zero (F : Fin (flatAtlas 1).n → (Fin 1 → ℂ) → ℂ) (hF : F ∈ exV 0) :
    F ∈ Vnat (flatAtlas 1) (trivLB _) (trivLB _) (fun _ x => ‖x 0‖ ^ 2) (fsWeight exE) 0 := by
  have hmem := exV_le 0 hF
  have hF' : F ∈ Submodule.span ℂ {exOne} := by simpa [exV] using hF
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hF'
  refine ⟨hmem, ?_⟩
  simp only [topNormSq, chartIntegral]
  refine ENNReal.sum_lt_top.mpr fun j _ => ?_
  refine lt_of_le_of_lt (setLIntegral_le_lintegral _ _) ?_
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) (lintegral_gaussian_complex_line_lt_top (2 * ‖c‖ ^ 2))
  simp [exOne]

theorem exSJac (c : Fin (flatAtlas 1).n) (x : Fin 1 → ℂ) :
    sJac (flatAtlas 1) (fun i => lin exE (exC i)) c x = 1 := by
  simp only [sJac, sJacMap, exSMap, fderiv_id]
  rw [ContinuousLinearMap.coe_id, LinearMap.det_id]

abbrev exSpace : SpaceDatum exEmb 2 where
  β := 1
  one_le_β := le_rfl
  φA := exPhiA
  φA_le j x _ := by
    change Real.exp (-‖x 0‖ ^ 2) ≤ 1 ^ (1 + 1) * Real.exp (-(fsWeight exE₂ j x + ((1 : ℕ) : ℝ) * fsWeight exE j x))
    have hw : fsWeight exE₂ j x + ((1 : ℕ) : ℝ) * fsWeight exE j x = Real.log (1 + ‖x 0‖ ^ 2) := by
      simp [fsWeight, exE, exE₂, Fin.sum_univ_two]
    rw [hw, one_pow, one_mul, Real.exp_neg (Real.log _), Real.exp_log (by positivity), Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (‖x 0‖ ^ 2)])
  V := exV
  V_le := exV_le
  normT F := Real.sqrt (topNormSq (flatAtlas 1) (exEmb.wt (1 + 2)) F).toReal
  sections_zero_mem_natural := mem_natural_sections_of_degree_zero
  sections_top_mem_natural F hF := by
    show F ∈ exV 1
    simp only [exV, one_ne_zero, ↓reduceIte]
    exact hF.1
  H1 j _ i F hF := by
    have h := mul_mem_topSections (exEmb.e_mem i) (exV_le j hF)
    show exE i * F ∈ exV (j + 1)
    simp only [exV, Nat.succ_ne_zero, ↓reduceIte]
    exact h
  H2 F _ := by
    rw [Real.sq_sqrt ENNReal.toReal_nonneg, one_pow, ENNReal.ofReal_one, one_mul]
    exact ENNReal.ofReal_toReal_le

theorem exResOnto : ResOnto exZ exSpace := by
  intro g
  refine ⟨g 0 • exOne, ?_, fun x hx => ?_⟩
  · show g 0 • exOne ∈ exV 0
    simp only [exV, ↓reduceIte]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · have hx' : x ∈ zeroSet (flatAtlas 1) (fun i => lin exE (exC i)) := hx
    rw [exZero, mem_singleton_iff] at hx'
    subst hx'
    show (g 0 • exOne) _ 0 / sJac (flatAtlas 1) (fun i => lin exE (exC i)) _ 0 = g 0
    rw [exSJac]
    simp [exOne]

theorem inhabited_at_embedding :
    ∃ (X : EmbDatum 1) (Z : ZeroDatum X) (Y : SpaceDatum X 2), ResOnto Z Y ∧ Z.S.Nonempty :=
  ⟨exEmb, exZ, exSpace, exResOnto, ⟨0, by
    change (0 : Fin 1 → ℂ) ∈ zeroSet (flatAtlas 1) (fun i => lin exE (exC i))
    rw [exZero]; rfl⟩⟩

theorem hormander_hyp :
    IsAlgCover (flatAtlas 1) ∧
    (∀ j, (flatAtlas 1).SmoothOn ((flatAtlas 1).chart j).source (exPhiA.φ j)) ∧
    (∀ j k, ∀ x ∈ ((flatAtlas 1).chart j).source ∩ ((flatAtlas 1).chart k).source,
      exPhiA.φ j x = exPhiA.φ k x + Real.log (‖(trivLB (flatAtlas 1)).g j k x‖ ^ 2)) ∧
    (∀ j, ∀ y ∈ ((flatAtlas 1).chart j).target, ∀ w : Fin 1 → ℂ,
      0 ≤ levi (exPhiA.φ j ∘ ((flatAtlas 1).chart j).symm) y w) ∧
    (∀ j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (exOne j ∘ ((flatAtlas 1).chart j).symm)
      ((flatAtlas 1).chart j).target) ∧
    (∀ j k, ∀ x ∈ ((flatAtlas 1).chart j).source ∩ ((flatAtlas 1).chart k).source,
      exOne j x = jac (flatAtlas 1) j k x * (trivLB (flatAtlas 1)).g j k x * exOne k x) ∧
    (∀ j, ∀ x ∉ ((flatAtlas 1).chart j).source, exOne j x = 0) ∧
    (∀ j, ∀ y ∈ ((flatAtlas 1).chart j).target, ∀ ξ : Fin 1 → ℂ,
      ‖∑ l, dbarC (exOne j ∘ ((flatAtlas 1).chart j).symm) y l * starRingEnd ℂ (ξ l)‖ ^ 2 ≤
        (0 : ℝ) * levi (exPhiA.φ j ∘ ((flatAtlas 1).chart j).symm) y ξ) := by
  refine ⟨isAlgCover_flat 1, exPhiA.smooth, fun j k x _ => ?_, exPhiA.psh, fun j => ?_,
    fun j k x _ => by simp [exOne, jac_flat, trivLB], fun j x hx => absurd (by simp) hx,
    fun j y _ ξ => ?_⟩
  · simp [exPhiA, trivLB]
  · exact contDiffOn_const
  · have h1 : (exOne j ∘ ((flatAtlas 1).chart j).symm) = fun _ => (1 : ℂ) := rfl
    simp only [dbarC]
    rw [h1]
    simp

end

end GroundTheory.Heights₂.Heights.EffectiveHS
