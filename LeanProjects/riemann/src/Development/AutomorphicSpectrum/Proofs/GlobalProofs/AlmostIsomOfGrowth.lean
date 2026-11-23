import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.NormExpSubOneSubLe
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.HsInnerSelfEqSumSq
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Growth

open MeasureTheory GroundTheory.Heights₂.Theta.SecondKind

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def avgForm (μ : Measure G) (φ : G → ℝ) (ρ : G → (H →L[ℂ] H)) (x y : H) : ℂ :=
  ∫ g, (φ g : ℂ) * ⟪ρ g x, ρ g y⟫_ℂ ∂μ

variable {μ : Measure G} {φ B : G → ℝ} {ρ : G → (H →L[ℂ] H)}

theorem avg_smul (c : ℂ) (x y : H) : avgForm μ φ ρ x (c • y) = c * avgForm μ φ ρ x y := by
  simp only [avgForm, map_smul, inner_smul_right]
  rw [← integral_const_mul]
  congr 1
  funext g
  ring

theorem avg_conj (x y : H) : avgForm μ φ ρ y x = star (avgForm μ φ ρ x y) := by
  show _ = (starRingEnd ℂ) _
  simp only [avgForm]
  rw [← integral_conj]
  congr 1
  funext g
  rw [map_mul, Complex.conj_ofReal, inner_conj_symm]

theorem avg_self (x : H) : avgForm μ φ ρ x x = ((∫ g, φ g * ‖ρ g x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [avgForm, ← integral_complex_ofReal]
  congr 1
  funext g
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

variable (hφ : Continuous φ) (hφ0 : ∀ g, 0 < φ g) (hρ : ∀ v, Continuous fun g => ρ g v)
  (hB : Integrable B μ) (hb : ∀ g x y, φ g * (‖ρ g x‖ * ‖ρ g y‖) ≤ B g * (‖x‖ * ‖y‖))

include hφ hφ0 hρ hB hb

theorem integrable_avg (x y : H) : Integrable (fun g => (φ g : ℂ) * ⟪ρ g x, ρ g y⟫_ℂ) μ := by
  refine (hB.mul_const (‖x‖ * ‖y‖)).mono' ?_ (.of_forall fun g => ?_)
  · exact ((Complex.continuous_ofReal.comp hφ).mul ((hρ x).inner (hρ y))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hφ0 g).le]
    exact (mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (hφ0 g).le).trans (hb g x y)

theorem integrable_sq (x : H) : Integrable (fun g => φ g * ‖ρ g x‖ ^ 2) μ := by
  refine (hB.mul_const (‖x‖ * ‖x‖)).mono' ?_ (.of_forall fun g => ?_)
  · exact (hφ.mul ((hρ x).norm.pow 2)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (hφ0 g).le (sq_nonneg _)), sq]
    exact hb g x x

theorem avg_add (x y z : H) :
    avgForm μ φ ρ x (y + z) = avgForm μ φ ρ x y + avgForm μ φ ρ x z := by
  simp only [avgForm, map_add, inner_add_right, mul_add]
  exact integral_add (integrable_avg hφ hφ0 hρ hB hb x y) (integrable_avg hφ hφ0 hρ hB hb x z)

theorem avg_norm_le (x y : H) : ‖avgForm μ φ ρ x y‖ ≤ (∫ g, B g ∂μ) * ‖x‖ * ‖y‖ := by
  have h := norm_integral_le_of_norm_le (μ := μ)
    (f := fun g => (φ g : ℂ) * ⟪ρ g x, ρ g y⟫_ℂ) (hB.mul_const (‖x‖ * ‖y‖)) (.of_forall fun g => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hφ0 g).le]
      exact (mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (hφ0 g).le).trans (hb g x y))
  rw [integral_mul_const] at h
  rw [mul_assoc]
  exact h

theorem avg_lower (hφI : Integrable φ μ) {S : Set G} (hS : MeasurableSet S) {D : ℝ} (hD : 0 < D)
    (hDS : ∀ g ∈ S, ∀ x, ‖x‖ ≤ D * ‖ρ g x‖) (x : H) :
    (∫ g in S, φ g ∂μ) / D ^ 2 * ‖x‖ ^ 2 ≤ (avgForm μ φ ρ x x).re := by
  have hI := integrable_sq hφ hφ0 hρ hB hb x
  rw [avg_self, Complex.ofReal_re]
  calc (∫ g in S, φ g ∂μ) / D ^ 2 * ‖x‖ ^ 2 = ∫ g in S, φ g * (‖x‖ ^ 2 / D ^ 2) ∂μ := by
        rw [integral_mul_const]; ring
    _ ≤ ∫ g in S, φ g * ‖ρ g x‖ ^ 2 ∂μ := by
        refine setIntegral_mono_on (hφI.integrableOn.mul_const _) hI.integrableOn hS fun g hg => ?_
        refine mul_le_mul_of_nonneg_left ?_ (hφ0 g).le
        rw [div_le_iff₀ (by positivity)]
        have := pow_le_pow_left₀ (norm_nonneg _) (hDS g hg x) 2
        rw [mul_pow] at this
        linarith
    _ ≤ ∫ g, φ g * ‖ρ g x‖ ^ 2 ∂μ :=
        setIntegral_le_integral hI (.of_forall fun g => mul_nonneg (hφ0 g).le (sq_nonneg _))

theorem avg_growth [MeasurableMul G] [μ.IsMulRightInvariant]
    (hmul : ∀ g g', ρ (g * g') = (ρ g).comp (ρ g')) (h : G) {c : ℝ}
    (hφc : ∀ g, φ (g * h⁻¹) ≤ c * φ g) (x : H) :
    (avgForm μ φ ρ (ρ h x) (ρ h x)).re ≤ c * (avgForm μ φ ρ x x).re := by
  have hI := integrable_sq hφ hφ0 hρ hB hb x
  rw [avg_self, avg_self, Complex.ofReal_re, Complex.ofReal_re]
  have e : ∫ g, φ g * ‖ρ g (ρ h x)‖ ^ 2 ∂μ = ∫ g, φ (g * h⁻¹) * ‖ρ g x‖ ^ 2 ∂μ := by
    refine Eq.trans (integral_congr_ae (.of_forall fun g => ?_))
      (integral_mul_right_eq_self (μ := μ) (fun g => φ (g * h⁻¹) * ‖ρ g x‖ ^ 2) h)
    simp [hmul]
  rw [e, ← integral_const_mul]
  refine integral_mono_of_nonneg (.of_forall fun g => mul_nonneg (hφ0 _).le (sq_nonneg _))
    (hI.const_mul c) (.of_forall fun g => ?_)
  show φ (g * h⁻¹) * ‖ρ g x‖ ^ 2 ≤ c * (φ g * ‖ρ g x‖ ^ 2)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hφc g) (sq_nonneg _)

end Abstract

section Mat

variable {n : ℕ}

theorem wt_eq_hs_sq (g : Matrix (Fin n) (Fin n) ℂ) : wt g = UnitaryRecombination.hs g ^ 2 := by
  rw [← UnitaryRecombination.tInner_self, wt, UnitaryRecombination.tInner, trace_mul_comm]

theorem hs_le_mnorm (X : Matrix (Fin n) (Fin n) ℂ) : UnitaryRecombination.hs X ≤ mnorm X := by
  have hm : 0 ≤ mnorm X := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hij : ∀ i j, ‖X i j‖ ≤ mnorm X := fun i j =>
    (Finset.single_le_sum (f := fun b => ‖X i b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, ‖X a b‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  refine (sq_le_sq₀ (UnitaryRecombination.hs_nonneg X) hm).1 ?_
  rw [UnitaryRecombination.hs_sq]
  calc ∑ i, ∑ j, ‖X i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖X i j‖ * mnorm X :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [sq]; exact mul_le_mul_of_nonneg_left (hij i j) (norm_nonneg _)
    _ = mnorm X ^ 2 := by
        simp only [← Finset.sum_mul]
        rw [sq]; rfl

theorem continuous_wt : Continuous (wt : Matrix (Fin n) (Fin n) ℂ → ℝ) :=
  Complex.continuous_re.comp ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id).matrix_trace)

theorem wt_one : wt (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  simp [wt]

section L2

open scoped Matrix.Norms.L2Operator

theorem wt_mul_le (A h : Matrix (Fin n) (Fin n) ℂ) : wt (A * h) ≤ wt A * ‖h‖ ^ 2 := by
  rw [wt_eq_hs_sq, wt_eq_hs_sq, ← mul_pow]
  exact pow_le_pow_left₀ (UnitaryRecombination.hs_nonneg _) (UnitaryRecombination.hs_mul_right_le A h) 2

theorem norm_exp_smul_le (hn : 0 < n) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    ‖NormedSpace.exp (t • X)‖ ≤ Real.exp (|t| * mnorm X) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : NormOneClass (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨by rw [← l2_opNorm_toEuclideanCLM, map_one]; exact norm_one⟩
  refine (PI.IwaMeasEx.Gauge.ZetaZeros.norm_exp_le' _).trans (Real.exp_le_exp.2 ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((UnitaryRecombination.opNorm_le_hs X).trans (hs_le_mnorm X)) (abs_nonneg _)

end L2

theorem wt_mul_exp_le (hn : 0 < n) (A X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    wt (A * NormedSpace.exp (t • X)) ≤ wt A * Real.exp (2 * (|t| * mnorm X)) := by
  open scoped Matrix.Norms.L2Operator in
  refine (wt_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · rw [two_mul, Real.exp_add, ← sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_exp_smul_le hn X t) 2
  · rw [wt_eq_hs_sq]; positivity

theorem wt_pos {ε : Fin n → Bool} (hn : 0 < n) (g : UJ ε) : 0 < wt (uMat g) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hne : uMat g ≠ 0 := Units.ne_zero (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  obtain ⟨i, j, hij⟩ : ∃ i j, uMat g i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Matrix.ext h)
  rw [wt_eq_hs_sq, UnitaryRecombination.hs_sq]
  have h1 : 0 < ‖uMat g i j‖ ^ 2 := by positivity
  have h2 := Finset.single_le_sum (f := fun b => ‖uMat g i b‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ j)
  have h3 := Finset.single_le_sum (f := fun a => ∑ b, ‖uMat g a b‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact h1.trans_le (h2.trans h3)

theorem exists_uMat_eq {ε : Fin n → Bool} {c : Matrix (Fin n) (Fin n) ℂ} (hc : c ∈ UJset ε) :
    ∃ h : UJ ε, uMat h = c := by
  have hc' : cᴴ * Jm ε * c = Jm ε := hc
  have hl : (Jm ε * cᴴ * Jm ε) * c = 1 := by
    rw [mul_assoc (Jm ε * cᴴ), mul_assoc (Jm ε), ← mul_assoc cᴴ, hc', Jm_mul_self]
  exact ⟨⟨⟨c, Jm ε * cᴴ * Jm ε, mul_eq_one_comm.1 hl, hl⟩, hc⟩, rfl⟩

theorem continuous_uMat {ε : Fin n → Bool} : Continuous (uMat : UJ ε → Matrix (Fin n) (Fin n) ℂ) :=
  Units.continuous_val.comp continuous_subtype_val

end Mat

theorem almostIsom_of_growth {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε))
    (hg : ∃ C b : ℝ, 0 < C ∧ 0 ≤ b ∧ ∀ g ∈ UJset ε, ∀ x, ‖π g x‖ ≤ C * wt g ^ b * ‖x‖)
    (hv : ∃ b : ℝ, 0 ≤ b ∧ ∀ b' : ℝ, b ≤ b' →
      MeasureTheory.Integrable (fun g : UJ ε => wt (uMat g) ^ (-b')) (Formalism.REAL.muG ε).inv) :
    AlmostIsom (UJset ε) π := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun x y => ⟪x, y⟫_ℂ, 1, 1, 0, one_pos, zero_le_one, le_rfl,
      fun x y z => inner_add_right _ _ _, fun c x y => inner_smul_right _ _ _,
      fun x y => (inner_conj_symm y x).symm, fun x => ?_, fun x y => ?_, fun X _ t x => ?_⟩
    · rw [one_mul]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) x).ge
    · rw [one_mul]
      exact norm_inner_le_norm _ _
    · have h1 : NormedSpace.exp (t • X) = 1 := Subsingleton.elim _ _
      rw [h1, hrep.1]
      simp
  obtain ⟨C, b, hC, hb, hgr⟩ := hg
  obtain ⟨b0, hb0, hint⟩ := hv
  have hw : Continuous fun g : UJ ε => wt (uMat g) := continuous_wt.comp continuous_uMat
  have hwp : ∀ g : UJ ε, 0 < wt (uMat g) := wt_pos hn
  obtain ⟨b', hb'⟩ : ∃ b' : ℝ, b' = b0 + 2 * b := ⟨_, rfl⟩
  have hb'0 : 0 ≤ b' := by rw [hb']; positivity
  have hb0' : b0 ≤ b' := by rw [hb']; linarith
  let φ : UJ ε → ℝ := fun g => wt (uMat g) ^ (-b')
  let Bf : UJ ε → ℝ := fun g => C ^ 2 * wt (uMat g) ^ (-b0)
  let ρ : UJ ε → (H →L[ℂ] H) := fun g => π (uMat g)
  have hφ : Continuous φ := hw.rpow_const fun g => Or.inl (hwp g).ne'
  have hφ0 : ∀ g, 0 < φ g := fun g => Real.rpow_pos_of_pos (hwp g) _
  have hρ : ∀ v, Continuous fun g => ρ g v := fun v =>
    (hc v).comp_continuous continuous_uMat fun g => g.2
  have hB : MeasureTheory.Integrable Bf (Formalism.REAL.muG ε).inv := (hint b0 le_rfl).const_mul _
  have hφI : MeasureTheory.Integrable φ (Formalism.REAL.muG ε).inv := hint b' hb0'
  have hbd : ∀ g x y, φ g * (‖ρ g x‖ * ‖ρ g y‖) ≤ Bf g * (‖x‖ * ‖y‖) := by
    intro g x y
    have hwb : 0 ≤ wt (uMat g) ^ b := (Real.rpow_pos_of_pos (hwp g) _).le
    have h1 := hgr _ g.2 x
    have h2 := hgr _ g.2 y
    have e : φ g * (wt (uMat g) ^ b * wt (uMat g) ^ b) = wt (uMat g) ^ (-b0) := by
      simp only [φ]
      rw [← Real.rpow_add (hwp g), ← Real.rpow_add (hwp g), hb']
      congr 1
      ring
    calc φ g * (‖ρ g x‖ * ‖ρ g y‖)
        ≤ φ g * ((C * wt (uMat g) ^ b * ‖x‖) * (C * wt (uMat g) ^ b * ‖y‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (hφ0 g).le
      _ = C ^ 2 * (φ g * (wt (uMat g) ^ b * wt (uMat g) ^ b)) * (‖x‖ * ‖y‖) := by ring
      _ = Bf g * (‖x‖ * ‖y‖) := by rw [e]

  let S : Set (UJ ε) := {g | wt (uMat g) < n + 1} ∩ {g | wt (uMat g⁻¹) < n + 1}
  have hSo : IsOpen S := (isOpen_lt hw continuous_const).inter
    (isOpen_lt (hw.comp continuous_inv) continuous_const)
  have hS1 : (1 : UJ ε) ∈ S := by
    have h1 : wt (uMat (1 : UJ ε)) = n := wt_one
    refine ⟨?_, ?_⟩
    · show wt (uMat (1 : UJ ε)) < n + 1
      linarith
    · show wt (uMat (1 : UJ ε)⁻¹) < n + 1
      rw [inv_one]
      linarith
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = C * ((n : ℝ) + 1) ^ b := ⟨_, rfl⟩
  have hD : 0 < D := by rw [hDdef]; positivity
  have hDS : ∀ g ∈ S, ∀ x, ‖x‖ ≤ D * ‖ρ g x‖ := by
    intro g hgS x
    have e : π (uMat g⁻¹) (π (uMat g) x) = x := by
      have h1 : π (uMat g⁻¹ * uMat g) = (π (uMat g⁻¹)).comp (π (uMat g)) :=
        hrep.2 _ (g⁻¹).2 _ g.2
      have h2 : uMat g⁻¹ * uMat g = 1 := by
        show uMat (g⁻¹ * g) = 1
        rw [inv_mul_cancel]
        rfl
      rw [h2, hrep.1] at h1
      exact (DFunLike.congr_fun h1 x).symm
    have h3 := hgr _ (g⁻¹).2 (π (uMat g) x)
    rw [e] at h3
    refine h3.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [hDdef]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hwp _).le (le_of_lt hgS.2) hb) hC.le
  have hmS : 0 < ∫ g in S, φ g ∂(Formalism.REAL.muG ε).inv := by
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      (.of_forall fun g => (hφ0 g).le) hφI.integrableOn]
    have hsupp : Function.support φ = Set.univ :=
      Set.eq_univ_of_forall fun g => (hφ0 g).ne'
    rw [hsupp, Set.univ_inter]
    exact hSo.measure_pos _ ⟨1, hS1⟩
  refine ⟨avgForm (Formalism.REAL.muG ε).inv φ ρ, (∫ g in S, φ g ∂(Formalism.REAL.muG ε).inv) / D ^ 2,
    ∫ g, Bf g ∂(Formalism.REAL.muG ε).inv, 2 * b', by positivity,
    MeasureTheory.integral_nonneg fun g => mul_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos (hwp g) _).le,
    by positivity, avg_add hφ hφ0 hρ hB hbd, avg_smul, avg_conj,
    avg_lower hφ hφ0 hρ hB hbd hφI hSo.measurableSet hD hDS, avg_norm_le hφ hφ0 hρ hB hbd, ?_⟩
  intro X hX t x
  obtain ⟨h, hh⟩ := exists_uMat_eq (hX t)
  have hmul : ∀ g g', ρ (g * g') = (ρ g).comp (ρ g') := fun g g' => hrep.2 _ g.2 _ g'.2
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = 2 * (|t| * mnorm X) := ⟨_, rfl⟩
  have hφc : ∀ g, φ (g * h⁻¹) ≤ Real.exp (b' * l) * φ g := by
    intro g
    have h1 : wt (uMat g) ≤ wt (uMat (g * h⁻¹)) * Real.exp l := by
      have h2 := wt_mul_exp_le hn (uMat (g * h⁻¹)) X t
      rw [← hh, ← hl] at h2
      have h3 : uMat (g * h⁻¹) * uMat h = uMat g := by
        show uMat (g * h⁻¹ * h) = uMat g
        rw [inv_mul_cancel_right]
      rwa [h3] at h2
    have h4 : wt (uMat g) * Real.exp (-l) ≤ wt (uMat (g * h⁻¹)) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      exact h1
    have h5 : 0 < wt (uMat g) * Real.exp (-l) := mul_pos (hwp g) (Real.exp_pos _)
    calc φ (g * h⁻¹) ≤ (wt (uMat g) * Real.exp (-l)) ^ (-b') :=
          Real.rpow_le_rpow_of_nonpos h5 h4 (by linarith)
      _ = Real.exp (b' * l) * φ g := by
          rw [Real.mul_rpow (hwp g).le (Real.exp_pos _).le, ← Real.exp_mul, mul_comm]
          congr 2
          ring
  have key := avg_growth (μ := (Formalism.REAL.muG ε).inv) hφ hφ0 hρ hB hbd hmul h hφc x
  have e : ρ h = π (NormedSpace.exp (t • X)) := by
    simp only [ρ]
    rw [hh]
  rw [e] at key
  refine key.trans (le_of_eq ?_)
  congr 2
  rw [hl]
  ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Growth

end
