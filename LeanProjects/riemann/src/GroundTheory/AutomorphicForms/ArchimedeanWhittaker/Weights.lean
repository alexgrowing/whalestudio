import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.FiltrationCocycleLiftCriterion

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral
open scoped Matrix.Norms.L2Operator Real InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

theorem continuous_kMat : Continuous kMat := by
  have : kMat = fun θ : ℝ => hGL2.expG (θ • lW) := funext fun θ => (expG_lW θ).symm
  rw [this]
  exact hGL2.continuous_expG.comp (continuous_id.smul continuous_const)

theorem kMat_add_two_pi (θ : ℝ) : kMat (θ + 2 * π) = kMat θ := by
  rw [kMat_add, kMat_two_pi, mul_one]

noncomputable def chi (j : ℤ) (θ : ℝ) : ℂ := Complex.exp ((j : ℂ) * θ * I)

theorem chi_add (j : ℤ) (a b : ℝ) : chi j (a + b) = chi j a * chi j b := by
  simp only [chi, ofReal_add, ← Complex.exp_add]; ring_nf

theorem chi_neg (j : ℤ) (a : ℝ) : chi j (-a) = (chi j a)⁻¹ := by
  simp only [chi, ofReal_neg, ← Complex.exp_neg]; ring_nf

theorem chi_mul_chi_neg (j : ℤ) (a : ℝ) : chi j a * chi j (-a) = 1 := by
  rw [chi_neg, mul_inv_cancel₀ (by simp [chi, Complex.exp_ne_zero])]

theorem chi_two_pi (j : ℤ) : chi j (2 * π) = 1 := by
  simp only [chi]
  have := Complex.exp_int_mul_two_pi_mul_I j
  rw [← this]; congr 1; push_cast; ring

theorem continuous_chi (j : ℤ) : Continuous (chi j) := by
  unfold chi; fun_prop

theorem norm_chi (j : ℤ) (a : ℝ) : ‖chi j a‖ = 1 := by
  rw [chi, Complex.norm_exp]
  simp

theorem conj_chi (j : ℤ) (a : ℝ) : (starRingEnd ℂ) (chi j a) = chi j (-a) := by
  rw [chi, chi, ← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

def weightSpace (j : ℤ) : Submodule ℂ H where
  carrier := {v | ∀ θ : ℝ, σ (kMat θ) v = chi j θ • v}
  add_mem' {v w} hv hw θ := by simp [map_add, hv θ, hw θ, smul_add]
  zero_mem' θ := by simp
  smul_mem' c v hv θ := by simp [hv θ, smul_comm c]

theorem mem_weightSpace {j : ℤ} {v : H} :
    v ∈ weightSpace σ j ↔ ∀ θ : ℝ, σ (kMat θ) v = chi j θ • v := Iff.rfl

theorem isClosed_weightSpace (j : ℤ) : IsClosed (weightSpace σ j : Set H) := by
  have : (weightSpace σ j : Set H) = ⋂ θ : ℝ, {v | σ (kMat θ) v = chi j θ • v} := by
    ext v; simp [mem_weightSpace]
  rw [this]
  exact isClosed_iInter fun θ => isClosed_eq (σ (kMat θ)).continuous (continuous_const_smul _)

noncomputable def wProj (j : ℤ) (x : H) : H :=
  ((2 * π : ℝ)⁻¹ : ℂ) • ∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x

theorem continuous_orbit_kMat (x : H) : Continuous fun θ : ℝ => σ (kMat θ) x :=
  (σ.continuous_orbit x).comp continuous_kMat

theorem continuous_wIntegrand (j : ℤ) (x : H) :
    Continuous fun θ : ℝ => chi j (-θ) • σ (kMat θ) x :=
  ((continuous_chi j).comp continuous_neg).smul (continuous_orbit_kMat σ x)

theorem wProj_mem (j : ℤ) (x : H) : wProj σ j x ∈ weightSpace σ j := by
  intro φ
  have hper : Function.Periodic (fun θ : ℝ => chi j (-θ) • σ (kMat θ) x) (2 * π) := by
    intro θ
    simp only [kMat_add_two_pi, neg_add, chi_add, chi_neg j (2 * π), chi_two_pi, inv_one, mul_one]
  have hint := (continuous_wIntegrand σ j x).intervalIntegrable (μ := volume) 0 (2 * π)
  have h1 : σ (kMat φ) (∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x) =
      ∫ θ in (0 : ℝ)..(2 * π), chi j φ • (chi j (-(φ + θ)) • σ (kMat (φ + θ)) x) := by
    rw [← (σ (kMat φ)).intervalIntegral_comp_comm hint]
    congr 1; funext θ
    simp only [map_smul, ← UnitaryRep.map_mul_apply, ← kMat_add, smul_smul, neg_add, chi_add]
    congr 1
    rw [← mul_assoc, chi_mul_chi_neg, one_mul]
  have h2 : ∫ θ in (0 : ℝ)..(2 * π), (chi j (-(φ + θ)) • σ (kMat (φ + θ)) x) =
      ∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x := by
    rw [intervalIntegral.integral_comp_add_left (fun θ : ℝ => chi j (-θ) • σ (kMat θ) x) φ, add_zero]
    have := hper.intervalIntegral_add_eq φ 0
    rw [zero_add] at this
    exact this
  unfold wProj
  rw [map_smul, h1, intervalIntegral.integral_smul, h2, smul_comm]

theorem wProj_of_mem {j : ℤ} {x : H} (hx : x ∈ weightSpace σ j) : wProj σ j x = x := by
  have : (fun θ : ℝ => chi j (-θ) • σ (kMat θ) x) = fun _ => x := by
    funext θ
    rw [hx θ, smul_smul, mul_comm, chi_mul_chi_neg, one_smul]
  rw [wProj, this, intervalIntegral.integral_const, sub_zero]
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  rw [← Complex.coe_smul, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hπ), one_smul]

theorem inner_wProj (j : ℤ) (x y : H) :
    ⟪y, wProj σ j x⟫_ℂ = ((2 * π : ℝ)⁻¹ : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) * ⟪y, σ (kMat θ) x⟫_ℂ := by
  rw [wProj, inner_smul_right]
  congr 1
  have hint := (continuous_wIntegrand σ j x).intervalIntegrable (μ := volume) 0 (2 * π)
  have := (innerSL ℂ y).intervalIntegral_comp_comm hint
  simp only [innerSL_apply_apply, inner_smul_right] at this
  exact this.symm

theorem norm_wProj_le (j : ℤ) (x : H) : ‖wProj σ j x‖ ≤ ‖x‖ := by
  rw [wProj, norm_smul]
  have hb : ‖∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x‖ ≤ ‖x‖ * |2 * π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_smul, norm_chi, one_mul, UnitaryRep.norm_map]
  rw [sub_zero, abs_of_pos (by positivity)] at hb
  have hn : ‖((2 * π : ℝ)⁻¹ : ℂ)‖ = (2 * π)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hn]
  calc (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x‖
      ≤ (2 * π)⁻¹ * (‖x‖ * (2 * π)) := by gcongr
    _ = ‖x‖ := by field_simp

theorem wProj_sub (j : ℤ) (x y : H) : wProj σ j (x - y) = wProj σ j x - wProj σ j y := by
  simp only [wProj, map_sub, smul_sub]
  rw [intervalIntegral.integral_sub ((continuous_wIntegrand σ j x).intervalIntegrable _ _)
    ((continuous_wIntegrand σ j y).intervalIntegrable _ _), smul_sub]

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

theorem eps_mem_weightSpace {j : ℤ} {v : H} (hv : v ∈ weightSpace σ j) :
    σ eps v ∈ weightSpace σ (-j) := by
  intro θ
  have e : kMat θ * eps = eps * kMat (-θ) := by
    have := eps_kMat_eps (-θ)
    rw [neg_neg] at this
    calc kMat θ * eps = (eps * kMat (-θ) * eps) * eps := by rw [this]
      _ = eps * kMat (-θ) := by rw [mul_assoc, eps_mul_eps, mul_one]
  rw [← UnitaryRep.map_mul_apply, e, UnitaryRep.map_mul_apply, hv (-θ), map_smul]
  congr 1
  simp only [chi]; congr 1; push_cast; ring

theorem zPos_mem_weightSpace {j : ℤ} {v : H} (hv : v ∈ weightSpace σ j) (s : ℝ) :
    σ (zPos s) v ∈ weightSpace σ j := by
  intro θ
  rw [← UnitaryRep.map_mul_apply, ← zPos_mul_comm, UnitaryRep.map_mul_apply, hv θ, map_smul]

theorem continuous_iteratedFDeriv_partial {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {Φ : P × ℝ → E'}
    (hΦ : ContDiff ℝ ∞ Φ) (k : ℕ) :
    Continuous (fun p : P × ℝ => iteratedFDeriv ℝ k (fun Y => Φ (Y, p.2)) p.1) := by
  set L := ContinuousLinearMap.inl ℝ P ℝ
  have hpart : ∀ (θ : ℝ) (Y : P), iteratedFDeriv ℝ k (fun Y => Φ (Y, θ)) Y =
      ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => L) (iteratedFDeriv ℝ k Φ (Y, θ)) := by
    intro θ Y
    have e : (fun Y => Φ (Y, θ)) = (fun w => Φ (w + (0, θ))) ∘ L := by
      funext Y; simp [L]
    have hΦθ : ContDiff ℝ ∞ (fun w : P × ℝ => Φ (w + (0, θ))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [e, L.iteratedFDeriv_comp_right hΦθ Y (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    simp [L]
  simp_rw [hpart]
  exact (ContinuousLinearMap.continuous _).comp
    ((hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_fst.prodMk continuous_snd))

theorem contDiff_intervalIntegral_param {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
    {Φ : P × ℝ → E'} (hΦ : ContDiff ℝ ∞ Φ) {a b : ℝ} (hab : a ≤ b) :
    ContDiff ℝ ∞ (fun Y => ∫ θ in a..b, Φ (Y, θ)) := by
  let ρ : ContDiffBump ((a + b) / 2) := ⟨(b - a) / 2 + 1, (b - a) / 2 + 2, by linarith, by linarith⟩
  set F : P → ℝ → E' := fun Y θ => ρ θ • Φ (Y, θ) with hF
  have hρ1 : ∀ θ ∈ Ioc a b, ρ θ = 1 := by
    intro θ hθ
    apply ρ.one_of_mem_closedBall
    have hr : ρ.rIn = (b - a) / 2 + 1 := rfl
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [hθ.1, hθ.2]
  have key : (fun Y => ∫ θ in a..b, Φ (Y, θ)) = fun Y => ∫ θ, F Y θ ∂(volume.restrict (Ioc a b)) := by
    funext Y
    rw [intervalIntegral.integral_of_le hab]
    refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
    simp [hF, hρ1 θ hθ]
  rw [key]
  have hcΦ : ∀ θ, ContDiff ℝ ∞ (fun Y => Φ (Y, θ)) := fun θ =>
    hΦ.comp (contDiff_id.prodMk contDiff_const)
  refine contDiff_integral_of_iteratedFDeriv F (fun θ => (hcΦ θ).const_smul _) (fun k => ?_)
    (fun Y₀ => ⟨univ, univ_mem, tsupport ρ, ρ.hasCompactSupport, fun Y _ θ hθ => ?_⟩)
  · have e : ∀ p : P × ℝ, ParamIntegral.iter F k p.1 p.2 =
        ρ p.2 • iteratedFDeriv ℝ k (fun Y => Φ (Y, p.2)) p.1 := by
      intro p
      simp only [ParamIntegral.iter, hF]
      exact iteratedFDeriv_const_smul_apply ((hcΦ p.2).contDiffAt.of_le (by exact_mod_cast le_top))
    simp_rw [e]
    exact (ρ.continuous.comp continuous_snd).smul (continuous_iteratedFDeriv_partial hΦ k)
  · simp only [hF]
    rw [image_eq_zero_of_notMem_tsupport hθ, zero_smul]

theorem isSmoothVector_wProj {w : H} (hw : hGL2.IsSmoothVector (BanachRep.ofUnitary σ) w) (j : ℤ) :
    hGL2.IsSmoothVector (BanachRep.ofUnitary σ) (wProj σ j w) := by
  rw [IsExpLieAlgebra.isSmoothVector_iff]
  set πB := BanachRep.ofUnitary σ
  set Φ : gl2 × ℝ → H := fun p =>
    chi j (-p.2) • πB (hGL2.expG p.1 * hGL2.expG (p.2 • lW) * hGL2.expG 0) w with hΦ
  have hΦs : ContDiff ℝ ∞ Φ := by
    have h1 := hGL2.contDiff_orbit_expG_mul πB hw (φ₁ := fun p : gl2 × ℝ => p.1)
      (φ₂ := fun p => p.2 • lW) (φ₃ := fun _ => 0) contDiff_fst (contDiff_snd.smul contDiff_const)
      contDiff_const
    have h2 : ContDiff ℝ ∞ (fun p : gl2 × ℝ => chi j (-p.2)) := by
      simp only [chi]
      exact Complex.contDiff_exp.comp (((contDiff_const.mul
        (Complex.ofRealCLM.contDiff.comp contDiff_snd.neg)).mul contDiff_const))
    exact h2.smul h1
  have e : hGL2.expOrbit πB (wProj σ j w) = fun Y =>
      ((2 * π : ℝ)⁻¹ : ℂ) • ∫ θ in (0 : ℝ)..(2 * π), Φ (Y, θ) := by
    funext Y
    rw [IsExpLieAlgebra.expOrbit_apply, wProj, map_smul]
    congr 1
    rw [← (πB (hGL2.expG Y)).intervalIntegral_comp_comm
      ((continuous_wIntegrand σ j w).intervalIntegrable _ _)]
    congr 1; funext θ
    simp only [hΦ, map_smul, IsExpLieAlgebra.expG_zero, mul_one, expG_lW, BanachRep.map_mul_apply]
    rfl
  rw [e]
  exact (contDiff_intervalIntegral_param hΦs (by positivity)).const_smul _

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

theorem fourier_neg_coe_eq_chi (n : ℤ) (θ : ℝ) :
    fourier (-n) (θ : AddCircle (2 * π - 0)) = chi n (-θ) := by
  rw [fourier_coe_apply, chi, sub_zero]
  congr 1
  push_cast
  field_simp

theorem exists_wProj_ne_zero {x : H} (hx : x ≠ 0) : ∃ j : ℤ, wProj σ j x ≠ 0 := by
  by_contra hall
  push Not at hall
  set φ : ℝ → ℂ := fun θ => ⟪x, σ (kMat θ) x⟫_ℂ with hφ
  have hφc : Continuous φ := continuous_const.inner (continuous_orbit_kMat σ x)
  have hab : (0 : ℝ) < 2 * π := by positivity
  have hcoeff : ∀ n : ℤ, fourierCoeffOn hab φ n = 0 := by
    intro n
    rw [fourierCoeffOn_eq_integral]
    have h1 := inner_wProj σ n x x
    rw [hall n, inner_zero_right] at h1
    have h2 : ∫ θ in (0 : ℝ)..(2 * π), chi n (-θ) * ⟪x, σ (kMat θ) x⟫_ℂ = 0 := by
      have hne : ((2 * π : ℝ)⁻¹ : ℂ) ≠ 0 := by
        rw [ne_eq, inv_eq_zero]; exact_mod_cast hab.ne'
      exact (mul_eq_zero.1 h1.symm).resolve_left hne
    simp_rw [fourier_neg_coe_eq_chi, smul_eq_mul]
    rw [show (∫ θ in (0 : ℝ)..(2 * π), chi n (-θ) * φ θ) = 0 from h2, smul_zero]
  have hL2 : MemLp φ 2 (volume.restrict (Ioc 0 (2 * π))) := by
    refine MemLp.of_bound hφc.aestronglyMeasurable (‖x‖ * ‖x‖) (Eventually.of_forall fun θ => ?_)
    calc ‖φ θ‖ ≤ ‖x‖ * ‖σ (kMat θ) x‖ := norm_inner_le_norm _ _
      _ = ‖x‖ * ‖x‖ := by rw [UnitaryRep.norm_map]
  have hsum := hasSum_sq_fourierCoeffOn hab hL2
  have h0 : HasSum (fun i : ℤ => ‖fourierCoeffOn hab φ i‖ ^ 2) (0 : ℝ) := by
    simp only [hcoeff, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact hasSum_zero
  have hzero : (2 * π - 0)⁻¹ • ∫ θ in (0 : ℝ)..(2 * π), ‖φ θ‖ ^ 2 = 0 := hsum.unique h0
  have hint0 : ∫ θ in (0 : ℝ)..(2 * π), ‖φ θ‖ ^ 2 = 0 := by
    rw [smul_eq_mul, sub_zero] at hzero
    exact (mul_eq_zero.1 hzero).resolve_left (inv_ne_zero hab.ne')

  set g : ℝ → ℝ := fun θ => ‖φ θ‖ ^ 2 with hg
  have hgc : Continuous g := (continuous_norm.comp hφc).pow 2
  have hg0 : 0 < g 0 := by
    simp only [hg, hφ, kMat_zero]
    have : ⟪x, σ 1 x⟫_ℂ ≠ 0 := by
      rw [UnitaryRep.map_one, ContinuousLinearMap.one_apply, inner_self_ne_zero]; exact hx
    positivity
  have hpos : 0 < ∫ θ in (0 : ℝ)..(2 * π), g θ := by
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun θ => by positivity) (hgc.intervalIntegrable _ _)]
    refine ⟨hab, ?_⟩
    have hopen : IsOpen (Function.support g) := isOpen_ne_fun hgc continuous_const
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 0 (Function.mem_support.2 hg0.ne')
    set δ := min ε (2 * π) with hδ
    have hδ0 : 0 < δ := lt_min hε hab
    have hsub : Ioo 0 δ ⊆ Function.support g ∩ Ioc 0 (2 * π) := by
      intro θ hθ
      refine ⟨hball ?_, hθ.1, le_trans hθ.2.le (min_le_right _ _)⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hθ.1]
      exact lt_of_lt_of_le hθ.2 (min_le_left _ _)
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Ioo, sub_zero]
    exact ENNReal.ofReal_pos.2 hδ0
  rw [hint0] at hpos
  exact lt_irrefl _ hpos

theorem exists_smooth_weight {j : ℤ} {x : H} (hx : x ∈ weightSpace σ j) (hx0 : x ≠ 0) :
    ∃ v ∈ weightSpace σ j, v ≠ 0 ∧ hGL2.IsSmoothVector (BanachRep.ofUnitary σ) v := by
  have hd := hGL2.dense_smoothVectors (BanachRep.ofUnitary σ)
  obtain ⟨w, hw, hwx⟩ := Metric.dense_iff.1 hd x ‖x‖ (norm_pos_iff.2 hx0)
  refine ⟨wProj σ j w, wProj_mem σ j w, ?_, isSmoothVector_wProj σ hwx j⟩
  intro h0
  have h1 : ‖wProj σ j (x - w)‖ ≤ ‖x - w‖ := norm_wProj_le σ j (x - w)
  rw [wProj_sub, h0, sub_zero, wProj_of_mem σ hx] at h1
  rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hw
  exact lt_irrefl _ (lt_of_le_of_lt h1 hw)

end GroundTheory.Automorphic.ArchWhittaker
