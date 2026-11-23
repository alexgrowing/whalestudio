import Formalism.RealPlaceAnalysis.SmoothVectorGrowthBound
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexificationHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.REAL

section F4ALinfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma continuous_exp_neg_smul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp (((-t : ℝ) : ℂ) • X)) :=
  NormedSpace.exp_continuous.comp ((Complex.continuous_ofReal.comp continuous_neg).smul continuous_const)

end F4ALinfty

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma frobenius_nonneg {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs g := by
  unfold hs
  positivity

lemma frobenius_cauchy_schwarz {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, ‖A i j‖ * ‖B i j‖) ^ 2 ≤ hs A * hs B := by
  unfold hs
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p => ‖A p.1 p.2‖) (fun p => ‖B p.1 p.2‖)
  simpa only [Fintype.sum_prod_type] using h

lemma frobenius_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : hs (A * B) ≤ hs A * hs B := by
  unfold hs
  have key : ∀ i j, ‖(A * B) i j‖ ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) := by
    intro i j
    rw [Matrix.mul_apply]
    calc ‖∑ k, A i k * B k j‖ ^ 2 ≤ (∑ k, ‖A i k‖ * ‖B k j‖) ^ 2 := by
          gcongr
          calc ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
            _ = ∑ k, ‖A i k‖ * ‖B k j‖ := by simp only [norm_mul]
      _ ≤ (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ i, ∑ j, ‖(A * B) i j‖ ^ 2
        ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) := by
          gcongr with i _ j _
          exact key i j
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * (∑ j, ∑ k, ‖B k j‖ ^ 2) := by
          rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ j, ‖A i j‖ ^ 2) * ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
          congr 1
          exact Finset.sum_comm

lemma contDiff_frobenius {n : ℕ} : ContDiff ℝ ∞ (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact (contDiff_norm_sq (𝕜 := ℝ)).comp (contDiff_apply_apply (𝕜 := ℝ) (E := ℂ) i j)

lemma frobenius_pos_of_indefinite_unitary {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    [Nonempty (Fin n)] : 0 < hs g := by
  by_contra hle
  push_neg at hle
  have h0 : hs g = 0 := le_antisymm hle (frobenius_nonneg g)
  have hg0 : g = 0 := by
    unfold hs at h0
    ext i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h0 i (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 h1 j (Finset.mem_univ _)
    simpa using h2
  unfold inUJ at hg
  rw [hg0] at hg
  obtain ⟨i⟩ := ‹Nonempty (Fin n)›
  have := congrFun (congrFun hg i) i
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_apply, Jm,
    Matrix.diagonal_apply_eq] at this
  split_ifs at this <;> norm_num at this

theorem smooth_log_frobenius (n : ℕ) (ε : Fin n → Bool) : SmoothOnG ε (fun x => ((hh x : ℝ) : ℂ)) := by
  intro g₀ hg₀
  rcases isEmpty_or_nonempty (Fin n) with hE | hN
  · refine ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => ?_⟩
    simp [hh, hs]
  · refine ⟨{g | 0 < hs g}, fun x => ((hh x : ℝ) : ℂ),
      isOpen_lt continuous_const contDiff_frobenius.continuous, frobenius_pos_of_indefinite_unitary hg₀, ?_, fun g _ _ => rfl⟩
    have h1 : ContDiffOn ℝ ∞ (fun x => hh x) {g : Matrix (Fin n) (Fin n) ℂ | 0 < hs g} := by
      unfold hh
      exact contDiff_frobenius.contDiffOn.log (fun x hx => ne_of_gt hx)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn h1

lemma mul_exp_zero_smul {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
  simp

private lemma hasDerivAt_mul_matrix_exp_smul {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => g * NormedSpace.exp ((s : ℂ) • X))
      (g * (NormedSpace.exp ((t : ℂ) • X) * X)) t := by
  letI i1 : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI i2 : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI i3 : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI i4 : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedSpace
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h3 : ∀ s : ℝ, ((s : ℂ) • X) = s • X := fun s => by
    ext i j
    simp [Complex.real_smul]
  simp only [h3]
  exact (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).const_mul g

lemma hasDerivAt_frobenius_curve {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => hs (g * NormedSpace.exp ((t : ℂ) • X)))
      (∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * X) i j)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
    have h2 := hasDerivAt_mul_matrix_exp_smul g X 0
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul] at h2
    exact h2
  have hentry : ∀ i j, HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X)) i j) ((g * X) i j) 0 :=
    fun i j => hasDerivAt_pi.1 (hasDerivAt_pi.1 hc i) j
  have hE : ∀ i j, HasDerivAt (fun t : ℝ => ‖(g * NormedSpace.exp ((t : ℂ) • X)) i j‖ ^ 2)
      (2 * inner ℝ (g i j) ((g * X) i j)) 0 := by
    intro i j
    convert (hentry i j).norm_sq using 1
    beta_reduce
    rw [mul_exp_zero_smul]
  have hS := HasDerivAt.sum (u := Finset.univ)
    (fun i _ => HasDerivAt.sum (u := Finset.univ) (fun j _ => hE i j))
  unfold hs
  have hfun : (fun t : ℝ => ∑ i, ∑ j, ‖(g * NormedSpace.exp ((t : ℂ) • X)) i j‖ ^ 2) =
      ∑ i, ∑ j, fun t : ℝ => ‖(g * NormedSpace.exp ((t : ℂ) • X)) i j‖ ^ 2 := by
    funext t
    simp only [Finset.sum_apply]
  rw [hfun]
  exact hS

lemma right_derivative_log_frobenius {n : ℕ} (X g : Matrix (Fin n) (Fin n) ℂ) (hpos : 0 < hs g) :
    Rd X (fun x => ((hh x : ℝ) : ℂ)) g =
      (((∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * X) i j)) / hs g : ℝ) : ℂ) := by
  have h0 : hs (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = hs g := by rw [mul_exp_zero_smul]
  have h2 : HasDerivAt (fun t : ℝ => Real.log (hs (g * NormedSpace.exp ((t : ℂ) • X))))
      ((∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * X) i j)) / hs g) 0 := by
    have := (hasDerivAt_frobenius_curve g X).log (by simp only [h0]; exact hpos.ne')
    simpa only [h0] using this
  unfold Rd hh
  exact h2.ofReal_comp.deriv

private lemma bound_of_hs_pos {n : ℕ} (X g : Matrix (Fin n) (Fin n) ℂ) (hpos : 0 < hs g) :
    |(∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * X) i j)) / hs g| ≤ 2 * Real.sqrt (hs X) := by
  have h1 : |∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * X) i j)| ≤
      2 * ∑ i, ∑ j, ‖g i j‖ * ‖(g * X) i j‖ := by
    calc |∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * X) i j)|
          ≤ ∑ i, ∑ j, |2 * inner ℝ (g i j) ((g * X) i j)| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            gcongr with i _
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, 2 * (‖g i j‖ * ‖(g * X) i j‖) := by
            gcongr with i _ j _
            rw [abs_mul, abs_two]
            gcongr
            exact abs_real_inner_le_norm _ _
      _ = 2 * ∑ i, ∑ j, ‖g i j‖ * ‖(g * X) i j‖ := by simp only [Finset.mul_sum]
  have hT0 : 0 ≤ ∑ i, ∑ j, ‖g i j‖ * ‖(g * X) i j‖ := by positivity
  have hX0 := frobenius_nonneg X
  have hB0 : 0 ≤ hs g * Real.sqrt (hs X) := by positivity
  have hsq : (∑ i, ∑ j, ‖g i j‖ * ‖(g * X) i j‖) ^ 2 ≤ (hs g * Real.sqrt (hs X)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hX0]
    calc (∑ i, ∑ j, ‖g i j‖ * ‖(g * X) i j‖) ^ 2 ≤ hs g * hs (g * X) := frobenius_cauchy_schwarz g (g * X)
      _ ≤ hs g * (hs g * hs X) := by gcongr; exact frobenius_mul_le g X
      _ = hs g ^ 2 * hs X := by ring
  have hT : ∑ i, ∑ j, ‖g i j‖ * ‖(g * X) i j‖ ≤ hs g * Real.sqrt (hs X) := by nlinarith
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  nlinarith

theorem right_derivative_log_frobenius_le {n : ℕ} (ε : Fin n → Bool) (X g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    ‖Rd X (fun x => ((hh x : ℝ) : ℂ)) g‖ ≤ 2 * Real.sqrt (hs X) := by
  rcases isEmpty_or_nonempty (Fin n) with hE | hN
  · have : ∀ x : Matrix (Fin n) (Fin n) ℂ, hs x = 0 := fun x => by simp [hs]
    simp only [Rd, hh, this, Real.log_zero, Complex.ofReal_zero, deriv_const, norm_zero]
    positivity
  · have hpos := frobenius_pos_of_indefinite_unitary hg
    rw [right_derivative_log_frobenius X g hpos, Complex.norm_real, Real.norm_eq_abs]
    exact bound_of_hs_pos X g hpos

theorem log_frobenius_lipschitz_holds : HhLip :=
  fun n ε => ⟨smooth_log_frobenius n ε, fun X g _ hg => right_derivative_log_frobenius_le ε X g hg⟩

lemma continuous_frobenius_exp_neg_smul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => hs (NormedSpace.exp (((-t : ℝ) : ℂ) • X))) := by
  have h1 : Continuous (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := contDiff_frobenius.continuous
  exact h1.comp (continuous_exp_neg_smul X)

private lemma Jm_mul_Jm_self {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private lemma inUJ_exp_real_smul_of_inG {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (u : ℝ) : inUJ ε (NormedSpace.exp ((u : ℂ) • X)) := by
  have hJ := Jm_mul_Jm_self ε
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := by
    unfold inG at hX
    exact eq_neg_of_add_eq_zero_left hX
  have h2 : Xᴴ = -(Jm ε * X * Jm ε) := by
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = -(Jm ε * X * Jm ε) := by rw [h1, Matrix.neg_mul]
  have hYc : ((u : ℂ) • X)ᴴ = Jm ε * (-((u : ℂ) • X)) * Jm ε := by
    rw [Matrix.conjTranspose_smul, h2]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨Jm ε, Jm ε, hJ, hJ⟩
  have hU : ((u : ℂ) • X)ᴴ = (U : Matrix (Fin n) (Fin n) ℂ) * (-((u : ℂ) • X)) *
      ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := hYc
  unfold inUJ
  rw [← Matrix.exp_conjTranspose, hU, Matrix.exp_units_conj]
  show Jm ε * NormedSpace.exp (-((u : ℂ) • X)) * Jm ε * Jm ε * NormedSpace.exp ((u : ℂ) • X) = Jm ε
  rw [Matrix.mul_assoc (Jm ε * NormedSpace.exp (-((u : ℂ) • X))) (Jm ε) (Jm ε), hJ, Matrix.mul_one,
    Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ ((Commute.refl ((u : ℂ) • X)).neg_left),
    neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]

private lemma inUJ_mul_real_place_taylor {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : inUJ ε a) (hb : inUJ ε b) : inUJ ε (a * b) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul, show bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b by
    simp only [Matrix.mul_assoc], ha, hb]

lemma hasDerivAt_right_derivative {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {X h : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hX : inG ε X) (hh : inUJ ε h) :
    HasDerivAt (fun u : ℝ => f (h * NormedSpace.exp ((u : ℂ) • X))) (Rd X f h) 0 := by
  obtain ⟨U, F, hU, hhU, hF, hfF⟩ := hf h hh
  have h0 : h * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = h := mul_exp_zero_smul h X
  have hcont : ContinuousAt (fun u : ℝ => h * NormedSpace.exp ((u : ℂ) • X)) 0 :=
    (hasDerivAt_mul_matrix_exp_smul h X 0).continuousAt
  have hmem : U ∈ 𝓝 (h * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [h0]
    exact hU.mem_nhds hhU
  have hev : (fun u : ℝ => f (h * NormedSpace.exp ((u : ℂ) • X))) =ᶠ[𝓝 0]
      (fun u => F (h * NormedSpace.exp ((u : ℂ) • X))) := by
    filter_upwards [hcont.preimage_mem_nhds hmem] with u hu
    exact hfF _ hu (inUJ_mul_real_place_taylor hh (inUJ_exp_real_smul_of_inG hX u))
  have hFd : DifferentiableAt ℝ F (h * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [h0]
    exact (hF.contDiffAt (hU.mem_nhds hhU)).differentiableAt (by simp)
  have hdF : DifferentiableAt ℝ (fun u : ℝ => F (h * NormedSpace.exp ((u : ℂ) • X))) 0 :=
    hFd.comp (0 : ℝ) (hasDerivAt_mul_matrix_exp_smul h X 0).differentiableAt
  have hd : DifferentiableAt ℝ (fun u : ℝ => f (h * NormedSpace.exp ((u : ℂ) • X))) 0 :=
    hdF.congr_of_eventuallyEq hev
  unfold Rd
  exact hd.hasDerivAt

lemma hasDerivAt_right_translate {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {X g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hX : inG ε X) (hg : inUJ ε g) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X)))
      (Rd X f (g * NormedSpace.exp ((t : ℂ) • X))) t := by
  have hm : inUJ ε (g * NormedSpace.exp ((t : ℂ) • X)) := inUJ_mul_real_place_taylor hg (inUJ_exp_real_smul_of_inG hX t)
  have H := hasDerivAt_right_derivative hf hX hm
  have H2 : HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((u : ℂ) • X)))
      (Rd X f (g * NormedSpace.exp ((t : ℂ) • X))) (t - t) := by
    rw [sub_self]
    exact H
  have H3 := H2.comp_sub_const t t
  have hfun : (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X))) =
      (fun s : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((s - t : ℝ) : ℂ) • X))) := by
    funext s
    rw [Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _
      (((Commute.refl X).smul_left (t : ℂ)).smul_right ((s - t : ℝ) : ℂ)), ← add_smul,
      show ((t : ℂ) + ((s - t : ℝ) : ℂ)) = (s : ℂ) by push_cast; ring]
  rw [hfun]
  exact H3

lemma right_derivative_zero_outside_support {n : ℕ} {ε : Fin n → Bool} {φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {X h : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hX : inG ε X) (hh : inUJ ε h)
    (hsupp : ∀ g, inUJ ε g → R < hs g → φ g = 0) (hR : R < hs h) : Rd X φ h = 0 := by
  have hcont : ContinuousAt (fun u : ℝ => h * NormedSpace.exp ((u : ℂ) • X)) 0 :=
    (hasDerivAt_mul_matrix_exp_smul h X 0).continuousAt
  have hc2 : ContinuousAt (fun u : ℝ => hs (h * NormedSpace.exp ((u : ℂ) • X))) 0 :=
    contDiff_frobenius.continuous.continuousAt.comp hcont
  have h0 : R < hs (h * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [mul_exp_zero_smul]
    exact hR
  have hR' : ∀ᶠ u : ℝ in 𝓝 (0 : ℝ), R < hs (h * NormedSpace.exp ((u : ℂ) • X)) :=
    hc2.eventually (lt_mem_nhds h0)
  have hev : (fun u : ℝ => φ (h * NormedSpace.exp ((u : ℂ) • X))) =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
    filter_upwards [hR'] with u hu
    exact hsupp _ (inUJ_mul_real_place_taylor hh (inUJ_exp_real_smul_of_inG hX u)) hu
  unfold Rd
  rw [hev.deriv_eq]
  simp

lemma continuous_smooth_on_group {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) :
    Continuous (fun g : UJ ε => f (toM g)) := by
  have hc : Continuous (toM : UJ ε → Matrix (Fin n) (Fin n) ℂ) := by
    unfold toM
    exact Units.continuous_val.comp continuous_subtype_val
  rw [continuous_iff_continuousAt]
  intro g
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (toM g) g.2
  have hev : (fun g' : UJ ε => F (toM g')) =ᶠ[𝓝 g] (fun g' => f (toM g')) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)] with g' hg'
    exact (hfF _ hg' g'.2).symm
  exact ContinuousAt.congr ((hF.continuousOn.continuousAt (hU.mem_nhds hgU)).comp hc.continuousAt) hev

private lemma Jm_mul_conjTranspose_mul_Jm_mul_eq_one_of_inUJ {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : inUJ ε g) : Jm ε * gᴴ * Jm ε * g = 1 := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Jm_mul_Jm_self]

lemma isCompact_frobenius_sublevel {n : ℕ} (ε : Fin n → Bool) (r : ℝ) : IsCompact {g : UJ ε | hsG g ≤ r} := by
  haveI : ProperSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.proper ℝ _
  have hhs : Continuous (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := contDiff_frobenius.continuous
  have hSc : IsCompact {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g ∧ hs g ≤ r} := by
    apply Metric.isCompact_of_isClosed_isBounded
    · show IsClosed ({g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Jm ε * g = Jm ε} ∩ {g | hs g ≤ r})
      have hcJ : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => gᴴ * Jm ε * g) :=
        (continuous_id.matrix_conjTranspose.mul continuous_const).mul continuous_id
      exact (isClosed_eq hcJ continuous_const).inter (isClosed_le hhs continuous_const)
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨Real.sqrt r, fun g hg => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (Matrix.norm_le_iff (Real.sqrt_nonneg r)).2 fun i j => ?_
      have h1 : ‖g i j‖ ^ 2 ≤ hs g := by
        unfold hs
        calc ‖g i j‖ ^ 2 ≤ ∑ j', ‖g i j'‖ ^ 2 :=
              Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun _ _ => by positivity)
                (Finset.mem_univ j)
          _ ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
              Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2) (fun _ _ => by positivity)
                (Finset.mem_univ i)
      calc ‖g i j‖ = Real.sqrt (‖g i j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt r := Real.sqrt_le_sqrt (h1.trans hg.2)
  haveI := isCompact_iff_compactSpace.mp hSc
  let ψ : {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g ∧ hs g ≤ r} → UJ ε := fun p =>
    ⟨⟨p.1, Jm ε * (p.1)ᴴ * Jm ε, mul_eq_one_comm.mp (Jm_mul_conjTranspose_mul_Jm_mul_eq_one_of_inUJ p.2.1), Jm_mul_conjTranspose_mul_Jm_mul_eq_one_of_inUJ p.2.1⟩, p.2.1⟩
  have hψ : Continuous ψ := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · exact continuous_subtype_val
    · exact (continuous_const.mul continuous_subtype_val.matrix_conjTranspose).mul continuous_const
  have key : {g : UJ ε | hsG g ≤ r} = Set.range ψ := by
    ext g
    constructor
    · intro hg
      exact ⟨⟨toM g, show inUJ ε (toM g) ∧ hs (toM g) ≤ r from ⟨g.2, hg⟩⟩, Subtype.ext (Units.ext rfl)⟩
    · rintro ⟨p, rfl⟩
      exact p.2.2
  rw [key]
  exact isCompact_range hψ

theorem integral_right_derivative_zero : IntRdZero := by
  intro n ε φ X R hφ hX hsupp
  let E : ℝ → UJ ε := fun t =>
    indefiniteUnitaryMk ε (NormedSpace.exp ((t : ℂ) • X)) (exp_indefinite_unitary_holds n ε X hX t)
  have : (muG ε).IsMulRightInvariant := ⟨fun g => indefinite_unitary_unimodular n ε g⟩
  have hcφ := continuous_smooth_on_group hφ
  have hcR := continuous_smooth_on_group (rdSmooth_of right_derivative_extends n ε φ X hφ hX)
  obtain ⟨M0, hM0⟩ := (isCompact_frobenius_sublevel ε R).exists_bound_of_continuousOn hcR.continuousOn
  obtain ⟨M1, hM1⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_frobenius_exp_neg_smul X).continuousOn
  let M := max M0 0
  let K' := {g : UJ ε | hsG g ≤ R * M1}
  let F : ℝ → UJ ε → ℂ := fun t g => φ (toM g * NormedSpace.exp ((t : ℂ) • X))
  let F' : ℝ → UJ ε → ℂ := fun t g => Rd X φ (toM g * NormedSpace.exp ((t : ℂ) • X))
  let bound : UJ ε → ℝ := K'.indicator (fun _ => M)
  have hFc : ∀ t, Continuous (F t) := fun t => by
    have := hcφ.comp (continuous_mul_const (E t)); exact this
  have hF'c : ∀ t, Continuous (F' t) := fun t => by
    have := hcR.comp (continuous_mul_const (E t)); exact this
  have hint0 : Integrable (F 0) (muG ε) := by
    refine (hFc 0).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_frobenius_sublevel ε R) ?_)
    intro g hg
    simp only [Set.mem_ofPred_eq, not_le] at hg
    show φ (toM g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = 0
    rw [mul_exp_zero_smul]
    exact hsupp _ g.2 hg
  have hbound : ∀ g : UJ ε, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖F' t g‖ ≤ bound g := by
    intro g t ht
    have hh : inUJ ε (toM g * NormedSpace.exp ((t : ℂ) • X)) :=
      indefinite_unitary_mul_mem ε g.2 (exp_indefinite_unitary_holds n ε X hX t)
    by_cases hc : hs (toM g * NormedSpace.exp ((t : ℂ) • X)) ≤ R
    · have hM : ‖F' t g‖ ≤ M := (hM0 (g * E t) hc).trans (le_max_left _ _)
      have hmem : g ∈ K' := by
        have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
          exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
        have h1 := hM1 t ht'
        rw [Real.norm_eq_abs] at h1
        have h2 : hs (NormedSpace.exp (((-t : ℝ) : ℂ) • X)) ≤ M1 := (le_abs_self _).trans h1
        have hR0 : 0 ≤ R := (frobenius_nonneg _).trans hc
        have hg : toM g = (toM g * NormedSpace.exp ((t : ℂ) • X)) *
            NormedSpace.exp (((-t : ℝ) : ℂ) • X) := by
          rw [Matrix.mul_assoc, ← one_parameter_subgroup_holds n X t (-t), add_neg_cancel, mul_exp_zero_smul]
        show hs (toM g) ≤ R * M1
        rw [hg]
        exact (frobenius_mul_le _ _).trans (mul_le_mul hc h2 (frobenius_nonneg _) hR0)
      show ‖F' t g‖ ≤ K'.indicator (fun _ => M) g
      rw [Set.indicator_of_mem hmem]
      exact hM
    · push Not at hc
      have h0 : F' t g = 0 := right_derivative_zero_outside_support hX hh hsupp hc
      rw [h0, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) g
  have hbint : Integrable bound (muG ε) := by
    refine (integrable_indicator_iff (isCompact_frobenius_sublevel ε (R * M1)).isClosed.measurableSet).2 ?_
    exact integrableOn_const (isCompact_frobenius_sublevel ε (R * M1)).measure_lt_top.ne
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muG ε) (F := F) (F' := F')
    (x₀ := 0) (bound := bound) (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    (Eventually.of_forall fun t => (hFc t).aestronglyMeasurable) hint0
    (hF'c 0).aestronglyMeasurable (ae_of_all _ hbound) hbint
    (ae_of_all _ fun g t _ => hasDerivAt_right_translate hφ hX g.2 t)
  have hconst : (fun t => ∫ g, F t g ∂(muG ε)) = fun _ => ∫ g, φ (toM g) ∂(muG ε) := by
    funext t
    exact integral_mul_right_eq_self (fun g => φ (toM g)) (E t)
  rw [hconst] at key
  have h0 := key.2.unique (hasDerivAt_const (0 : ℝ) _)
  simpa only [F', mul_exp_zero_smul] using h0

end Formalism.REAL
