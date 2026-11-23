import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ContDiff

open scoped Nat Topology

noncomputable section

namespace GlobalTheory.RightDerivSmooth

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in

theorem exp_intertwine (Y Z H : Matrix (Fin n) (Fin n) ℂ) (h : Y * H = H * Z) :
    NormedSpace.exp Y * H = H * NormedSpace.exp Z := by
  have hp : ∀ m : ℕ, Y ^ m * H = H * Z ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  have h1 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) * H) (NormedSpace.exp Y * H) := by
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y).mul_right H
  have h2 : HasSum (fun m : ℕ => H * ((m ! : ℂ)⁻¹ • Z ^ m)) (H * NormedSpace.exp Z) := by
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Z).mul_left H
  have e : (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) * H) = fun m : ℕ => H * ((m ! : ℂ)⁻¹ • Z ^ m) := by
    funext m
    rw [Matrix.smul_mul, hp, Matrix.mul_smul]
  rw [e] at h1
  exact h1.unique h2

set_option backward.isDefEq.respectTransparency false in

theorem inUH_exp {H X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (t : ℝ) :
    inUH H (NormedSpace.exp ((t : ℂ) • X)) := by
  have hY : ((t : ℂ) • X)ᴴ * H + H * ((t : ℂ) • X) = 0 := by
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hX, smul_zero]
  generalize (t : ℂ) • X = Y at hY
  show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
  have h1 : Yᴴ * H = H * (-Y) := by
    rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hY
  rw [← Matrix.exp_conjTranspose, exp_intertwine _ _ _ h1, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

theorem inUH_mul {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) : inUH H (a * b) := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

set_option backward.isDefEq.respectTransparency false in

theorem hasDerivAt_exp_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  open scoped Matrix.Norms.Operator in
  have h : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  open scoped Matrix.Norms.Operator in
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  open scoped Matrix.Norms.Operator in
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_mul_exp (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_exp_entry X k j).const_mul _

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasDerivAt_local {H X g : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (hg : inUH H g)
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (e : ∀ h ∈ U, inUH H h → f h = F h) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hc := hasDerivAt_mul_exp g X
  have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  have hd : HasFDerivAt F (fderiv ℝ F g) (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [h0]
    exact ((hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (0 : ℝ) hc
  refine h1.congr_of_eventuallyEq ?_
  have h2 : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hc.continuousAt.eventually (hU.mem_nhds (by simpa only [h0] using hgU))
  filter_upwards [h2] with t ht
  exact e _ ht (inUH_mul hg (inUH_exp hX t))

end GlobalTheory.RightDerivSmooth

section
open GlobalTheory.RightDerivSmooth
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option backward.isDefEq.respectTransparency false in

theorem GlobalTheory.RightDerivSmooth.right_derivative_smooth_on_unitary_group : ∀ (n : ℕ) (H X : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E), Xᴴ * H + H * X = 0 → SmoothOnH H f →
    ContinuousOn f {g | inUH H g} ∧ SmoothOnH H (rdM X f) ∧
      ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (rdM X f g) 0 := by
  intro n H X E _ _ f hX hf
  have hder : ∀ g, inUH H g → ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), ∃ F : Matrix (Fin n) (Fin n) ℂ → E,
      IsOpen U ∧ g ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ (∀ h ∈ U, inUH H h → f h = F h) ∧
      ∀ h ∈ U, inUH H h → rdM X f h = fderiv ℝ F h (h * X) ∧
        HasDerivAt (fun t : ℝ => f (h * NormedSpace.exp ((t : ℂ) • X))) (rdM X f h) 0 := by
    intro g hg
    obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
    refine ⟨U, F, hU, hgU, hF, e, fun h hhU hh => ?_⟩
    have hd := hasDerivAt_local hX hh hU hhU hF e
    have hr : rdM X f h = fderiv ℝ F h (h * X) := hd.deriv
    exact ⟨hr, hr ▸ hd⟩
  refine ⟨?_, ?_, fun g hg => ?_⟩
  · intro g hg
    obtain ⟨U, F, hU, hgU, hF, e, -⟩ := hder g hg
    have hFc : ContinuousWithinAt F {g | inUH H g} g :=
      ((hF.continuousOn).continuousAt (hU.mem_nhds hgU)).continuousWithinAt
    refine hFc.congr_of_eventuallyEq ?_ (e g hgU hg)
    filter_upwards [inter_mem_nhdsWithin {g | inUH H g} (hU.mem_nhds hgU)] with h hh
    exact e h hh.2 hh.1
  · intro g hg
    obtain ⟨U, F, hU, hgU, hF, -, hr⟩ := hder g hg
    refine ⟨U, fun h => fderiv ℝ F h (h * X), hU, hgU, ?_, fun h hhU hh => (hr h hhU hh).1⟩
    have h1 : ContDiffOn ℝ ∞ (fun h => fderiv ℝ F h) U := hF.fderiv_of_isOpen hU (le_of_eq rfl)
    have h2 : ContDiff ℝ ∞ (fun h : Matrix (Fin n) (Fin n) ℂ => h * X) :=
      (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff
    exact h1.clm_apply h2.contDiffOn
  · obtain ⟨U, F, hU, hgU, hF, -, hr⟩ := hder g hg
    exact (hr g hgU hg).2

end

example : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := le_of_eq rfl

theorem GlobalTheory.rdM_smoothOnH : ∀ (n : ℕ) (H X : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E), Xᴴ * H + H * X = 0 → SmoothOnH H f →
    ContinuousOn f {g | inUH H g} ∧ SmoothOnH H (rdM X f) ∧
      ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (rdM X f g) 0 :=
  fun n H X E _ _ f hX hf => GlobalTheory.RightDerivSmooth.right_derivative_smooth_on_unitary_group n H X E f hX hf
