import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KbBase

noncomputable section

open Matrix Finset Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbCurve

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain.KbBase
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hasDerivAt_entry {A : ℝ → Mat n} {A' : Mat n} {t : ℝ} (h : HasDerivAt A A' t) (a b : Fin n) :
    HasDerivAt (fun s => A s a b) (A' a b) t :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 h a) b

theorem hasDerivAt_of_entry {A : ℝ → Mat n} {A' : Mat n} {t : ℝ} (h : ∀ a b, HasDerivAt (fun s => A s a b) (A' a b) t) :
    HasDerivAt A A' t :=
  hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => h a b

theorem hasDerivAt_matmul {A B : ℝ → Mat n} {A' B' : Mat n} {t : ℝ} (hA : HasDerivAt A A' t) (hB : HasDerivAt B B' t) :
    HasDerivAt (fun s => A s * B s) (A' * B t + A t * B') t := by
  apply hasDerivAt_of_entry
  intro a b
  have hsum : HasDerivAt (fun s => ∑ k, A s a k * B s k b)
      (∑ k, (A' a k * B t k b + A t a k * B' k b)) t :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_entry hA a k).mul (hasDerivAt_entry hB k b)
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using hsum

theorem hasDerivAt_line (X : Mat n) : HasDerivAt (fun t : ℝ => 1 + t • X) X 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
  simp only [id, one_smul] at h
  exact h

theorem det_line_ne (X : Mat n) : ∀ᶠ t : ℝ in 𝓝 0, (1 + t • X).det ≠ 0 := by
  have hc : Continuous fun t : ℝ => (1 + t • X).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have h0 : (1 + (0:ℝ) • X).det ≠ 0 := by simp
  exact hc.continuousAt.eventually_ne h0

theorem hasDerivAt_lineInv (X : Mat n) : HasDerivAt (fun t : ℝ => (1 + t • X)⁻¹) (-X) 0 := by
  set B : ℝ → Mat n := fun t => (1 + t • X)⁻¹ with hB
  have hB0 : B 0 = 1 := by simp [hB]
  have hcont : ContinuousAt B 0 := by
    have hline : Continuous fun t : ℝ => (1 : Mat n) + t • X :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hdet : ContinuousAt Ring.inverse ((1 : Mat n) + (0:ℝ) • X).det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (by simp)
    have h2 : ContinuousAt (fun t : ℝ => (1 : Mat n) + t • X) 0 := hline.continuousAt
    exact ContinuousAt.comp (g := Inv.inv) (f := fun t : ℝ => (1 : Mat n) + t • X)
      (continuousAt_matrix_inv _ hdet) h2
  have hlim : Tendsto (fun t => -(B t * X)) (𝓝[≠] (0:ℝ)) (𝓝 (-X)) := by
    have h1 : Tendsto (fun t => -(B t * X)) (𝓝 (0:ℝ)) (𝓝 (-(B 0 * X))) :=
      ((hcont.mul continuousAt_const).neg)
    rw [hB0, one_mul] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  refine hasDerivAt_iff_tendsto_slope.mpr (hlim.congr' ?_)
  have hne : ∀ᶠ t in 𝓝[≠] (0:ℝ), (1 + t • X).det ≠ 0 :=
    (det_line_ne X).filter_mono nhdsWithin_le_nhds
  filter_upwards [hne, self_mem_nhdsWithin] with t ht ht0
  have hinv : B t * (1 + t • X) = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht)
  rw [mul_add, mul_one, Matrix.mul_smul] at hinv
  have ht0' : t ≠ 0 := ht0
  rw [slope_def_module, hB0, sub_zero, ← hinv, sub_add_cancel_left, smul_neg, smul_smul,
    inv_mul_cancel₀ ht0', one_smul]

theorem hasDerivAt_detLine (X : Mat n) : HasDerivAt (fun t : ℝ => (1 + t • X).det) X.trace 0 := by
  set p : Polynomial ℂ := (1 + (Polynomial.X : Polynomial ℂ) • X.map Polynomial.C).det with hp
  have hev : ∀ t : ℝ, (1 + t • X).det = p.eval (t : ℂ) := by
    intro t
    rw [hp, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, Complex.real_smul] <;> ring
  have hd : HasDerivAt (fun y : ℝ => p.eval (y : ℂ)) (p.derivative.eval ((0:ℝ) : ℂ)) 0 :=
    (p.hasDerivAt ((0:ℝ) : ℂ)).comp_ofReal
  rw [Complex.ofReal_zero, hp, Matrix.derivative_det_one_add_X_smul] at hd
  rw [show (fun t : ℝ => (1 + t • X).det) = fun y : ℝ => p.eval (y : ℂ) from funext hev]
  exact hd

end PositivityTheory.RgBcC.LfSt.Kchain.KbCurve
