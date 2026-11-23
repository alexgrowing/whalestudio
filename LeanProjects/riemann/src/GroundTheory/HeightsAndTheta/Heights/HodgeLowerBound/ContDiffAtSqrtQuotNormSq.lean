import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuWeightChartSmooth
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMuLineNormEq
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMuFrameExists
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped Matrix ComplexOrder

namespace MuWeightChartSmooth

section Calculus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞} {x : F}

theorem contDiffAt_eval {σ : Type*} {Φ : F → σ → ℂ} (hΦ : ∀ i, ContDiffAt ℝ n (fun w => Φ w i) x)
    (P : MvPolynomial σ ℂ) : ContDiffAt ℝ n (fun w => eval (Φ w) P) x := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiffAt_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (hΦ i)

theorem contDiffAt_det {m : Type*} [Fintype m] [DecidableEq m] {M : F → Matrix m m ℂ}
    (hM : ∀ i j, ContDiffAt ℝ n (fun w => M w i j) x) : ContDiffAt ℝ n (fun w => (M w).det) x := by
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hM _ _)

theorem contDiffAt_star {f : F → ℂ} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun w => star (f w)) x :=
  (Complex.conjCLE.contDiff.contDiffAt).comp x hf

theorem contDiffAt_zpow_of_ne {f : F → ℝ} (hf : ContDiffAt ℝ n f x) (h0 : f x ≠ 0) (m : ℤ) :
    ContDiffAt ℝ n (fun w => f w ^ m) x := by
  rcases m with m | m
  · simpa using hf.pow m
  · simp only [zpow_negSucc]
    exact (hf.pow (m + 1)).fun_inv (pow_ne_zero _ h0)

theorem contDiffAt_sandwich {m : Type*} [Fintype m] {A B : F → Matrix m m ℂ}
    (hA : ∀ i j, ContDiffAt ℝ n (fun w => A w i j) x) (hB : ∀ i j, ContDiffAt ℝ n (fun w => B w i j) x)
    (i j : m) : ContDiffAt ℝ n (fun w => ((A w)ᴴ * B w * A w) i j) x := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact ContDiffAt.sum fun k _ =>
    (ContDiffAt.sum fun l _ => (contDiffAt_star (hA l i)).mul (hB l k)).mul (hA k j)

end Calculus

section Chart

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

omit [Algebra ℚ Ω] in

theorem contDiffAt_valAt {y : (Σ k, ι k) → Ω} {m : ℕ} {γ : (Fin m → ℂ) → (Σ k, ι k) → ℂ}
    {t : Fin m → ℂ} (hγ : ∀ p, ContDiffAt ℝ 2 (fun t' => γ t' p) t)
    (hP : ∀ᶠ t' in 𝓝 t, γ t' ∈ mcPts (mCoordIdeal y)) {a : Ω} {v : ℂ}
    (hv : IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y a (γ t) v) :
    ContDiffAt ℝ 2 (fun t' => valAt y a (γ t')) t ∧ valAt y a (γ t) = v ∧
      ∀ᶠ t' in 𝓝 t, IsValueAt y a (γ t') (valAt y a (γ t')) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hgv⟩ := hv
  have hG := contDiffAt_eval hγ (map (Int.castRingHom ℂ) g)
  have hH := contDiffAt_eval hγ (map (Int.castRingHom ℂ) h)
  have hval : ∀ᶠ t' in 𝓝 t, IsValueAt y a (γ t') (eval (γ t') (map (Int.castRingHom ℂ) g) /
      eval (γ t') (map (Int.castRingHom ℂ) h)) ∧ γ t' ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [hP, hH.continuousAt.eventually_ne hz] with t' h1 h2
    exact ⟨⟨d, g, h, hg, hh, hy, hyg, h2, rfl⟩, h1⟩
  have hev : ∀ᶠ t' in 𝓝 t, valAt y a (γ t') =
      eval (γ t') (map (Int.castRingHom ℂ) g) * (eval (γ t') (map (Int.castRingHom ℂ) h))⁻¹ := by
    filter_upwards [hval] with t' h1
    rw [valAt_eq h1.2 h1.1, div_eq_mul_inv]
  refine ⟨(hG.mul (hH.fun_inv hz)).congr_of_eventuallyEq hev, ?_, ?_⟩
  · rw [hev.self_of_nhds, hgv, mul_inv_cancel_right₀ hz]
  · filter_upwards [hval] with t' h1
    rw [valAt_eq h1.2 h1.1]
    exact h1.1

def datumValue {D : ComponentData II Ψ K ι Ω E} (H : HodgeData D) (c : (k : K) → ι k)
    (b : ∀ τ, Fin D.N → E τ) (u : Ω) (z : (Σ k, ι k) → ℂ) : ℝ :=
  ‖valAt D.y u z‖ * (∏ k, ‖z ⟨k, c k⟩‖ ^ H.aMu k) *
    ∏ τ, Real.sqrt (quotNormSq D.j_le_N (gramAt (D.h τ) (b τ) z))

end Chart

end MuWeightChartSmooth

end GroundTheory.Heights₂.Heights.LowerBoundFree
