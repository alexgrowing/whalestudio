import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.Up
open Classical in

noncomputable def Wdiv {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X Xa.Fp x)) *
    ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
    ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0

noncomputable def Psdiv {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ) (x : Frame X.Ψ r) : ℝ :=
  phla X Xa.Fp x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)

def DivMetric : Prop := ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ), 1 ≤ n →
  IsMetricW X (Xa.Fp + n • Xa.L) (Wdiv X Xa Fl n) ∧ WLower X (Xa.Fp + n • Xa.L) (Wdiv X Xa Fl n) ∧
  ∀ x ∈ X.dom, (∃ k, Fl.s k x ≠ 0) → Wdiv X Xa Fl n x = ENNReal.ofReal (Real.exp (-Psdiv X Xa Fl n x))

def DivLevi : Prop := ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ), 1 ≤ n →
  ∀ x0, IsOrth X x0 → (∃ k0, ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0) ∧ ∀ k0 : Fin (nd X),
  ContDiffOn ℝ ∞ (fun z => Psdiv X Xa Fl n (cpt X x0 z)) {z | z ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 z) ≠ 0} ∧
  ∀ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0 → ∀ ξ : Fin (nd X) → ℂ,
    leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ ≤
      (leviV (nd X) (fun w => ((Psdiv X Xa Fl n (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re

def DivInFF : Prop := ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), FinMu X →
  ∀ x0, IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ (f g : Frame X.Ψ r → ℂ),
  X.IsSec (Xa.Fp + Xa.T • Xa.L) f → X.IsSec (Xa.Fp + Xa.T • Xa.L) g →
  ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) f (cpt X x0 z) ^ 2 *
    (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤ →
  (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (Xa.Fp + Xa.T • Xa.L) g x ^ 2 ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ Xa.T) →
  VanS X Fl.xs Fl.s (Xa.T - nd X) (fun x => f x - g x) →
  InFF X x0 (Wdiv X Xa Fl Xa.T) FF (fun x => f x - g x)

def DivUp : Prop := ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (x0 : Frame X.Ψ r), IsOrth X x0 →
  ∀ bb : ℝ, (∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
    bb * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ) →
  (∃ k0, ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0) →
  ∀ F : V (nd X) → ℂ, DifferentiableOn ℂ F (OmF X x0) → InAt X x0 (Wdiv X Xa Fl Xa.T) bb F →
  ∃ H : (Fin (nd X) → ℕ) → V (nd X) → ℂ,
    (∀ α, DifferentiableOn ℂ (H α) (OmF X x0) ∧ InAt X x0 (Wdiv X Xa Fl (nd X)) bb (H α)) ∧
    ∀ z ∈ OmF X x0, F z = ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
      monoM X Fl.s α (cpt X x0 z) * H α z

section API

variable {r : ℕ} {X : Data E r} (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ) {x : Frame X.Ψ r}

theorem Wdiv_of_mem (hx : x ∈ X.dom) :
    Wdiv X Xa Fl n x = ENNReal.ofReal (Real.exp (-phla X Xa.Fp x)) *
      ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  unfold Wdiv
  rw [if_pos hx]

theorem Wdiv_of_notMem (hx : x ∉ X.dom) : Wdiv X Xa Fl n x = 0 := by
  unfold Wdiv
  rw [if_neg hx]

theorem sum_normSq_pos {N : ℕ} {a : Fin N → ℂ} (h : ∃ k, a k ≠ 0) : 0 < ∑ k, ‖a k‖ ^ 2 := by
  obtain ⟨k, hk⟩ := h
  exact Finset.sum_pos' (fun _ _ => by positivity)
    ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hk) 2⟩

theorem sum_normSq_w_pos (hx : x ∈ X.dom) : 0 < ∑ k, ‖Xa.w k x‖ ^ 2 :=
  sum_normSq_pos (Xa.w_nz x hx)

theorem Wdiv_eq_exp (hx : x ∈ X.dom) (hs : ∃ k, Fl.s k x ≠ 0) :
    Wdiv X Xa Fl n x = ENNReal.ofReal (Real.exp (-Psdiv X Xa Fl n x)) := by
  have hw := sum_normSq_w_pos Xa hx
  have hs' : 0 < ∑ k, ‖Fl.s k x‖ ^ 2 := sum_normSq_pos hs
  rw [Wdiv_of_mem Xa Fl n hx, ENNReal.ofReal_rpow_of_pos hw, ENNReal.ofReal_rpow_of_pos hs',
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hw.le _)),
    Real.rpow_def_of_pos hw, Real.rpow_def_of_pos hs', ← Real.exp_add, ← Real.exp_add]
  congr 2
  unfold Psdiv
  ring

theorem Wdiv_eq_top (hn : 1 ≤ n) (hx : x ∈ X.dom) (hs : ∀ k, Fl.s k x = 0) :
    Wdiv X Xa Fl n x = ⊤ := by
  have hw := sum_normSq_w_pos Xa hx
  have hn' : -((n : ℝ) - 1 / 2) < 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h0 : ∑ k, ‖Fl.s k x‖ ^ 2 = 0 := by simp [hs]
  rw [Wdiv_of_mem Xa Fl n hx, h0, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg hn',
    ENNReal.ofReal_rpow_of_pos hw, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.mul_top]
  exact (ENNReal.ofReal_pos.2 (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hw _))).ne'

theorem phla_add_nsmul (hx : x ∈ X.dom) (la la' : Wt X.Ψ r) (k : ℕ) :
    phla X (la + k • la') x = phla X la x + k * phla X la' x := by
  rw [IW.phla_eq X hx, IW.phla_eq X hx, IW.phla_eq X hx, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem pnorm_sq_eq_exp (hx : x ∈ X.dom) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) :
    X.pnorm la P x ^ 2 = Real.exp (-phla X la x) * ‖P x‖ ^ 2 := by
  have hpos : 0 < X.nfac la x :=
    Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos
      (norm_pos_iff.2 (div_ne_zero (IW.dmin_ne_zero X hx τ _) (IW.dmin_ne_zero X hx τ _))) _
  have h : Real.exp (-phla X la x) = X.nfac la x ^ 2 := by
    unfold phla
    rw [show -(-2 * Real.log (X.nfac la x)) = Real.log (X.nfac la x) * ((2 : ℕ) : ℝ) by
      push_cast; ring, Real.exp_mul, Real.exp_log hpos, Real.rpow_natCast]
  rw [h]
  show (‖P x‖ * X.nfac la x) ^ 2 = _
  ring

theorem Wdiv_eq_pnorm (hx : x ∈ X.dom) :
    Wdiv X Xa Fl n x = ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + n • Xa.L) x)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  have ha := Real.exp_pos (-phla X Xa.L x)
  simp only [pnorm_sq_eq_exp hx, ← Finset.mul_sum]
  rw [Wdiv_of_mem Xa Fl n hx, ENNReal.ofReal_mul ha.le, ENNReal.ofReal_mul ha.le,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.ofReal_rpow_of_pos ha, ENNReal.ofReal_rpow_of_pos ha]
  have key : ENNReal.ofReal (Real.exp (-phla X Xa.Fp x)) =
      ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + n • Xa.L) x)) *
        ENNReal.ofReal (Real.exp (-phla X Xa.L x) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (Real.exp (-phla X Xa.L x) ^ (-((n : ℝ) - 1 / 2))) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ha.le _)),
      ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add, phla_add_nsmul hx]
    congr 2
    ring
  rw [key]
  ring

example (j : Fin Fl.δ) : Wdiv X Xa Fl Xa.T (Fl.xs j) = ⊤ := by
  have h2 := Xa.n_ge
  have hT := Xa.T_ge
  refine Wdiv_eq_top Xa Fl _ (by nlinarith) (Fl.xs_mem j) ?_
  refine (Fl.S_eq _ (Fl.xs_mem j)).2 ⟨j, 1, X.Γ.one_mem, fun _ => (1 : Matrix (Fin r) (Fin r) ℂ), ?_, ?_⟩
  · intro τ
    refine ⟨?_, fun a c h => Matrix.one_apply_ne h.ne'⟩
    show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · funext τ
    show Fl.xs j τ = ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      (mat (Fl.xs j) τ * (1 : Matrix (Fin r) (Fin r) ℂ))
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
    rfl

example (hx : x ∈ X.dom) (hs : ∀ k, Fl.s k x = 0) : Wdiv X Xa Fl 0 x = 0 := by
  have h0 : ∑ k, ‖Fl.s k x‖ ^ 2 = 0 := by simp [hs]
  rw [Wdiv_of_mem Xa Fl 0 hx, h0, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero]

example (hx : x ∈ X.dom) (hw : ∑ k, ‖Xa.w k x‖ ^ 2 = 1) (hs : ∑ k, ‖Fl.s k x‖ ^ 2 = 4) :
    Wdiv X Xa Fl 1 x = ENNReal.ofReal (Real.exp (-phla X Xa.Fp x) / 2) := by
  have h4 : (4 : ℝ) ^ (-(((1 : ℕ) : ℝ) - 1 / 2)) = 1 / 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [Wdiv_of_mem Xa Fl 1 hx, hw, hs, ENNReal.ofReal_one, ENNReal.one_rpow, mul_one,
    ENNReal.ofReal_rpow_of_pos (by norm_num), h4, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  ring

end API

end GlobalTheory.Up
