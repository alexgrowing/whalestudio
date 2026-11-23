import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

open Matrix Complex Filter Topology
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram

open GlobalTheory.HermFrame

variable {n a g : ℕ}

def polydisc (n : ℕ) (ρ : ℝ) : Set (Fin n → ℂ) := {z | ∀ k, ‖z k‖ < ρ}

def punctured (ha : a ≤ n) (ρ : ℝ) : Set (Fin n → ℂ) :=
  {z | z ∈ polydisc n ρ ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}

def tlog (w : ℂ) : ℝ := -Real.log ‖w‖ / (2 * Real.pi)

structure IsPeriodChart (rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) : Prop where

  rk_le : rk ≤ g

  holo : ∀ j k, DifferentiableOn ℂ (fun z => τ₀ z j k) (polydisc n 1)

  symm : ∀ z ∈ polydisc n 1, (τ₀ z).IsSymm

  psd : ∀ i, ((B i).map (Int.cast : ℤ → ℝ)).PosSemidef

  supp : ∀ i (j k : Fin g), (rk ≤ j.val ∨ rk ≤ k.val) → B i j k = 0

  toric : (((∑ i, B i).map (Int.cast : ℤ → ℝ)).submatrix
    (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef

  abelian : ∀ z ∈ polydisc n 1, (((τ₀ z).map Complex.im).submatrix
    (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef

def period (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (z : Fin n → ℂ) (L : Fin a → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  τ₀ z + ∑ i, (L i / (2 * Real.pi * I)) • (B i).map (Int.cast : ℤ → ℂ)

def imPeriod (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  (τ₀ z).map Complex.im + ∑ i, tlog (z (Fin.castLE ha i)) • (B i).map (Int.cast : ℤ → ℝ)

def hodgeGram (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (imPeriod ha τ₀ B z).map Complex.ofReal

def poincareGram (a : ℕ) (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun k =>
    ((if k.val < a then 1 / (2 * (‖z k‖ ^ 2 * tlog (z k) ^ 2)) else 1 / 2 : ℝ) : ℂ)

def BoundsOn (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ρ c C : ℝ) : Prop :=
  (∀ z ∈ punctured ha ρ, (imPeriod ha τ₀ B z - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) ∧
  (∀ z ∈ punctured ha ρ,
    ((C * (1 + ∑ i : Fin a, tlog (z (Fin.castLE ha i)))) • (1 : Matrix (Fin g) (Fin g) ℝ)
      - imPeriod ha τ₀ B z).PosSemidef) ∧
  OneFormBound (punctured ha ρ) (fun _ => 1) (poincareGram a) (conn (hodgeGram ha τ₀ B)) C ∧
  TwoFormBound (punctured ha ρ) (hodgeGram ha τ₀ B) (poincareGram a) (curv (hodgeGram ha τ₀ B)) C

def HodgeChartBounds : Prop :=
  ∀ (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ), IsPeriodChart rk τ₀ B →
    ∃ ρ c C : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ 0 < c ∧ BoundsOn ha τ₀ B ρ c C

open Matrix Complex Filter Topology in
open scoped ComplexOrder in
variable {n a g : ℕ} in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos {w : ℂ} (h0 : w ≠ 0) (h1 : ‖w‖ < 1) : 0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog w :=
  div_pos (neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr h0) h1)) (by positivity)

open Matrix Complex Filter Topology in
open scoped ComplexOrder in
variable {n a g : ℕ} in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.im_period (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) (L : Fin a → ℂ)
    (hL : ∀ i, exp (L i) = z (Fin.castLE ha i)) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period τ₀ B z L).map Complex.im = _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod ha τ₀ B z := by
  ext j k
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period, _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod, Matrix.map_apply, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply, Complex.add_im, Complex.im_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hL i, _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog, Complex.norm_exp, Real.log_exp]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [Complex.mul_im, Complex.div_re, Complex.div_im]
  simp [Complex.normSq_apply]
  field_simp

open Matrix Complex Filter Topology in
open scoped ComplexOrder in
variable {n a g : ℕ} in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.conn_hodgeGram {rk : ℕ} (ha : a ≤ n) {τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    {B : Fin a → Matrix (Fin g) (Fin g) ℤ} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B) {z : Fin n → ℂ}
    (hz : z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1) (ξ : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.conn (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B) z ξ =
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B z)⁻¹ * _root_.GlobalTheory.HermFrame.mdel (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B) z ξ := by
  apply _root_.GlobalTheory.HermFrame.conn_eq_of_isSymm
  have hnear : ∀ᶠ x in 𝓝 z, x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1 :=
    Filter.eventually_all.2 fun k =>
      (continuous_apply k).norm.continuousAt.eventually_lt continuousAt_const (hz k)
  filter_upwards [hnear] with x hx
  have hB : ∀ i, ((B i).map (Int.cast : ℤ → ℝ))ᵀ = (B i).map (Int.cast : ℤ → ℝ) := fun i => by
    have := (h.psd i).isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hτ : ((τ₀ x).map Complex.im)ᵀ = (τ₀ x).map Complex.im := by
    rw [← Matrix.transpose_map, (h.symm x hx).eq]
  have hI : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod ha τ₀ B x).IsSymm := by
    unfold Matrix.IsSymm _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod
    rw [Matrix.transpose_add, Matrix.transpose_sum, hτ]
    simp only [Matrix.transpose_smul, hB]
  exact hI.map _

end GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
