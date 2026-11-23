import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.SplitConst

def PB (X : ℝ) (k : ℕ) (a : ℝ) : Prop := 2 ≤ X ∧ 0 ≤ a ∧ a ≤ X ^ k

variable {X a b : ℝ} {i j : ℕ}

theorem PB.mono (h : PB X i a) (hij : i ≤ j) : PB X j a :=
  ⟨h.1, h.2.1, h.2.2.trans (pow_le_pow_right₀ (by linarith [h.1]) hij)⟩

theorem PB.of_le (h : PB X i a) (hb : 0 ≤ b) (hba : b ≤ a) : PB X i b := ⟨h.1, hb, hba.trans h.2.2⟩

theorem PB.add (h : PB X i a) (h' : PB X j b) : PB X (max i j + 1) (a + b) := by
  have h1 := (h.mono (le_max_left i j)).2.2
  have h2 := (h'.mono (le_max_right i j)).2.2
  have h3 : 0 ≤ X ^ max i j := pow_nonneg (by linarith [h.1]) _
  refine ⟨h.1, add_nonneg h.2.1 h'.2.1, ?_⟩
  rw [pow_succ]
  nlinarith [h.1]

theorem PB.mul (h : PB X i a) (h' : PB X j b) : PB X (i + j) (a * b) := by
  refine ⟨h.1, mul_nonneg h.2.1 h'.2.1, ?_⟩
  rw [pow_add]
  exact mul_le_mul h.2.2 h'.2.2 h'.2.1 (h.2.1.trans h.2.2)

theorem PB.pow (h : PB X i a) (n : ℕ) : PB X (i * n) (a ^ n) := by
  refine ⟨h.1, pow_nonneg h.2.1 _, ?_⟩
  rw [pow_mul]
  exact pow_le_pow_left₀ h.2.1 h.2.2 _

theorem PB.const (hX : 2 ≤ X) (k : ℕ) (ha : 0 ≤ a) (h : a ≤ 2 ^ k) : PB X k a :=
  ⟨hX, ha, h.trans (pow_le_pow_left₀ (by norm_num) hX _)⟩

theorem PB.base (hX : 2 ≤ X) (ha : 0 ≤ a) (h : a ≤ X) : PB X 1 a := ⟨hX, ha, by simpa using h⟩

theorem PB.sqrt (h : PB X i a) : PB X i (Real.sqrt a) := by
  refine ⟨h.1, Real.sqrt_nonneg _, ?_⟩
  have h1 : 1 ≤ X ^ i := one_le_pow₀ (by linarith [h.1])
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith [h.2.2]

theorem PB.log (h : PB X i a) (ha : 1 ≤ a) : PB X i (Real.log a) :=
  h.of_le (Real.log_nonneg ha) (by linarith [Real.log_le_sub_one_of_pos (show 0 < a by linarith)])

theorem PB.log_le {Z : ℝ} (h : PB (Real.exp Z) i a) (ha : 0 < a) : Real.log a ≤ i * Z := by
  have := Real.log_le_log ha h.2.2
  rwa [Real.log_pow, Real.log_exp] at this

theorem rpow_le_self {d s : ℝ} (hd : 1 ≤ d) (hs : 1 ≤ s) : d ^ (1 / s) ≤ d := by
  have := Real.rpow_le_rpow_of_exponent_le hd (show 1 / s ≤ 1 by rw [div_le_one (by linarith)]; exact hs)
  simpa using this

theorem isBoundedByPowerOfAtLeastTwo_inv_d4ep0 {g d f NA NC c w : ℝ} (hX : 2 ≤ X) (hg : 1 ≤ g) (hd : 1 ≤ d) (hf : 1 ≤ f) (hNA : 1 ≤ NA)
    (hNC : 1 ≤ NC) (hc : 0 < c) (hw : 1 ≤ w) (hg' : g ≤ X) (hd' : d ≤ X) (hf' : f ≤ X) (hNA' : NA ≤ X)
    (hNC' : NC ≤ X) (hc' : c ≤ X) (hw' : w ≤ X) : PB X 50 (flowEpsilonBound g d f NA NC c w)⁻¹ := by
  have pg := PB.base hX (by linarith) hg'
  have pd := PB.base hX (by linarith) hd'
  have pf := PB.base hX (by linarith) hf'
  have pNA := PB.base hX (by linarith) hNA'
  have pNC := PB.base hX (by linarith) hNC'
  have pc := PB.base hX hc.le hc'
  have pw := PB.base hX (by linarith) hw'
  have p1 : PB X 0 1 := PB.const hX 0 (by norm_num) (by norm_num)
  have p2 : PB X 1 2 := PB.const hX 1 (by norm_num) (by norm_num)
  have p4 : PB X 2 4 := PB.const hX 2 (by norm_num) (by norm_num)
  have prd : PB X 1 (d ^ (1 / (2 * f))) :=
    pd.of_le (Real.rpow_nonneg (by linarith) _) (rpow_le_self hd (by linarith))
  have pN0 := pg.mul (pd.pow 2)
  have pH := (pNC.pow 2).mul (p2.add (((p4.mul (pf.pow 4)).mul (prd.pow 2)).mul (pNA.pow 2)))
  have pK' := (pN0.mul pH).mul ((p2.mul pc).add p1)
  have pK := p1.add pK'
  have pN2 := p4.mul pf
  have pl := ((p2.mul pK).mul pN2).log (by nlinarith [pK'.2.1])
  have pR := ((pw.add (pN2.mul pl)).add pN2).add p2
  have pD := ((((pN0.pow 2).mul (pNC.pow 2)).mul pc).mul pR).mono (j := 50) (by norm_num)
  unfold flowEpsilonBound
  simp only []
  rcases min_choice (1 : ℝ) _ with h | h <;> rw [h]
  · rw [inv_one]; exact p1.mono (by norm_num)
  · rw [inv_div]
    refine pD.of_le (div_nonneg pD.2.1 (by positivity)) (div_le_self pD.2.1 (one_le_pow₀ hf))

theorem rh_inv {c w : ℝ} (hX : 2 ≤ X) (hc : 0 < c) (hw : 1 ≤ w) (hc' : c ≤ X) (hw' : w ≤ X) :
    PB X 8 (d6rh c w)⁻¹ := by
  have pc := PB.base hX hc.le hc'
  have pw := PB.base hX (by linarith) hw'
  have p12 : PB X 4 12 := PB.const hX 4 (by norm_num) (by norm_num)
  have ppi : PB X 2 Real.pi := PB.const hX 2 Real.pi_pos.le (by linarith [Real.pi_le_four])
  unfold d6rh
  rw [one_div, inv_inv]
  exact ((p12.mul ppi).mul (pc.add pw)).mono (by norm_num)

end GlobalTheory.SplitConst
