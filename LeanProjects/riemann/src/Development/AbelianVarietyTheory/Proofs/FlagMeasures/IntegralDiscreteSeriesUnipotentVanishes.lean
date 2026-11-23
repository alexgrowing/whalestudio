import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRepFormalDegreeBoundStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.RealFibre

private lemma eq_zero_of_sum_star_mul_const_mul_eq_zero {n : ℕ} (x : Fin n → ℂ) (c : ℂ) (hc : c ≠ 0)
    (h : ∑ i, star (x i) * (c * x i) = 0) : x = 0 := by
  have h1 : c * ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) = 0 := by
    rw [← h, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (Complex.normSq (x i) : ℂ) = star (x i) * x i := Complex.normSq_eq_conj_mul_self
    rw [e]; ring
  have h2 : ∑ i, Complex.normSq (x i) = 0 := by
    have h3 := (mul_eq_zero.mp h1).resolve_left hc
    exact_mod_cast h3
  funext i
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (x j))).mp h2 i
    (Finset.mem_univ i)
  simpa using h4

theorem one_le_rkR_of_isIsoC {n : ℕ} {ε : Fin n → Bool} {W : Submodule ℂ (Fin n → ℂ)} (hW : IsIsoC ε W) :
    1 ≤ rkR ε := by
  unfold IsIsoC herm Jm at hW
  obtain ⟨hne, hiso⟩ := hW
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hq := hiso x hxW x hxW

  have hall : ∀ b : Bool, ∃ i, ε i = b := by
    intro b
    by_contra hno
    push_neg at hno
    have hb : ∀ i, ε i = !b := fun i => by
      have h' := hno i
      cases hε : ε i <;> cases b <;> simp_all
    apply hx0
    apply eq_zero_of_sum_star_mul_const_mul_eq_zero x (if (!b) = true then (1 : ℂ) else -1) (by split_ifs <;> norm_num)
    rw [← hq]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, hb]
  obtain ⟨i, hi⟩ := hall true
  obtain ⟨j, hj⟩ := hall false
  unfold rkR
  apply le_min
  · exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  · exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

theorem decE_le_exp {q : ℕ} (hq : 1 ≤ q) {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    decE q h t ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt q) * t)) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hs1 : 1 ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hq)
  unfold decE
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  obtain ⟨s, hsd⟩ : ∃ s, s = Real.sqrt q := ⟨_, rfl⟩
  rw [← hsd] at hs hs1 ⊢
  have hs0 : s ≠ 0 := hs.ne'

  have key : t / s - min (2 * t ^ 2) (t / s) ≤ 1 := by
    rcases le_total (2 * t ^ 2) (t / s) with h' | h'
    · rw [min_eq_left h']
      obtain ⟨u, hu⟩ : ∃ u, u = t / s := ⟨_, rfl⟩
      rw [← hu]
      have ht : t = u * s := by rw [hu]; field_simp
      have h2 : t ^ 2 = u ^ 2 * s ^ 2 := by rw [ht]; ring
      have h1 : 0 ≤ u ^ 2 * (s ^ 2 - 1) := mul_nonneg (sq_nonneg u) (by nlinarith)
      nlinarith [sq_nonneg (u - 1 / 4)]
    · rw [min_eq_right h']; norm_num
  have e : h / (8 * s) * t = h / 8 * (t / s) := by ring
  rw [e]
  nlinarith [mul_nonneg hh (sub_nonneg.mpr key)]

theorem rate_lt {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) {h : ℝ}
    (hh : 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    0 ≤ h ∧ 12 * (n : ℝ) * q < h / (8 * Real.sqrt q) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hpow : (q : ℝ) ^ ((3 : ℝ) / 2) = q * Real.sqrt q := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hq0, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hpow] at hh
  have hP : 0 < (n : ℝ) * q * Real.sqrt q := by positivity
  refine ⟨by nlinarith, ?_⟩
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

private lemma list_prod_eq_take_mul_pair_mul_drop {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ℂ) (v : ι) :
    ∏ u, F u = F v * ∏ u ∈ Finset.univ.erase v, F u :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ v)).symm

private lemma rkR_le' {n : ℕ} (ε : Fin n → Bool) : rkR ε ≤ n := by
  unfold rkR
  calc min (Finset.univ.filter fun a => ε a = true).card (Finset.univ.filter fun a => ε a = false).card
      ≤ (Finset.univ.filter fun a => ε a = true).card := min_le_left _ _
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

theorem integral_phe_eq_zero : StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → LocDec B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → ∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0 := by
  classical
  intro hS B d h hD hL hh v Wv hW ν hν x y
  obtain ⟨hHC, hDS, hLow, hFd⟩ := hD v
  have hDS' := hDS
  obtain ⟨_, _, hU, _⟩ := hDS'
  obtain ⟨hw1, hwS⟩ := hLow
  have hq1 : 1 ≤ rkR (B.I.ε v) := one_le_rkR_of_isIsoC hW
  have hn1 : 1 ≤ B.I.n := le_trans hq1 (rkR_le' _)
  obtain ⟨h0, hc⟩ := rate_lt hn1 hq1 (hh v)

  obtain ⟨α, hαs, hαc, hαfix⟩ := exists_smooth_fix_lowKSub B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) hU
    (hS B.I.n (B.I.ε v) (B.lam v) hHC (B.H v) (B.σ v) hDS).1

  have hT := GlobalTheory.T.unitary_rep_matrixCoeff_integral_eq_zero B.I.n (B.I.ε v) Wv ν hW hν (B.H v) (B.σ v) (d v)
    (h / (8 * Real.sqrt (rkR (B.I.ε v) : ℝ))) α (B.w v) hU hFd hc hw1 hαs hαc
    (fun u => hαfix (B.w v) hwS u)
    ⟨Real.exp (h / 8), fun g => (hL v g).trans (decE_le_exp hq1 h0 _)⟩ (x.1 v) (y.1 v)
  have hstar : ∫ m, star ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ ∂ν = 0 := by
    refine (integral_conj (μ := ν)
      (f := fun m => ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ)).trans ?_
    rw [hT]; simp

  have hfun : ∀ m : UJ (B.I.ε v),
      phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) =
        ((((∏ u, d u : ℝ) : ℂ) * star (∏ u ∈ Finset.univ.erase v,
          ⟪B.w u, B.σ u (uMat (x.1 u * y.1 u)) (B.w u)⟫_ℂ)) * B.e (x.2 * y.2)) *
        star ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ := by
    intro m
    have hrest : ∏ u ∈ Finset.univ.erase v,
        ⟪B.w u, B.σ u (uMat (x.1 u * (open Classical in (Pi.mulSingle v m : B.I.Ginf)) u * y.1 u)) (B.w u)⟫_ℂ =
        ∏ u ∈ Finset.univ.erase v, ⟪B.w u, B.σ u (uMat (x.1 u * y.1 u)) (B.w u)⟫_ℂ :=
      Finset.prod_congr rfl fun u hu => by
        rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hu), mul_one]
    simp only [GlobalTheory.Count.phe, GlobalTheory.Count.ph, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_one]
    rw [list_prod_eq_take_mul_pair_mul_drop _ v, hrest, Pi.mulSingle_eq_same, star_mul']
    ring
  refine (integral_congr_ae (ae_of_all ν hfun)).trans ?_
  rw [integral_const_mul, hstar, mul_zero]

end GlobalTheory.RealFibre
