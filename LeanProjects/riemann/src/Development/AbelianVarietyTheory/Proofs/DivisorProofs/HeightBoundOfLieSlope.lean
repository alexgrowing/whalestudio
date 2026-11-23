import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSlopePointBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHeightStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointBoundStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaComparisonStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSaturatedStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHeightBoundedBelowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAbelDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedBasePt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianPeriodLatticeBasisSameSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLineHeightNeg
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeightParts.BdHtProof

open Finset

theorem sum_Icc_shift (f : ℕ → ℝ) (a n : ℕ) :
    ∑ l ∈ Icc (a + 1) (a + n), f l = ∑ k ∈ range n, f (a + 1 + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 by omega, Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    congr 2
    omega

theorem sum_Ico_telescope (lam : ℕ → ℝ) {a b : ℕ} (h : a ≤ b) :
    ∑ i ∈ Ico a b, (lam i - lam (i + 1)) = lam a - lam b := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [Finset.sum_Ico_succ_top hab, ih]; ring

theorem sum_fin_eq_Icc {N : ℕ} (g : Fin N → ℝ) :
    ∑ i, g i = ∑ l ∈ Icc 1 N, (if h : l - 1 < N then g ⟨l - 1, h⟩ else 0) := by
  have e := sum_Icc_shift (fun l => if h : l - 1 < N then g ⟨l - 1, h⟩ else 0) 0 N
  simp only [zero_add] at e
  rw [e, ← Fin.sum_univ_eq_sum_range (fun k => if h : 1 + k - 1 < N then g ⟨1 + k - 1, h⟩ else 0) N]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : 1 + (i : ℕ) - 1 = i := by omega
  simp only [hi, dif_pos i.2]

theorem abel_lower (N j : ℕ) (lam x : ℕ → ℝ) (hj : 1 ≤ j) (hjN : j < N)
    (hmon : ∀ i, 1 ≤ i → i < N → lam (i + 1) ≤ lam i) (hlam : ∀ i, 1 ≤ i → i ≤ N → |lam i| ≤ 2)
    (B C₂ : ℝ) (hB : 0 ≤ B) (hF : |∑ l ∈ Icc 1 N, x l| ≤ C₂)
    (h1 : ∀ i, 1 ≤ i → i ≤ j → -B ≤ -(∑ l ∈ Icc 1 i, x l))
    (h2 : ∀ i, j < i → i < N → -B ≤ ∑ l ∈ Icc (i + 1) N, x l) :
    -(4 * B) - 2 * C₂ ≤ -(∑ i ∈ Icc 1 N, lam i * x i) := by
  rw [GlobalTheory.weight_abel_decomposition N j lam x hj hjN]
  have c1 : ∑ i ∈ Ico 1 j, (lam i - lam (i + 1)) * (-B) ≤
      ∑ i ∈ Ico 1 j, (lam i - lam (i + 1)) * -(∑ l ∈ Icc 1 i, x l) :=
    Finset.sum_le_sum fun i hi => by
      simp only [Finset.mem_Ico] at hi
      exact mul_le_mul_of_nonneg_left (h1 i hi.1 hi.2.le) (sub_nonneg.2 (hmon i hi.1 (by omega)))
  have c2 : (lam j - lam (j + 1)) * (-B) ≤ (lam j - lam (j + 1)) * -(∑ l ∈ Icc 1 j, x l) :=
    mul_le_mul_of_nonneg_left (h1 j hj le_rfl) (sub_nonneg.2 (hmon j hj hjN))
  have c3 : ∑ i ∈ Ioo j N, (lam i - lam (i + 1)) * (-B) ≤
      ∑ i ∈ Ioo j N, (lam i - lam (i + 1)) * ∑ l ∈ Icc (i + 1) N, x l :=
    Finset.sum_le_sum fun i hi => by
      simp only [Finset.mem_Ioo] at hi
      exact mul_le_mul_of_nonneg_left (h2 i hi.1 hi.2) (sub_nonneg.2 (hmon i (by omega) hi.2))
  have hI : Ioo j N = Ico (j + 1) N := by ext i; simp only [Finset.mem_Ioo, Finset.mem_Ico]; omega
  rw [← Finset.sum_mul, sum_Ico_telescope lam hj] at c1
  rw [← Finset.sum_mul, hI, sum_Ico_telescope lam (show j + 1 ≤ N by omega)] at c3
  have l1 := abs_le.1 (hlam 1 le_rfl (by omega))
  have lN := abs_le.1 (hlam N (by omega) le_rfl)
  have t4 : |lam (j + 1) * ∑ l ∈ Icc 1 N, x l| ≤ 2 * C₂ := by
    rw [abs_mul]; exact mul_le_mul (hlam _ (by omega) (by omega)) hF (abs_nonneg _) (by norm_num)
  have t5 := le_abs_self (lam (j + 1) * ∑ l ∈ Icc 1 N, x l)
  have t6 : (lam 1 - lam N) * B ≤ 4 * B := mul_le_mul_of_nonneg_right (by linarith) hB
  rw [hI]
  linarith

end GlobalTheory.HeightParts.BdHtProof

namespace GlobalTheory.HeightParts.BdHtProof

open Finset GlobalTheory.ShFam GlobalTheory.ShFam.Pad ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem main : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → LieSlope → HtBdSt := by
  intro hP2 hPH hSW hLS D O hcore hN A T H hR
  choose Cc hCc using GlobalTheory.T.abelian_height_bounded_below hP2 hPH D O hcore
  obtain ⟨B0, hB0⟩ := (Set.finite_range Cc).bddAbove
  set C0 : ℝ := max B0 0 with hC0def
  have hAlow : ∀ y : Pt O.s, -C0 ≤ H.hA y := fun y => by
    rw [hR.ht.hA y]
    have h1 : ∀ c, Cc c ≤ C0 := fun c => (hB0 ⟨c, rfl⟩).trans (le_max_left _ _)
    exact (neg_le_neg (h1 _)).trans (hCc _ _ (HtTieRead.isClosed_basePt O y))
  obtain ⟨C1, hC1, hSt⟩ := GlobalTheory.T.lie_slope_point_bound hP2 hPH hLS (GlobalTheory.T.point_bound_statement hP2 hPH (GlobalTheory.T.torus_saturated_statement hP2))
    (GlobalTheory.T.omega_comparison_statement hP2 hPH) D O hcore hN A T H hR
  obtain ⟨C2, hFl⟩ := GlobalTheory.T.flat_height_statement hP2 hPH hSW D O hcore hN A T H hR
  have hDual := GlobalTheory.T.dual_line_height_neg D O hcore
  set nT : ℝ := (Fintype.card D.what₂.Tau : ℝ) with hnT
  have hnT0 : 0 ≤ nT := Nat.cast_nonneg _
  set C : ℝ := max (max 1 C0) (max C1 (4 * nT * C1 + 2 * nT * |C2|)) with hCdef
  have hCa : 1 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCb : C0 ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCc1 : C1 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCd : 4 * nT * C1 + 2 * nT * |C2| ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hCa, fun y => (neg_le_neg hCb).trans (hAlow y), fun u hu hnu y hy => ?_⟩
  obtain ⟨hAy, hsteps⟩ := hSt y hy

  obtain ⟨v, hv⟩ : ∃ v : D.what₂.Tau → Fin O.N → ℝ, v = u := ⟨u, rfl⟩
  have hdom : ∀ τ (a b : Fin O.N), a ≤ b → v τ b ≤ v τ a := fun τ a b h => by rw [hv]; exact hu τ a b h
  have hbd : ∀ τ (i : Fin O.N), |v τ i| ≤ 2 := fun τ i => by
    rw [hv]
    have := (norm_le_pi_norm (u τ) i).trans ((norm_le_pi_norm u τ).trans hnu)
    rwa [Real.norm_eq_abs] at this
  rw [← hv]
  clear hu hnu
  have hp : O.S.Dw.p = O.j := O.S.p_eq
  have hpq : O.S.Dw.p + O.S.Dw.q = O.N := O.S.rank_eq
  have hj1 := O.indef.1
  have hjN := O.indef.2
  have mτ : ∀ τ : D.what₂.Tau, O.S.Dw.mult (DV.tauEmb D τ) = O.S.Dw.p := fun τ => by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult
    rw [if_pos (O.A.cm τ)]
  have mc : ∀ τ : D.what₂.Tau, O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) = O.S.Dw.q := fun τ => by
    have := GlobalTheory.ShFam.Hor.PerBasis.mult_conj_add_mult O.S.Dw (DV.tauEmb D τ)
    rw [mτ τ] at this
    omega
  set c := compPt O.s y with hc
  set z := basePt O.Φ y with hz
  have hzc : IsClosed ({z} : Set (O.var c).X) := HtTieRead.isClosed_basePt O y

  set xx : D.what₂.Tau → ℕ → ℝ := fun τ l =>
    if h : l - 1 < O.N then (O.root0 c ∅ (τ, ⟨l - 1, h⟩)).ht z else 0 with hxx
  set lam : D.what₂.Tau → ℕ → ℝ := fun τ l => if h : l - 1 < O.N then v τ ⟨l - 1, h⟩ else 0 with hlam

  have E0 : H.h0 v y = ∑ τ, -(∑ l ∈ Icc 1 O.N, lam τ l * xx τ l) := by
    rw [hR.ht.h0 v y]
    unfold Setup.htWt
    rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [sum_fin_eq_Icc]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [hlam, hxx]
    split_ifs <;> first | rfl | (simp <;> rfl)
  have hF : ∀ τ, |∑ l ∈ Icc 1 O.N, xx τ l| ≤ C2 := by
    intro τ
    have h := (hFl τ y).1
    erw [hR.ht.h0] at h
    unfold Setup.htWt at h
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ, abs_neg, sum_fin_eq_Icc] at h
    · refine (le_of_eq ?_).trans h
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hxx]
      split_ifs <;> first | rfl | (simp <;> rfl)
    · intro τ' _ h'
      simp [h']
    · simp
  have S1 : ∀ τ, ∀ i, i ≤ O.j → -(∑ l ∈ Icc 1 i, xx τ l) = stepHt O (ref0 O) y (DV.tauEmb D τ) i := by
    intro τ i hi
    have e := sum_Icc_shift (xx τ) 0 i
    simp only [zero_add] at e
    rw [e]
    unfold stepHt
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have h1 : 1 + k - 1 < O.N := by omega
    have e1 : 1 + k - 1 = k := by omega
    have h2 : k < O.S.Dw.p := by omega
    simp only [hxx, dif_pos h1, Setup.root0, Setup.adl0, rootSym, Fin.val_mk, e1, if_pos h2]
    rfl
  have S2 : ∀ τ, ∀ i, O.j < i → i < O.N →
      ∑ l ∈ Icc (i + 1) O.N, xx τ l = stepHt O (ref0 O) y (conjEmb (DV.tauEmb D τ)) (O.N - i) := by
    intro τ i hi hiN
    have e := sum_Icc_shift (xx τ) i (O.N - i)
    rw [show i + (O.N - i) = O.N by omega] at e
    rw [e, ← Finset.sum_range_reflect (fun k => xx τ (i + 1 + k)) (O.N - i)]
    unfold stepHt
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have h1 : i + 1 + (O.N - i - 1 - k) - 1 < O.N := by omega
    have e1 : i + 1 + (O.N - i - 1 - k) - 1 = O.N - 1 - k := by omega
    have h2 : ¬ (O.N - 1 - k < O.S.Dw.p) := by omega
    have h3 : k < O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) := by rw [mc τ]; omega
    have h4 : O.S.Dw.p + O.S.Dw.q - 1 - (O.N - 1 - k) = k := by omega
    simp only [hxx, dif_pos h1, Setup.root0, Setup.adl0, rootSym, Fin.val_mk, e1, if_neg h2, h4]
    exact hDual c z hzc _ _ h3

  have hB0' : 0 ≤ C1 * Real.log (2 + C1 + H.hA y) + C1 := by
    have : 0 ≤ Real.log (2 + C1 + H.hA y) := Real.log_nonneg (by linarith)
    positivity
  have per : ∀ τ, -(4 * (C1 * Real.log (2 + C1 + H.hA y) + C1)) - 2 * C2 ≤
      -(∑ l ∈ Icc 1 O.N, lam τ l * xx τ l) := by
    intro τ
    refine abel_lower O.N O.j (lam τ) (xx τ) hj1 hjN ?_ ?_ _ C2 hB0' (hF τ) ?_ ?_
    · intro i hi hiN
      have h1 : i + 1 - 1 < O.N := by omega
      have h2 : i - 1 < O.N := by omega
      simp only [hlam, dif_pos h1, dif_pos h2]
      exact hdom τ _ _ (by rw [Fin.mk_le_mk]; omega)
    · intro i hi hiN
      have h2 : i - 1 < O.N := by omega
      simp only [hlam, dif_pos h2]
      exact hbd τ _
    · intro i hi hij
      rw [S1 τ i hij]
      have := hsteps (DV.tauEmb D τ) i (by rw [mτ τ]; omega)
      linarith
    · intro i hi hiN
      rw [S2 τ i hi hiN]
      have := hsteps (conjEmb (DV.tauEmb D τ)) (O.N - i) (by rw [mc τ]; omega)
      linarith
  have hsum : nT * (-(4 * (C1 * Real.log (2 + C1 + H.hA y) + C1)) - 2 * C2) ≤ H.h0 v y := by
    rw [E0]
    have := Finset.sum_le_sum (s := Finset.univ) fun τ _ => per τ
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    rw [hnT]
    exact this
  have hL1 : 0 ≤ Real.log (2 + C1 + H.hA y) := Real.log_nonneg (by linarith)
  have hL : Real.log (2 + C1 + H.hA y) ≤ Real.log (2 + C + H.hA y) :=
    Real.log_le_log (by linarith) (by linarith)
  have a1 : 4 * nT * C1 ≤ C := by nlinarith [abs_nonneg C2]
  have a2 : 0 ≤ 4 * nT * C1 := by positivity
  have e1 : 4 * nT * C1 * Real.log (2 + C1 + H.hA y) ≤ C * Real.log (2 + C + H.hA y) :=
    (mul_le_mul_of_nonneg_left hL a2).trans (mul_le_mul_of_nonneg_right a1 (hL1.trans hL))
  have e2 : 2 * nT * C2 ≤ 2 * nT * |C2| := by
    have := le_abs_self C2
    nlinarith
  linarith

end GlobalTheory.HeightParts.BdHtProof

example : Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → LieSlope → HtBdSt := GlobalTheory.HeightParts.BdHtProof.main
