import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicScalar.SizeBounds

theorem one_le_rdE (D : D7) : (1 : ℝ) ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow
  · have h := NumberField.discr_ne_zero D.host.E
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs h
  · positivity

theorem one_le_b (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) : 1 ≤ b := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes at h
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]
    show 0 < 2 * D.R.ord
    have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    omega
  obtain ⟨-, -, -, hb⟩ := h.1 τ
  have hq := (D.hc τ).gap_be i
  have hr : ((((D.R.t : ℚ) + 3) / 2 : ℚ) : ℝ) ≤ (((D.hc τ).e i - (D.hc τ).b i : ℚ) : ℝ) := by
    exact_mod_cast hq
  push_cast at hr
  have habs := abs_le.mp (hb i)
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  linarith [habs.1, habs.2]

theorem lam_bounds (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (τ : D.what₂.Tau) (n : ℕ) :
    -b ≤ ((Formalism.L2.NTheta.lamAt (D.hc τ) n : ℚ) : ℝ) + (((D.hc τ).e i : ℚ) : ℝ) ∧
      ((Formalism.L2.NTheta.lamAt (D.hc τ) n : ℚ) : ℝ) + (((D.hc τ).e i : ℚ) : ℝ) ≤ 3 * b := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes at h
  obtain ⟨he0, he2, hv, hb⟩ := h.1 τ
  have hb0 : (0 : ℝ) ≤ b := by linarith
  unfold Formalism.L2.NTheta.lamAt
  split_ifs with h1 h2
  · obtain ⟨hv0, hv1⟩ := hv ⟨n, h1⟩
    constructor <;> linarith
  · have habs := abs_le.mp (hb ⟨n - (D.R.k - 1), h2⟩)
    push_cast
    constructor <;> linarith [habs.1, habs.2]
  · push_cast
    constructor <;> linarith

theorem toNat_floor_le (x : ℚ) (c : ℝ) (hc : 0 ≤ c) (hx : (x : ℝ) ≤ c) : ((⌊x⌋.toNat : ℕ) : ℝ) ≤ c := by
  rcases le_or_gt ⌊x⌋ 0 with h0 | h0
  · rw [Int.toNat_of_nonpos h0]
    simpa using hc
  · have h1 : ((⌊x⌋.toNat : ℕ) : ℤ) = ⌊x⌋ := Int.toNat_of_nonneg h0.le
    have h2 : ((⌊x⌋.toNat : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast h1
    rw [h2]
    have h3 : ((⌊x⌋ : ℤ) : ℝ) ≤ ((x : ℚ) : ℝ) := by exact_mod_cast Int.floor_le x
    linarith

theorem aPl_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (p : ℕ) (τ : D.what₂.Tau) (n : ℕ) :
    (aPl D i p τ n : ℝ) ≤ 3 * b := by
  have hlam := (lam_bounds D i b h τ n).2
  have hb1 := one_le_b D i b h
  unfold aPl
  split_ifs with hn
  · apply toNat_floor_le _ _ (by linarith)
    push_cast
    have hnp : (n : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
    have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith
  · simp only [Nat.cast_zero]
    linarith

theorem aMi_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (p q : ℕ) (τ : D.what₂.Tau) (n : ℕ) :
    (aMi D i p q τ n : ℝ) ≤ 3 * b := by
  have hlam := (lam_bounds D i b h τ (p + (q - n) - 1)).1
  have hb1 := one_le_b D i b h
  unfold aMi
  split_ifs with hn
  · apply toNat_floor_le _ _ (by linarith)
    push_cast
    have hqn : (0 : ℝ) ≤ ((q - n : ℕ) : ℝ) := Nat.cast_nonneg _
    have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith
  · simp only [Nat.cast_zero]
    linarith

theorem degAt_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    (degAt D i σ ρ : ℝ) ≤ 3 * (D.R.r : ℝ) * b := by
  have hb1 := one_le_b D i b h
  have hi := i.isLt
  have hs := D.sp.W_sigval ((i : ℕ) + 1) (by omega) (by omega) (tauE D ρ)
  have hP : ∀ n, ((aPlAt D i σ ρ n : ℕ) : ℝ) ≤ 3 * b := fun n => aPl_le D i b h _ _ n
  have hM : ∀ n, ((aMiAt D i σ ρ n : ℕ) : ℝ) ≤ 3 * b := fun n => aMi_le D i b h _ _ _ n
  have h1 := Finset.sum_le_sum (s := Finset.range (pW D i ρ)) (fun n _ => hP n)
  have h2 := Finset.sum_le_sum (s := Finset.range (qW D i ρ)) (fun n _ => hM n)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1 h2
  have hr : (pW D i ρ : ℝ) + (qW D i ρ : ℝ) = (D.R.r : ℝ) := by
    have hn : pW D i ρ + qW D i ρ = D.R.r := by
      simp only [pW, qW, Wc, hs]
      unfold Formalism.BasicNotions.Ranks.sigW Formalism.BasicNotions.Ranks.r
      dsimp only
      omega
    exact_mod_cast hn
  unfold degAt
  push_cast
  calc _ ≤ (pW D i ρ : ℝ) * (3 * b) + (qW D i ρ : ℝ) * (3 * b) := add_le_add h1 h2
    _ = 3 * (D.R.r : ℝ) * b := by rw [← hr]; ring

theorem sizes : ∀ (D : D7) (i : Fin D.R.m) (b : ℝ), Sizes D i b → (5.5 : ℝ) ≤ Lp D b ∧ Real.log (D.R.nV : ℝ) ≤ Lp D b ∧ 0 ≤ b ∧ Real.log (3 * (D.R.r : ℝ) * b + 2) ≤ 2 * Lp D b ∧ ∀ (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), (degAt D i σ ρ : ℝ) ≤ 3 * (D.R.r : ℝ) * b := by
  intro D i b h
  have hb1 := one_le_b D i b h
  have hrd := one_le_rdE D
  have hnV : (1 : ℝ) ≤ (D.R.nV : ℝ) := by
    have h1 := D.R.t_odd.pos
    have h2 : 1 ≤ D.R.nV := by
      unfold Formalism.BasicNotions.Ranks.nV
      omega
    exact_mod_cast h2
  have hk5 : 5 ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    have := D.R.two_le_m
    omega
  have hrk : D.R.r ≤ 2 * D.R.k := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hk : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk5
  have hr2 : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by exact_mod_cast hrk
  have hgl := h.2
  have hg0 := hgl 0
  have hg1 := hgl 1
  set y : ℝ := (D.R.k : ℝ) * b with hy
  have hy5 : 5 ≤ y := by nlinarith
  have hy8 : y ^ 3 ≤ y ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hyy : 25 ≤ y * y := by nlinarith
  have hy3 : 25 * y ≤ y ^ 3 := by nlinarith [mul_le_mul_of_nonneg_right hyy (by linarith : (0 : ℝ) ≤ y)]
  have hyP : (390625 : ℝ) ≤ y ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hy5 8
    norm_num at this
    linarith
  have hg1' : (1 : ℝ) ≤ (D.host.g 1 : ℝ) := by linarith
  have hg0' : (0 : ℝ) ≤ (D.host.g 0 : ℝ) := Nat.cast_nonneg _
  have hbr : (1 : ℝ) ≤ b * D.host.rdE := one_le_mul_of_one_le_of_one_le hb1 hrd
  have hG : (D.host.g 0 : ℝ) ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := le_mul_of_one_le_right hg0' hg1'
  have hA : (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) :=
    le_mul_of_one_le_left (by positivity) hbr
  have hB : b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤
      b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) :=
    le_mul_of_one_le_right (by positivity) hnV
  have hC : (1 : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by linarith
  have hD : (D.R.nV : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) :=
    le_mul_of_one_le_left (by positivity) hC
  have hX : y ^ 8 ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by linarith
  have hL : Lp D b = Real.log (b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ)) := rfl
  have hXpos : 0 < b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by linarith
  have he6 : Real.exp (5.5 : ℝ) ≤ 729 := by
    have h1 : Real.exp (5.5 : ℝ) ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
    have h2 : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 : Real.exp 1 ^ 6 ≤ (3 : ℝ) ^ 6 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) 6
    norm_num at h3
    linarith
  have h55 : (5.5 : ℝ) ≤ Lp D b := by
    rw [hL]
    calc (5.5 : ℝ) = Real.log (Real.exp 5.5) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith)
  refine ⟨h55, ?_, by linarith, ?_, fun σ ρ => degAt_le D i b h σ ρ⟩
  · rw [hL]
    exact Real.log_le_log (by linarith) hD
  · have hb0 : (0 : ℝ) ≤ b := by linarith
    have hrb : (D.R.r : ℝ) * b ≤ (2 * (D.R.k : ℝ)) * b := mul_le_mul_of_nonneg_right hr2 hb0
    have h32 : 3 * (D.R.r : ℝ) * b + 2 ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by
      nlinarith
    have hpos : 0 < 3 * (D.R.r : ℝ) * b + 2 := by positivity
    have hlog := Real.log_le_log hpos h32
    rw [← hL] at hlog
    linarith

end GlobalTheory.AdelicScalar.SizeBounds
