import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LogVandermondeBounds.HookGammaAmgmMultinomialBounds
import Formalism.GL3MeanSquares.TraceIntegralityResults

noncomputable section

namespace Formalism.MainNotions.flipTwoThree

section PA
open Formalism.BasicNotions NumberField Finset

section Use

open Formalism.HermitianLattices.TraceIntegrality Formalism.LogVandermondeBounds.flipTwoThree

theorem b_Wnum_one_le {n : ℕ} (lam : Fin (n + 1) → ℤ) (h : Antitone lam) : (1 : ℝ) ≤ (Wnum lam : ℝ) := by
  have h0 : lam (Fin.last n) ≤ lam 0 := h (Fin.zero_le _)
  have h0' : (lam (Fin.last n) : ℝ) ≤ lam 0 := by exact_mod_cast h0
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold Wnum
  push_cast
  linarith

theorem b_summin_nonneg {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) (h : Formalism.LogVandermondeBounds.flipTwoThree.Interlace lam nu) :
    (0 : ℝ) ≤ ∑ i, ((min (len lam i) (B0 lam nu) : ℤ) : ℝ) := by
  have hB : 0 ≤ B0 lam nu := Finset.sum_nonneg fun i _ => by have := (h.2 i).1; omega
  refine Finset.sum_nonneg fun i _ => ?_
  have h1 : 0 ≤ len lam i := by have := h.2 i; unfold len; omega
  exact_mod_cast le_min h1 hB

def Z3bd {n : ℕ} (c : ℝ) (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) (logT : ℝ) : ℝ :=
  -(degZ lam nu : ℝ) * logT
    + c * ((n : ℝ) + 1) * Real.log (Wnum lam : ℝ) * (∑ i, ((min (len lam i) (B0 lam nu) : ℤ) : ℝ))
    + Real.log (weylDim lam)

theorem b_Z3bd_le {n : ℕ} (c : ℝ) (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) (logT : ℝ) (h : Formalism.LogVandermondeBounds.flipTwoThree.Interlace lam nu) :
    Z3bd c lam nu logT ≤ MeanSquareTwistBound lam nu logT + (max c 1 - 1) * MeanSquareTwistBound lam nu 0 := by
  have hd := (Formalism.HermitianLattices.TraceIntegrality.third_zeta_dimension_bound n lam h.1).1
  have hld : 0 ≤ Real.log (weylDim lam) := Real.log_nonneg hd
  have hW : 0 ≤ Real.log (Wnum lam : ℝ) := Real.log_nonneg (b_Wnum_one_le lam h.1)
  have hS := b_summin_nonneg lam nu h
  set K := max c 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hKc : c ≤ K := le_max_left _ _
  set S := ∑ i, ((min (len lam i) (B0 lam nu) : ℤ) : ℝ) with hSdef
  set W := Real.log (Wnum lam : ℝ) with hWdef
  have key : c * ((n : ℝ) + 1) * W * S ≤ K * (2 * (n : ℝ) * W * S) := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have : S = 0 := by rw [hSdef]; simp
      rw [this]; simp
    · have hn : (1 : ℝ) ≤ n := by exact_mod_cast h0
      have hWS : 0 ≤ W * S := mul_nonneg hW hS
      have h1 : c * ((n : ℝ) + 1) ≤ K * (2 * n) := by
        have : K * ((n : ℝ) + 1) ≤ K * (2 * n) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        have h2 : c * ((n : ℝ) + 1) ≤ K * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right hKc (by linarith)
        linarith
      calc c * ((n : ℝ) + 1) * W * S = (c * ((n : ℝ) + 1)) * (W * S) := by ring
        _ ≤ (K * (2 * n)) * (W * S) := mul_le_mul_of_nonneg_right h1 hWS
        _ = _ := by ring
  unfold Z3bd MeanSquareTwistBound
  have h3 : 0 ≤ (K - 1) * Real.log (weylDim lam) := mul_nonneg (by linarith) hld
  nlinarith [key, h3]

theorem b_use : ∀ C₀ c : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (TT : Finset ι) (n : ℕ)
    (lam : ι → Fin (n + 1) → ℤ) (sg : ι → Fin n → ℤ) (A bt : ι → ℝ)
    (b' L logT eta S mt logP : ℝ),
    1 ≤ L → 0 ≤ logT → 0 ≤ b' → 0 ≤ eta → 0 ≤ S → 0 ≤ mt →
    (∀ ρ, Formalism.LogVandermondeBounds.flipTwoThree.Interlace (lam ρ) (sg ρ)) → (∀ ρ, Real.log (Wnum (lam ρ) : ℝ) ≤ C₀ * L) →
    (∀ ρ ∈ TT, bt ρ ≤ 2 * b') →
    (∀ ρ ∈ TT, (B0 (lam ρ) (sg ρ) : ℝ) ≤ bt ρ + eta + S) →
    (∀ ρ, ρ ∉ TT → (B0 (lam ρ) (sg ρ) : ℝ) ≤ eta + S) →
    (∀ ρ, ∃ X : Finset (Fin n), X.card ≤ 3 ∧ ((∑ i ∈ Xᶜ, len (lam ρ) i : ℤ) : ℝ) ≤ eta + S) →
    (∀ ρ ∈ TT, A ρ - bt ρ - C₀ * (S + eta + mt) ≤ (degZ (lam ρ) (sg ρ) : ℝ)) →
    (∀ ρ, ρ ∉ TT → -(S + eta) - C₀ * mt ≤ (degZ (lam ρ) (sg ρ) : ℝ)) →
    logP ≤ ∑ ρ, Z3bd c (lam ρ) (sg ρ) logT →
    logP ≤ -(∑ ρ ∈ TT, A ρ) * logT + C * TT.card * b' * (logT + ((n : ℝ) + 1) * L)
        + C * Fintype.card ι * (eta + 3 * S + mt) * (logT + ((n : ℝ) + 1) * L)
        + C * Fintype.card ι * ((n : ℝ) + 1) ^ 2 * L := by
  intro C₀ c hC₀
  obtain ⟨C1, hC1⟩ := Formalism.HermitianLattices.TraceIntegrality.third_zeta_application C₀ hC₀
  set K := max c 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  refine ⟨K * max C1 0, mul_nonneg (by linarith) (le_max_right _ _), ?_⟩
  intro ι _ _ TT n lam sg A bt b' L logT eta S mt logP hL hT hb he hS hmt hI hW hbt hB1 hB2 hX hd1 hd2 hP
  have u1 := hC1 ι TT n lam sg A bt b' L logT eta S mt _ hL hT hb he hS hmt hI hW hbt hB1 hB2 hX hd1 hd2 le_rfl
  have u0 := hC1 ι TT n lam sg A bt b' L 0 eta S mt _ hL le_rfl hb he hS hmt hI hW hbt hB1 hB2 hX hd1 hd2 le_rfl
  have hsum : ∑ ρ, Z3bd c (lam ρ) (sg ρ) logT ≤
      ∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT + (K - 1) * ∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun ρ _ => b_Z3bd_le c _ _ _ (hI ρ)
  set M := max C1 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM1 : C1 ≤ M := le_max_left _ _
  have hn : (0 : ℝ) ≤ ((n : ℝ) + 1) * L := by positivity
  set e1 := (TT.card : ℝ) * b' * (logT + ((n : ℝ) + 1) * L) with he1
  set e2 := (Fintype.card ι : ℝ) * (eta + 3 * S + mt) * (logT + ((n : ℝ) + 1) * L) with he2
  set e3 := (Fintype.card ι : ℝ) * ((n : ℝ) + 1) ^ 2 * L with he3
  set z1 := (TT.card : ℝ) * b' * (0 + ((n : ℝ) + 1) * L) with hz1
  set z2 := (Fintype.card ι : ℝ) * (eta + 3 * S + mt) * (0 + ((n : ℝ) + 1) * L) with hz2
  have p1 : 0 ≤ e1 := by positivity
  have p2 : 0 ≤ e2 := by positivity
  have p3 : 0 ≤ e3 := by positivity
  have q1 : 0 ≤ z1 := by positivity
  have q2 : 0 ≤ z2 := by positivity
  have r1 : z1 ≤ e1 := by
    rw [hz1, he1]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have r2 : z2 ≤ e2 := by
    rw [hz2, he2]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have v1 : ∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT ≤ -(∑ ρ ∈ TT, A ρ) * logT + M * (e1 + e2 + e3) := by
    have : C1 * (e1 + e2 + e3) ≤ M * (e1 + e2 + e3) := mul_le_mul_of_nonneg_right hM1 (by linarith)
    calc _ ≤ _ := u1
      _ = -(∑ ρ ∈ TT, A ρ) * logT + C1 * (e1 + e2 + e3) := by rw [he1, he2, he3]; ring
      _ ≤ _ := by linarith
  have v0 : ∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) 0 ≤ M * (e1 + e2 + e3) := by
    have h1 : C1 * (z1 + z2 + e3) ≤ M * (z1 + z2 + e3) := mul_le_mul_of_nonneg_right hM1 (by linarith)
    have h2 : M * (z1 + z2 + e3) ≤ M * (e1 + e2 + e3) := mul_le_mul_of_nonneg_left (by linarith) hM0
    calc _ ≤ _ := u0
      _ = C1 * (z1 + z2 + e3) := by rw [hz1, hz2, he3]; ring
      _ ≤ _ := by linarith
  have v2 : (K - 1) * ∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) 0 ≤ (K - 1) * (M * (e1 + e2 + e3)) :=
    mul_le_mul_of_nonneg_left v0 (by linarith)
  calc logP ≤ _ := hP
    _ ≤ _ := hsum
    _ ≤ -(∑ ρ ∈ TT, A ρ) * logT + M * (e1 + e2 + e3) + (K - 1) * (M * (e1 + e2 + e3)) := by linarith
    _ = _ := by rw [he1, he2, he3]; ring

end Use

end PA

section PB
open Formalism.BasicNotions NumberField Finset

def interlacingGapSum {N : ℕ} (lt : DomWeight N) (sg : DomWeight (N - 1)) : ℤ :=
  ∑ i : Fin (N - 1), (sg.w i - lt.w ⟨i.1 + 1, by omega⟩)

def leng {N : ℕ} (lt : DomWeight N) (i : Fin (N - 1)) : ℤ := lt.w ⟨i.1, by omega⟩ - lt.w ⟨i.1 + 1, by omega⟩

theorem b_dimV_eq {n : ℕ} (lam : Fin n → ℤ) : dimV lam = Formalism.HermitianLattices.TraceIntegrality.weylDim lam := by
  unfold dimV Formalism.HermitianLattices.TraceIntegrality.weylDim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  push_cast
  rfl

theorem b_spread_eq {n : ℕ} (lt : DomWeight (n + 1)) : lt.spread = Formalism.HermitianLattices.TraceIntegrality.Wnum lt.w := by
  unfold Formalism.BasicNotions.DomWeight.spread Formalism.HermitianLattices.TraceIntegrality.Wnum
  rw [dif_pos (Nat.succ_pos n)]
  have e0 : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) = 0 := Fin.ext (by simp)
  have e1 : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  rw [e0, e1]
  omega

theorem b_useN : ∀ C₀ c : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (TT : Finset ι) (N : ℕ)
    (lam : ι → DomWeight N) (sg : ι → DomWeight (N - 1)) (A bt : ι → ℝ)
    (b' L logT eta S mt logP : ℝ), 0 < N →
    1 ≤ L → 0 ≤ logT → 0 ≤ b' → 0 ≤ eta → 0 ≤ S → 0 ≤ mt →
    (∀ ρ (i : Fin (N - 1)), (sg ρ).w i ≤ (lam ρ).w ⟨i.1, by omega⟩ ∧ (lam ρ).w ⟨i.1 + 1, by omega⟩ ≤ (sg ρ).w i) →
    (∀ ρ, Real.log ((lam ρ).spread : ℝ) ≤ C₀ * L) →
    (∀ ρ ∈ TT, bt ρ ≤ 2 * b') →
    (∀ ρ ∈ TT, (interlacingGapSum (lam ρ) (sg ρ) : ℝ) ≤ bt ρ + eta + S) →
    (∀ ρ, ρ ∉ TT → (interlacingGapSum (lam ρ) (sg ρ) : ℝ) ≤ eta + S) →
    (∀ ρ, ∃ X : Finset (Fin (N - 1)), X.card ≤ 3 ∧ ((∑ i ∈ Xᶜ, leng (lam ρ) i : ℤ) : ℝ) ≤ eta + S) →
    (∀ ρ ∈ TT, A ρ - bt ρ - C₀ * (S + eta + mt) ≤ ((∑ i, (lam ρ).w i - ∑ i, (sg ρ).w i : ℤ) : ℝ)) →
    (∀ ρ, ρ ∉ TT → -(S + eta) - C₀ * mt ≤ ((∑ i, (lam ρ).w i - ∑ i, (sg ρ).w i : ℤ) : ℝ)) →
    logP ≤ ∑ ρ, (-((∑ i, (lam ρ).w i - ∑ i, (sg ρ).w i : ℤ) : ℝ) * logT +
      c * N * Real.log ((lam ρ).spread : ℝ) * (∑ i, ((min (leng (lam ρ) i) (interlacingGapSum (lam ρ) (sg ρ)) : ℤ) : ℝ)) +
      Real.log (dimV (lam ρ).w)) →
    logP ≤ -(∑ ρ ∈ TT, A ρ) * logT + C * TT.card * b' * (logT + (N : ℝ) * L)
        + C * Fintype.card ι * (eta + 3 * S + mt) * (logT + (N : ℝ) * L)
        + C * Fintype.card ι * (N : ℝ) ^ 2 * L := by
  intro C₀ c hC₀
  obtain ⟨C, hC0, hC⟩ := b_use C₀ c hC₀
  refine ⟨C, hC0, ?_⟩
  intro ι _ _ TT N lam sg A bt b' L logT eta S mt logP hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  intro hL hT hb he hS hmt hI hW hbt hB1 hB2 hX hd1 hd2 hP
  have := hC ι TT n (fun ρ => (lam ρ).w) (fun ρ => (sg ρ).w) A bt b' L logT eta S mt logP hL hT hb he hS hmt
    (fun ρ => ⟨(lam ρ).anti, fun i => ⟨(hI ρ i).2, (hI ρ i).1⟩⟩)
    (fun ρ => by rw [← b_spread_eq]; exact hW ρ) hbt hB1 hB2 hX hd1 hd2
    (by
      refine le_trans hP (le_of_eq (Finset.sum_congr rfl fun ρ _ => ?_))
      unfold Z3bd
      rw [← b_spread_eq, ← b_dimV_eq, Nat.cast_succ]
      rfl)
  push_cast
  exact this

end PB

section PC
open Formalism.BasicNotions NumberField Finset

theorem b_nums {D : D7} {T g1 g2 : ℕ} {Cn x b L b' Sc eta : ℝ} (h : Nums D T g1 g2 Cn x b L b' Sc eta) :
    1 ≤ L ∧ 0 ≤ Cn ∧ 4 ≤ b' ∧ b' ≤ b ∧ (D.R.N D.R.m : ℝ) ≤ b' ∧ Sc + eta + D.R.m * D.R.t ≤ b' ∧
      Real.log (x * b * D.host.v) ≤ L ∧ 8 ≤ x * b * D.host.v := by
  obtain ⟨hb, hL, -, -, -, hbb, hSc, heta, hSe, -, -, -, hd, hx, hv, hN⟩ := h
  have hx0 : 0 < x := by linarith
  have hbb' : b' ≤ b := by rwa [mul_div_cancel_left₀ b hx0.ne'] at hbb
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht1 : (1 : ℝ) ≤ D.R.t := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr D.R.t_odd.pos.ne'
  have hmt : (2 : ℝ) ≤ D.R.m * D.R.t := by nlinarith [mul_nonneg (sub_nonneg.2 hm2) (sub_nonneg.2 ht1)]
  have hq : 4 ≤ b' / x := by linarith
  have hb'4x : 4 * x ≤ b' := by rwa [le_div_iff₀ hx0] at hq
  have hb'0 : 0 ≤ b' := by linarith
  have hb'4 : 4 ≤ b' := by linarith
  have hdiv : b' / x ≤ b' := div_le_self hb'0 (by linarith)
  have h8 : 8 ≤ x * b * D.host.v := by
    have hxb : 16 ≤ x * b := by nlinarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x * b) (by linarith : (0 : ℝ) ≤ D.host.v - 1)]
  have hL1 : 1 ≤ L := by
    have h1 : (1 : ℝ) < Real.log 8 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact Real.exp_one_lt_d9.trans (by norm_num)
    have h2 : Real.log 8 ≤ Real.log (x * b * D.host.v) := Real.log_le_log (by norm_num) h8
    linarith
  have hCn : 0 ≤ Cn := by
    by_contra hc
    push_neg at hc
    have : Cn * L < 0 := mul_neg_of_neg_of_pos hc (by linarith)
    linarith [abs_nonneg (dlogL D 1)]
  have hNb : (D.R.N D.R.m : ℝ) ≤ b' := by
    have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
    have hm3 : (8 : ℝ) ≤ (D.R.m : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (D.R.m : ℝ) - 2)
        (by positivity : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 2 + 2 * D.R.m + 4)]
    have hA : (1 : ℝ) ≤ (1 + 2 * (2 * Cn + 4)) * (D.R.m : ℝ) ^ 3 := by
      nlinarith [mul_nonneg hCn (by positivity : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 3)]
    nlinarith [mul_nonneg (sub_nonneg.2 hA) hN0]
  exact ⟨hL1, hCn, hb'4, hbb', hNb, hSe.trans hdiv, hL, h8⟩

theorem b_lam_eq (D : D7) (u : D.what₂.Word) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (i : Fin (D.R.N j)) :
    (((D.fm u).lam j τ).w i : ℚ) = lamLiftN D u τ i := by
  rw [(D.fm u).lam_eq j hj τ i]
  unfold lamLiftN lamCol wJ
  by_cases h : i.1 < D.R.k
  · rw [dif_pos h, if_pos h, dif_pos h]
  · rw [dif_neg h, if_neg h, dif_pos (D.R.blk_lt hj i h)]

theorem b_mem_tops (D : D7) (τ : D.what₂.Tau) : τ ∈ tops D ↔ IsTop D τ := by
  classical
  simp only [tops, topsOf, IsTop, plc, Finset.mem_filter, Finset.mem_univ, true_and]

theorem b_card_tops (D : D7) : (tops D).card = D.host.TT.card := by
  classical
  have hF := Formalism.BasicNotions.factTopsThick D.R D.host
  rw [← hF.2.2.2.1]
  symm
  refine Finset.card_bij (fun g hg => D.eTau.symm ⟨g, hF.1 g hg⟩) ?_ ?_ ?_
  · intro g hg
    rw [b_mem_tops]
    unfold IsTop plc
    rw [Equiv.apply_symm_apply]
    exact hg
  · intro g hg g' hg' h
    exact congrArg Subtype.val (D.eTau.symm.injective h)
  · intro τ hτ
    rw [b_mem_tops] at hτ
    refine ⟨plc D τ, hτ, ?_⟩
    apply D.eTau.injective
    rw [Equiv.apply_symm_apply]
    rfl

theorem b_wJ_le {D : D7} {u : D.what₂.Word} {T g1 g2 : ℕ} {Cn x b L b' Sc eta : ℝ}
    (h : Nums D T g1 g2 Cn x b L b' Sc eta) (hw : Wts D u Cn x b b' Sc eta) (τ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) :
    (wJ D u τ j : ℝ) ≤ 2 * b := by
  obtain ⟨hL1, hCn, hb4, hbb, hN, hsm, -, -⟩ := b_nums h
  have hSc : 1 ≤ Sc := h.2.2.2.2.2.2.1
  have hmt : (0 : ℝ) ≤ D.R.m * D.R.t := by positivity
  obtain ⟨-, -, -, -, h5, h6, -, -⟩ := hw τ
  by_cases ht : IsThick D τ
  · have := (h6 ht j hj).2
    linarith
  · have := h5 ht j hj
    linarith

theorem b_spread_pos {N : ℕ} (hN : 0 < N) (lt : DomWeight N) : (1 : ℝ) ≤ (lt.spread : ℝ) := by
  have hs : (1 : ℤ) ≤ lt.spread := by
    unfold Formalism.BasicNotions.DomWeight.spread
    rw [dif_pos hN]
    have h0 := lt.2 (show (⟨0, hN⟩ : Fin N) ≤ ⟨N - 1, by omega⟩ from Fin.mk_le_mk.2 (Nat.zero_le _))
    omega
  exact_mod_cast hs

theorem b_log_spread {D : D7} {u : D.what₂.Word} {T g1 g2 : ℕ} {Cn x b L b' Sc eta : ℝ}
    (h : Nums D T g1 g2 Cn x b L b' Sc eta) (hw : Wts D u Cn x b b' Sc eta) (τ : D.what₂.Tau) :
    Real.log (((D.fm u).lam D.R.m τ).spread : ℝ) ≤ (Real.log (Cn + 4) + 1) * L := by
  obtain ⟨hL1, hCn, hb4, hbb, hN, hsm, hL, h8⟩ := b_nums h
  have hx : 2 ≤ x := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv : 1 ≤ D.host.v := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have heta : 1 ≤ eta := h.2.2.2.2.2.2.2.1
  have hmt : (0 : ℝ) ≤ D.R.m * D.R.t := by positivity
  have hNp := D.R.N_pos D.R.m
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega

  have e0 : ((((D.fm u).lam D.R.m τ).w ⟨0, hNp⟩ : ℤ) : ℝ) = (lamCol D u τ 0 : ℝ) := by
    have := b_lam_eq D u D.R.m le_rfl τ ⟨0, hNp⟩
    unfold lamLiftN at this
    rw [if_pos hk] at this
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) this

  have hlast : ¬ (D.R.N D.R.m - 1 < D.R.k) := by
    unfold Ranks.N
    have : 1 ≤ D.R.m * (D.R.t + 1) := Nat.mul_pos hm (Nat.succ_pos _)
    omega
  have e1 : ((((D.fm u).lam D.R.m τ).w ⟨D.R.N D.R.m - 1, by omega⟩ : ℤ) : ℝ) =
      -(wJ D u τ ((D.R.N D.R.m - 1 - D.R.k) / (D.R.t + 1)) : ℝ) := by
    have := b_lam_eq D u D.R.m le_rfl τ ⟨D.R.N D.R.m - 1, by omega⟩
    unfold lamLiftN at this
    rw [if_neg hlast] at this
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) this
  have hw2 := b_wJ_le h hw τ _ (D.R.blk_lt le_rfl ⟨D.R.N D.R.m - 1, by omega⟩ hlast)
  have hl0 : (lamCol D u τ 0 : ℝ) ≤ (Cn + 2) * (x * b) := by
    obtain ⟨-, h2, h3, -⟩ := hw τ
    have hxb : 0 ≤ x * b := by nlinarith
    by_cases ht : IsTop D τ
    · have := (h2 ht).2.1
      nlinarith
    · have h4 := (h3 ht 0 hk).2
      have h5 : Cn * Sc ≤ Cn * (x * b) := mul_le_mul_of_nonneg_left (by nlinarith) hCn
      nlinarith
  have hsp : (((D.fm u).lam D.R.m τ).spread : ℝ) ≤ (Cn + 4) * (x * b * D.host.v) := by
    unfold DomWeight.spread
    rw [dif_pos hNp]
    push_cast
    rw [e0, e1]
    have hxb : 2 * b ≤ x * b := by nlinarith
    have h9 : (Cn + 4) * (x * b) ≤ (Cn + 4) * (x * b * D.host.v) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      nlinarith
    nlinarith
  have hpos := b_spread_pos hNp ((D.fm u).lam D.R.m τ)
  calc Real.log (((D.fm u).lam D.R.m τ).spread : ℝ) ≤ Real.log ((Cn + 4) * (x * b * D.host.v)) :=
        Real.log_le_log (by linarith) hsp
    _ = Real.log (Cn + 4) + Real.log (x * b * D.host.v) := Real.log_mul (by linarith) (by linarith)
    _ ≤ Real.log (Cn + 4) * L + 1 * L := by
        have : 0 ≤ Real.log (Cn + 4) := Real.log_nonneg (by linarith)
        nlinarith
    _ = _ := by ring

theorem b_ptB_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ ptB D u :=
  Finset.prod_nonneg fun _ _ => mul_nonneg (zpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)

theorem b_opSq_le_ptB (D : D7) (h6 : adm6 D) (u : D.what₂.Word) (hP : (D.fm u).PRat) (s : D.what₂.LL →+* ℂ) :
    opSq D ((D.fm u).lat D.R.m) (D.fm u).ptLat s ((D.fm u).PtL hP) ≤ ptB D u := by
  obtain ⟨h', hb⟩ := h6 u
  exact opNormAt_sq_le _ _ _ _ ((D.fm u).lat_good D.R.m).1 (InfinitePlace.mk s)
    (IsTotallyComplex.isComplex _) ((D.fm u).PtL hP) _ (b_ptB_nonneg D u) (hb (InfinitePlace.mk s))

theorem b_Tu_pos (D : D7) (u : D.what₂.Word) : (0 : ℝ) < (Tu D u : ℝ) := by
  exact_mod_cast (D.mem u).A.T_prime.pos

theorem b_ptB_le (D : D7) (u : D.what₂.Word) (Cn : ℝ) (hB : BeOnBd D u Cn) :
    ptB D u ≤ Real.exp (∑ τ, (-((D.fm u).deg τ : ℝ) * Real.log (Tu D u) +
      Cn * D.R.N D.R.m * Real.log (((D.fm u).lam D.R.m τ).spread : ℝ) *
        (∑ i, ((min (leng ((D.fm u).lam D.R.m τ) i) (interlacingGapSum ((D.fm u).lam D.R.m τ) ((D.fm u).sg τ)) : ℤ) : ℝ)) +
      Real.log (dimV ((D.fm u).lam D.R.m τ).w))) := by
  rw [Real.exp_sum]
  unfold ptB
  refine Finset.prod_le_prod (fun τ _ => mul_nonneg (zpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)) fun τ _ => ?_
  rw [add_assoc, Real.exp_add]
  refine mul_le_mul (le_of_eq ?_) (hB τ) (sq_nonneg _) (Real.exp_pos _).le
  rw [← Real.rpow_intCast, Real.rpow_def_of_pos (b_Tu_pos D u)]
  congr 1
  push_cast
  ring

theorem half_mul_succ_le_mul_of_odd (R : Ranks) : (((R.m * (R.t + 1) / 2 : ℕ) : ℤ) : ℝ) ≤ (R.m : ℝ) * R.t := by
  rcases R with ⟨F, k, m, t, hk, hm, ht⟩
  show (((m * (t + 1) / 2 : ℕ) : ℤ) : ℝ) ≤ (m : ℝ) * t
  have ht1 : 1 ≤ t := ht.pos
  have key : m * (t + 1) / 2 ≤ m * t := Nat.div_le_of_le_mul (by nlinarith [Nat.mul_le_mul_left m ht1])
  exact_mod_cast key

theorem b_deg_eq (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    ((D.fm u).deg τ : ℝ) = ((∑ i, ((D.fm u).lam D.R.m τ).w i - ∑ i, ((D.fm u).sg τ).w i : ℤ) : ℝ) -
      (((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ) : ℝ) := by
  unfold MemberForms.deg
  push_cast
  ring

theorem exists_projection_estimate (Cn : ℝ) : ∃ C : ℝ, ∀ (D : D7) (x : ℝ), ConditionalProjectionOperatorEstimate D Cn C x := by
  classical
  by_cases hCn : 0 ≤ Cn
  swap
  · refine ⟨0, fun D x _ u b L b' Sc eta hn => absurd (b_nums hn).2.1 hCn⟩
  have hlog : 0 ≤ Real.log (Cn + 4) := Real.log_nonneg (by linarith)
  obtain ⟨C, hC0, hC⟩ := b_useN (Cn + (Real.log (Cn + 4) + 1)) Cn (by linarith)
  refine ⟨C + 1, fun D x h6 u b L b' Sc eta hn hw hs hB hP s => ?_⟩
  obtain ⟨hL1, -, hb4, hbb, hN, hsm, hL, h8⟩ := b_nums hn
  have hSc : 1 ≤ Sc := hn.2.2.2.2.2.2.1
  have heta : 1 ≤ eta := hn.2.2.2.2.2.2.2.1
  have hmt : (0 : ℝ) ≤ D.R.m * D.R.t := by positivity
  set c0 : ℝ := (((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ) : ℝ) with hc0
  have hc0n : 0 ≤ c0 := by rw [hc0]; positivity
  have hc0m : c0 ≤ D.R.m * D.R.t := half_mul_succ_le_mul_of_odd D.R
  refine le_trans (b_opSq_le_ptB D h6 u hP s) (le_trans (b_ptB_le D u Cn hB) (Real.exp_le_exp.2 ?_))
  have key := hC D.what₂.Tau (tops D) (D.R.N D.R.m) ((D.fm u).lam D.R.m) (D.fm u).sg (aT D u) (bT D u)
    b' L (Real.log (Tu D u)) eta Sc (D.R.m * D.R.t) _ (D.R.N_pos _) hL1 (Real.log_natCast_nonneg _) (by linarith)
    (by linarith) (by linarith) hmt hs.1
    (fun τ => le_trans (b_log_spread hn hw τ) (mul_le_mul_of_nonneg_right (by linarith) (by linarith)))
    (fun τ hτ => ((hw τ).2.1 ((b_mem_tops D τ).1 hτ)).2.2.2.1.le)
    (fun τ hτ => ((hs.2 τ).1 ((b_mem_tops D τ).1 hτ)).1)
    (fun τ hτ => ((hs.2 τ).2.1 (fun h => hτ ((b_mem_tops D τ).2 h))).1)
    (fun τ => (hs.2 τ).2.2)
    (fun τ hτ => by
      have h1 := abs_le.1 ((hs.2 τ).1 ((b_mem_tops D τ).1 hτ)).2
      have h2 : Cn * (Sc + eta + D.R.m * D.R.t) ≤ (Cn + (Real.log (Cn + 4) + 1)) * (Sc + eta + D.R.m * D.R.t) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have h3 := h1.1
      rw [b_deg_eq] at h3
      linarith)
    (fun τ hτ => by
      have h1 := ((hs.2 τ).2.1 (fun h => hτ ((b_mem_tops D τ).2 h))).2
      have h2 : Cn * ((D.R.m : ℝ) * D.R.t) ≤ (Cn + (Real.log (Cn + 4) + 1)) * ((D.R.m : ℝ) * D.R.t) :=
        mul_le_mul_of_nonneg_right (by linarith) hmt
      rw [b_deg_eq] at h1
      linarith)
    le_rfl
  rw [b_card_tops, D.what₂.card_Tau, neg_mul, Finset.sum_mul] at key
  have hsum : ∑ τ, (-((D.fm u).deg τ : ℝ) * Real.log (Tu D u) +
        Cn * D.R.N D.R.m * Real.log (((D.fm u).lam D.R.m τ).spread : ℝ) *
          (∑ i, ((min (leng ((D.fm u).lam D.R.m τ) i) (interlacingGapSum ((D.fm u).lam D.R.m τ) ((D.fm u).sg τ)) : ℤ) : ℝ)) +
        Real.log (dimV ((D.fm u).lam D.R.m τ).w)) =
      ∑ τ, (-((∑ i, ((D.fm u).lam D.R.m τ).w i - ∑ i, ((D.fm u).sg τ).w i : ℤ) : ℝ) * Real.log (Tu D u) +
        Cn * D.R.N D.R.m * Real.log (((D.fm u).lam D.R.m τ).spread : ℝ) *
          (∑ i, ((min (leng ((D.fm u).lam D.R.m τ) i) (interlacingGapSum ((D.fm u).lam D.R.m τ) ((D.fm u).sg τ)) : ℤ) : ℝ)) +
        Real.log (dimV ((D.fm u).lam D.R.m τ).w)) + (D.R.f : ℝ) * (c0 * Real.log (Tu D u)) := by
    rw [← D.what₂.card_Tau, ← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [b_deg_eq]
    ring
  rw [hsum]
  have hlT : 0 ≤ Real.log (Tu D u : ℝ) := Real.log_natCast_nonneg _
  have hNL : 0 ≤ (D.R.N D.R.m : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have e1 : c0 * Real.log (Tu D u) ≤ (eta + 3 * Sc + D.R.m * D.R.t) * (Real.log (Tu D u) + D.R.N D.R.m * L) :=
    le_trans (mul_le_mul_of_nonneg_right (by linarith) hlT)
      (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  have e2 := mul_le_mul_of_nonneg_left e1 (Nat.cast_nonneg D.R.f : (0 : ℝ) ≤ (D.R.f : ℝ))
  have p1 : 0 ≤ (D.host.TT.card : ℝ) * b' * (Real.log (Tu D u) + D.R.N D.R.m * L) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by linarith)
  have p3 : 0 ≤ (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (by linarith)
  linarith

theorem stmtFP_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : ShareFamilyAtConstant Fm := by
  intro h6 Cn
  obtain ⟨C, hC⟩ := exists_projection_estimate Cn
  obtain ⟨x0, h0⟩ := h6
  exact ⟨C, x0, fun x hx hx1 i => hC _ x (h0 x hx hx1 i)⟩

end PC

section PD
open Formalism.BasicNotions NumberField Finset

theorem b_toEuc_mul {l m n : Type} [Fintype l] [Fintype m] [Fintype n] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    (A : Matrix l m ℂ) (B : Matrix m n ℂ) :
    Matrix.toEuclideanLin (A * B) = (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  apply LinearMap.ext
  intro x
  simp [Matrix.mulVec_mulVec]

theorem matrix_mul_factor_through_inv {l m n : Type} [Fintype l] [Fintype m] [Fintype n] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    (P : Matrix l l ℂ) (A : Matrix l m ℂ) (Y : Matrix m m ℂ) (B : Matrix m n ℂ) (Z : Matrix n n ℂ)
    (h : Y * Y⁻¹ = 1) : P * (A * B) * Z = (P * A * Y) * (Y⁻¹ * B * Z) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Y Y⁻¹ (B * Z), h, Matrix.one_mul]

theorem b_opNormAt_comp {K : Type} [Field K] [NumberField K] [StarRing K]
    {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]
    {U μ : Type} [AddCommGroup U] [Module K U] [Fintype μ] [DecidableEq μ]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Module.Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (b'' : Module.Basis μ K U) (X'' : InfinitePlace K → Matrix μ μ ℂ)
    (hX' : ∀ v, IsUnit (X' v).det) (v : InfinitePlace K) (φ : V →ₗ[K] W) (ψ : W →ₗ[K] U) :
    Formalism.HN.opNormAt b X b'' X'' v (ψ.comp φ) ≤ Formalism.HN.opNormAt b' X' b'' X'' v ψ * Formalism.HN.opNormAt b X b' X' v φ := by
  unfold Formalism.HN.opNormAt
  have h1 : (X'' v)⁻¹ * (LinearMap.toMatrix b b'' (ψ.comp φ)).map v.embedding * X v =
      ((X'' v)⁻¹ * (LinearMap.toMatrix b' b'' ψ).map v.embedding * X' v) *
        ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v) := by
    rw [LinearMap.toMatrix_comp b b' b'', Matrix.map_mul]
    exact matrix_mul_factor_through_inv _ _ _ _ _ (Matrix.mul_nonsing_inv _ (hX' v))
  rw [h1, b_toEuc_mul]
  have h2 : ∀ (f : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ μ) (g : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ),
      LinearMap.toContinuousLinearMap (f.comp g) =
        (LinearMap.toContinuousLinearMap f).comp (LinearMap.toContinuousLinearMap g) := fun f g => rfl
  rw [h2]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem b_opNormAt_id {K : Type} [Field K] [NumberField K] [StarRing K]
    {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    Formalism.HN.opNormAt b X b X v LinearMap.id ≤ 1 := by
  unfold Formalism.HN.opNormAt
  have h1 : (X v)⁻¹ * (LinearMap.toMatrix b b LinearMap.id).map v.embedding * X v = 1 := by
    rw [LinearMap.toMatrix_id, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ (hX v)]
  rw [h1]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  simp

theorem b_prod_places {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (a : InfinitePlace K → ℝ)
    (F : (K →+* ℂ) → ℝ) (ha : ∀ v, 0 ≤ a v) (h : ∀ s, a (InfinitePlace.mk s) ≤ Real.exp (F s)) :
    ∏ v, a v ≤ Real.exp ((Formalism.HN.nPl K : ℝ) * ((∑ s, F s) / (Fintype.card (K →+* ℂ) : ℝ))) := by
  classical
  have fib : ∀ G : InfinitePlace K → ℝ, ∏ s : K →+* ℂ, G (InfinitePlace.mk s) = ∏ v, G v ^ 2 := by
    intro G
    rw [← Finset.prod_fiberwise (s := Finset.univ) (g := fun s : K →+* ℂ => InfinitePlace.mk s)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => G v) (fun s hs => by rw [(Finset.mem_filter.1 hs).2]),
      Finset.prod_const, InfinitePlace.card_filter_mk_eq, IsTotallyComplex.mult_eq]
  have hcard : (Fintype.card (K →+* ℂ) : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by
    have h2 := fib (fun _ => Real.exp 1)
    rw [Finset.prod_const, Finset.prod_const, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul] at h2
    have h3 := Real.exp_injective h2
    simp only [Finset.card_univ, mul_one] at h3
    unfold Formalism.HN.nPl
    push_cast at h3 ⊢
    linarith
  have hn : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    unfold Formalism.HN.nPl
    exact_mod_cast Fintype.card_pos
  have h1 : (∏ v, a v) ^ 2 ≤ Real.exp (∑ s, F s) := by
    rw [← Finset.prod_pow, ← fib a, Real.exp_sum]
    exact Finset.prod_le_prod (fun s _ => ha _) fun s _ => h s
  have h2 : Real.exp (∑ s, F s) =
      Real.exp ((Formalism.HN.nPl K : ℝ) * ((∑ s, F s) / (Fintype.card (K →+* ℂ) : ℝ))) ^ 2 := by
    rw [← Real.exp_nat_mul, hcard]
    congr 1
    field_simp
    push_cast
    ring
  rw [h2] at h1
  exact (pow_le_pow_iff_left₀ (Finset.prod_nonneg fun v _ => ha v) (Real.exp_pos _).le (by norm_num)).1 h1

end PD

section PE
open Formalism.BasicNotions NumberField Finset

theorem b_opSqPl_nonneg (D : D7) (A B : HLat D.what₂.LL) (v : InfinitePlace D.what₂.LL) (φ : A.V →ₗ[D.what₂.LL] B.V) :
    0 ≤ opSqPl D A B v φ := sq_nonneg _

theorem b_opSqPl_comp (D : D7) (A B C : HLat D.what₂.LL) (hB : B.Good) (v : InfinitePlace D.what₂.LL)
    (φ : A.V →ₗ[D.what₂.LL] B.V) (ψ : B.V →ₗ[D.what₂.LL] C.V) :
    opSqPl D A C v (ψ.comp φ) ≤ opSqPl D B C v ψ * opSqPl D A B v φ := by
  unfold opSqPl
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (b_opNormAt_comp A.b A.X B.b B.X C.b C.X hB.1 v φ ψ) 2

theorem b_chain_le (D : D7) (u : D.what₂.Word) (hK : ∀ i, i < D.R.m → (D.fm u).KRat i)
    (v : InfinitePlace D.what₂.LL) (e : ℕ → ℝ)
    (h : ∀ i (hi : i < D.R.m),
      opSqPl D ((D.fm u).lat i) ((D.fm u).lat (i + 1)) v ((D.fm u).KL i (hK i hi)) ≤ Real.exp (e i)) :
    ∀ j (hj : j ≤ D.R.m), opSqPl D ((D.fm u).lat 0) ((D.fm u).lat j) v (chainL D u hK j hj) ≤
      Real.exp (∑ i ∈ Finset.range j, e i) := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [Finset.range_zero, Finset.sum_empty, Real.exp_zero]
    show Formalism.HN.opNormAt _ _ _ _ v LinearMap.id ^ 2 ≤ 1
    exact pow_le_one₀ (norm_nonneg _) (b_opNormAt_id _ _ ((D.fm u).lat_good 0).1 v)
  | succ j ih =>
    intro hj
    rw [Finset.sum_range_succ, add_comm (∑ x ∈ Finset.range j, e x) (e j), Real.exp_add]
    show opSqPl D _ _ v (((D.fm u).KL j (hK j hj)).comp (chainL D u hK j (Nat.le_of_succ_le hj))) ≤ _
    refine le_trans (b_opSqPl_comp D _ _ _ ((D.fm u).lat_good j) v _ _) ?_
    exact mul_le_mul (h j hj) (ih _) (b_opSqPl_nonneg _ _ _ _ _) (Real.exp_pos _).le

theorem b_N_lt (D : D7) {j : ℕ} (hj : j < D.R.m) : D.R.N j < D.R.N D.R.m :=
  Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hj (Nat.succ_pos _)) _

theorem b_N_le (D : D7) {j : ℕ} (hj : j ≤ D.R.m) : D.R.N j ≤ D.R.N D.R.m := by
  rcases eq_or_lt_of_le hj with h | h
  · rw [h]
  · exact (b_N_lt D h).le

theorem b_wJ_eq (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) {j : ℕ} (hj : j < D.R.m) :
    wJ D u τ j = -((((D.fm u).lam D.R.m τ).w ⟨D.R.N j, b_N_lt D hj⟩ : ℤ) : ℚ) := by
  rw [b_lam_eq D u D.R.m le_rfl τ ⟨D.R.N j, b_N_lt D hj⟩]
  unfold lamLiftN
  have h1 : ¬ (D.R.N j < D.R.k) := by unfold Ranks.N; omega
  have h2 : (D.R.N j - D.R.k) / (D.R.t + 1) = j := by
    unfold Ranks.N
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ (Nat.succ_pos _)]
  simp only [h1, if_false, h2, neg_neg]

theorem b_nu_int (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) {j : ℕ} (hj : j < D.R.m) (i : Fin (D.R.N j)) :
    ∃ z : ℤ, 0 ≤ z ∧ nuLift D u τ j i = z := by
  have hi : i.1 < D.R.N D.R.m := lt_trans i.2 (b_N_lt D hj)
  refine ⟨((D.fm u).lam D.R.m τ).w ⟨i.1, hi⟩ - ((D.fm u).lam D.R.m τ).w ⟨D.R.N j, b_N_lt D hj⟩, ?_, ?_⟩
  · have := ((D.fm u).lam D.R.m τ).anti (show (⟨i.1, hi⟩ : Fin (D.R.N D.R.m)) ≤ ⟨D.R.N j, b_N_lt D hj⟩ from
      Fin.mk_le_mk.2 i.2.le)
    omega
  · unfold nuLift
    rw [b_wJ_eq D u τ hj, ← b_lam_eq D u D.R.m le_rfl τ ⟨i.1, hi⟩]
    push_cast
    ring

def nuN (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (j : ℕ) : Fin (D.R.N j) → ℕ := fun i => ⌊nuLift D u τ j i⌋.toNat

theorem b_nuN_cast (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) {j : ℕ} (hj : j < D.R.m) (i : Fin (D.R.N j)) :
    ((nuN D u τ j i : ℕ) : ℝ) = (lamLiftN D u τ i : ℝ) + (wJ D u τ j : ℝ) := by
  obtain ⟨z, hz, he⟩ := b_nu_int D u τ hj i
  unfold nuN
  rw [he, Int.floor_intCast]
  have h1 : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast congrArg (fun y : ℤ => (y : ℝ)) (Int.toNat_of_nonneg hz)
  rw [h1]
  have h2 : ((nuLift D u τ j i : ℚ) : ℝ) = (z : ℝ) := by rw [he]; push_cast; rfl
  rw [← h2]
  unfold nuLift
  push_cast
  rfl

theorem b_nuN_anti (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) {j : ℕ} (hj : j < D.R.m) : Antitone (nuN D u τ j) := by
  intro i i' hii
  unfold nuN
  apply Int.toNat_le_toNat
  apply Int.floor_mono
  unfold nuLift
  have h := ((D.fm u).lam j τ).anti hii
  have h1 := b_lam_eq D u j hj.le τ i
  have h2 := b_lam_eq D u j hj.le τ i'
  have h3 : ((((D.fm u).lam j τ).w i' : ℤ) : ℚ) ≤ (((D.fm u).lam j τ).w i : ℤ) := by exact_mod_cast h
  rw [h1, h2] at h3
  linarith

theorem b_hook_eq {N : ℕ} (nu : Fin N → ℚ) (h : ∀ i, 0 ≤ ⌊nu i⌋) :
    hook nu = Formalism.LogVandermondeBounds.flipTwoThree.hookF (fun i => ⌊nu i⌋.toNat) := by
  unfold hook Formalism.LogVandermondeBounds.flipTwoThree.hookF
  congr 1
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  rw [Int.toNat_of_nonneg (h i), Int.toNat_of_nonneg (h j)]

theorem b_hook_nu (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) {j : ℕ} (hj : j < D.R.m) :
    hook (nuLift D u τ j) = Formalism.LogVandermondeBounds.flipTwoThree.hookF (nuN D u τ j) := by
  exact b_hook_eq _ fun i => by
    obtain ⟨z, hz0, hz⟩ := b_nu_int D u τ hj i
    rw [hz, Int.floor_intCast]
    exact hz0

theorem b_absQ_nu (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) {j : ℕ} (hj : j < D.R.m) :
    ((absQ (nuLift D u τ j) : ℚ) : ℝ) = ∑ i, ((nuN D u τ j i : ℕ) : ℝ) := by
  unfold absQ
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [b_nuN_cast D u τ hj i]
  unfold nuLift
  push_cast
  rfl

theorem b_placeTerm (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) {j : ℕ} (hj : j < D.R.m) (lo : ℝ) :
    Real.log (hook (nuLift D u τ j)) - (absQ (nuLift D u τ j) : ℝ) * lo =
      Formalism.HermitianLattices.TraceIntegrality.placeTerm (nuN D u τ j) lo := by
  unfold Formalism.HermitianLattices.TraceIntegrality.placeTerm
  rw [b_hook_nu D u τ hj, b_absQ_nu D u τ hj]

theorem b_wJ_mono {D : D7} {u : D.what₂.Word} {Cn x b b' Sc eta : ℝ} (hw : Wts D u Cn x b b' Sc eta) (τ : D.what₂.Tau)
    {j j' : ℕ} (hjj : j ≤ j') (hj' : j' < D.R.m) : wJ D u τ j ≤ wJ D u τ j' := by
  induction j', hjj using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact le_trans (ih (by omega)) ((hw τ).2.2.2.1 n hj')

theorem b_nu_tail {D : D7} {u : D.what₂.Word} {Cn x b b' Sc eta : ℝ} (hw : Wts D u Cn x b b' Sc eta) (τ : D.what₂.Tau)
    {j : ℕ} (hj : j < D.R.m) (i : Fin (D.R.N j)) (hi : ¬ i.1 < D.R.k) :
    ((nuN D u τ j i : ℕ) : ℝ) ≤ eta := by
  rw [b_nuN_cast D u τ hj i]
  unfold lamLiftN
  rw [if_neg hi]
  have hb := D.R.blk_lt hj.le i hi
  have h1 := b_wJ_mono hw τ (Nat.zero_le _) hb
  have h2 := b_wJ_mono hw τ (show j ≤ D.R.m - 1 by omega) (by omega)
  have h3 := (hw τ).2.2.2.2.2.2.2
  have h1' : (wJ D u τ 0 : ℝ) ≤ (wJ D u τ ((i.1 - D.R.k) / (D.R.t + 1)) : ℝ) := by exact_mod_cast h1
  have h2' : (wJ D u τ j : ℝ) ≤ (wJ D u τ (D.R.m - 1) : ℝ) := by exact_mod_cast h2
  push_cast at h3 ⊢
  linarith

end PE

section PF
open Formalism.BasicNotions NumberField Finset

theorem b_Z2N : ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (ι σ : Type) [Fintype ι] [DecidableEq ι] [Fintype σ] [Nonempty σ]
    (TT T2 : Finset ι) (N' N m : ℕ) (hN' : 0 < N') (nu : ι → Fin N' → ℕ) (A w : ι → ℕ)
    (a b' L logT logg logOm : ℝ) (logOms : ι → σ → ℝ) (logTh logK : σ → ℝ),
    Disjoint TT T2 → N' ≤ N → 1 ≤ L → Real.log a ≤ L → 1 ≤ b' → b' ≤ a → (N : ℝ) * L ≤ b' →
    0 ≤ logT → 0 ≤ logg → (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg) ≤ N * b' * L →
    (∀ τ, Antitone (nu τ)) →
    (∀ τ ∈ TT, a ≤ A τ ∧ (A τ : ℝ) ≤ 2 * a ∧ nu τ ⟨0, hN'⟩ = A τ + w τ ∧ (w τ : ℝ) ≤ 2 * b' ∧
      ∀ i, i ≠ ⟨0, hN'⟩ → (nu τ i : ℝ) ≤ (2 + C₀) * b') →
    (∀ τ, τ ∉ TT → τ ∉ T2 → ∀ i, (nu τ i : ℝ) ≤ (2 + C₀) * b') →
    (∀ τ, Formalism.HermitianLattices.TraceIntegrality.mean (logOms τ) = logOm) → |logOm| ≤ C₀ * L →
    Formalism.HermitianLattices.TraceIntegrality.mean logTh ≤ C₀ * Fintype.card ι * (N : ℝ) ^ 2 * L →
    (∀ s, logK s ≤ ∑ τ, Formalism.HermitianLattices.TraceIntegrality.placeTerm (nu τ) (logOms τ s) + logTh s
        + C₀ * Fintype.card ι * (m : ℝ) ^ 2 * (N : ℝ) ^ 2 * (L + logT + logg)) →
    Formalism.HermitianLattices.TraceIntegrality.mean logK ≤ ∑ τ ∈ TT, Formalism.HermitianLattices.TraceIntegrality.topTerm (A τ) logOm +
              ∑ τ ∈ T2, Formalism.HermitianLattices.TraceIntegrality.placeTerm (nu τ) logOm + C * Fintype.card ι * N * b' * L := by
  intro C₀ hC₀
  obtain ⟨C, hC⟩ := Formalism.HermitianLattices.TraceIntegrality.second_zeta_mean_bound C₀ hC₀
  refine ⟨C, ?_⟩
  intro ι σ _ _ _ _ TT T2 N' N m hN'
  obtain ⟨R, rfl⟩ : ∃ R, N' = R + 1 := ⟨N' - 1, by omega⟩
  intro nu A w a b' L logT logg logOm logOms logTh logK
  exact hC ι σ TT T2 R N m nu A w a b' L logT logg logOm logOms logTh logK

def thicks (D : D7) : Finset D.what₂.Tau := by
  classical
  exact Finset.univ.filter (fun τ => IsThick D τ)

theorem b_mem_thicks (D : D7) (τ : D.what₂.Tau) : τ ∈ thicks D ↔ IsThick D τ := by
  simp [thicks]

theorem b_top_not_thick (D : D7) (τ : D.what₂.Tau) (h : IsTop D τ) : ¬ IsThick D τ :=
  Finset.disjoint_left.1 (Formalism.BasicNotions.factTopsThick D.R D.host).2.2.1 h

theorem b_toNat_cast (q : ℚ) (h : ∃ z : ℤ, q = z) (h0 : 0 ≤ q) : ((⌊q⌋.toNat : ℕ) : ℝ) = (q : ℝ) := by
  obtain ⟨z, rfl⟩ := h
  have hz : (0 : ℤ) ≤ z := by exact_mod_cast h0
  rw [Int.floor_intCast]
  have h2 : ((z.toNat : ℤ) : ℝ) = (z : ℝ) := by rw [Int.toNat_of_nonneg hz]
  rw [Rat.cast_intCast, ← h2, Int.cast_natCast]

theorem b_coef {c C₀ X Y : ℝ} (h1 : |c| ≤ C₀) (hX : 0 ≤ X) (hXY : X ≤ Y) : c * X ≤ C₀ * Y := by
  nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self c)) hX, mul_nonneg (sub_nonneg.2 h1) hX,
    mul_nonneg ((abs_nonneg c).trans h1) (sub_nonneg.2 hXY)]

def Z1rhs (D : D7) (u : D.what₂.Word) (C2 L : ℝ) (i : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  (∑ τ, (Real.log (hook (nuLift D u τ i)) - (absQ (nuLift D u τ i) : ℝ) * Real.log (D.gx.Om τ s))) +
    Real.log (thetaLocalFactorAtIndex D u i s ^ 2) +
    C2 * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N (i + 1) : ℝ) ^ 2 *
      (L + Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1))

theorem b_meanK (Cn Cper Cth C2 : ℝ) : ∃ C : ℝ, ∀ (D : D7) (x : ℝ), adm1 D Cn Cper x → adm2 D Cn Cth x →
    ∀ (u : D.what₂.Word) (b L b' Sc eta : ℝ),
    Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta → Wts D u Cn x b b' Sc eta →
    ∀ j < D.R.m, (∑ s, Z1rhs D u C2 L j s) / (Fintype.card (D.what₂.LL →+* ℂ) : ℝ) ≤
      (∑ t ∈ tops D, (aT D u t * Real.log (aT D u t) - aT D u t - aT D u t * logOm D t)) + LOW D u j +
        C * D.R.f * D.R.N D.R.m * b' * L := by
  classical
  by_cases hCn : 0 ≤ Cn
  swap
  · exact ⟨0, fun D x _ _ u b L b' Sc eta hn => absurd (b_nums hn).2.1 hCn⟩
  set C₀ := Cn + 1 + |Cper| + |Cth| + |C2| with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  obtain ⟨C, hC⟩ := b_Z2N C₀ hC₀0
  refine ⟨C, fun D x h1 h2 u b L b' Sc eta hn hw j hj => ?_⟩
  obtain ⟨hL1, -, hb4, hbb, hN, hsm, hL, h8⟩ := b_nums hn
  have hb0 : 0 < b := hn.1
  have hSc : 1 ≤ Sc := hn.2.2.2.2.2.2.1
  have heta : 1 ≤ eta := hn.2.2.2.2.2.2.2.1
  have hx : 2 ≤ x := hn.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv : 1 ≤ D.host.v := hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlin := hn.2.2.2.2.2.2.2.2.2.2.1
  have hm2 := hn.2.2.2.2.2.2.2.2.2.2.2.1
  have hmt : (0 : ℝ) ≤ D.R.m * D.R.t := by positivity
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  have hlogT : 0 ≤ Real.log (Tu D u : ℝ) := Real.log_natCast_nonneg _
  have hlogg : 0 ≤ Real.log ((D.host.g 0 : ℝ) * D.host.g 1) := by
    rw [← Nat.cast_mul]; exact Real.log_natCast_nonneg _
  have hTau : Nonempty D.what₂.Tau := by
    apply Fintype.card_pos_iff.1
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; positivity
  obtain ⟨τ0⟩ := hTau
  have hxb : b ≤ x * b := by nlinarith
  have hxb0 : 0 ≤ x * b := by linarith
  have hloga : Real.log (x * b) ≤ L := by
    refine le_trans (Real.log_le_log (by nlinarith) ?_) hL
    nlinarith
  have hNj := D.R.N_pos j
  have hNN : (D.R.N j : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast b_N_le D hj.le
  have hNN1 : (D.R.N (j + 1) : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast b_N_le D hj
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  have key := hC D.what₂.Tau (D.what₂.LL →+* ℂ) (tops D) (thicks D) (D.R.N j) (D.R.N D.R.m) D.R.m hNj
    (fun τ => nuN D u τ j) (fun τ => ⌊lamCol D u τ 0⌋.toNat) (fun τ => ⌊wJ D u τ j⌋.toNat)
    (x * b) b' L (Real.log (Tu D u)) (Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) (logOm D τ0)
    (fun τ s => Real.log (D.gx.Om τ s)) (fun s => Real.log (thetaLocalFactorAtIndex D u j s ^ 2)) (Z1rhs D u C2 L j)
    (Finset.disjoint_left.2 fun τ h h' => b_top_not_thick D τ ((b_mem_tops D τ).1 h) ((b_mem_thicks D τ).1 h'))
    (b_N_le D hj.le) hL1 hloga (by linarith) (by linarith) (by linarith) hlogT hlogg hm2
    (fun τ => b_nuN_anti D u τ hj)
    (fun τ hτ => by
      have ht := (b_mem_tops D τ).1 hτ
      obtain ⟨w1, w2, -, -, w5, -, w7, -⟩ := hw τ
      obtain ⟨t1, t2, t3, t4, t5⟩ := w2 ht
      have hA : ((⌊lamCol D u τ 0⌋.toNat : ℕ) : ℝ) = (lamCol D u τ 0 : ℝ) :=
        b_toNat_cast _ (w1 0 hk) (by
          have : (0 : ℝ) ≤ (lamCol D u τ 0 : ℝ) := by linarith
          exact_mod_cast this)
      have hw0 : (b' : ℝ) ≤ (wJ D u τ j : ℝ) := by
        have h3 : (wJ D u τ 0 : ℝ) ≤ (wJ D u τ j : ℝ) := by exact_mod_cast b_wJ_mono hw τ (Nat.zero_le j) hj
        have h4 : -(lamCol D u τ (D.R.k - 1) : ℝ) ≤ (wJ D u τ 0 : ℝ) := by exact_mod_cast w7
        linarith
      have hW : ((⌊wJ D u τ j⌋.toNat : ℕ) : ℝ) = (wJ D u τ j : ℝ) :=
        b_toNat_cast _ ⟨-((D.fm u).lam D.R.m τ).w ⟨D.R.N j, b_N_lt D hj⟩, by rw [b_wJ_eq D u τ hj, Int.cast_neg]⟩ (by
          have : (0 : ℝ) ≤ (wJ D u τ j : ℝ) := by linarith
          exact_mod_cast this)
      have hw2 := w5 (b_top_not_thick D τ ht) j hj
      refine ⟨by rw [hA]; exact t1, by rw [hA]; exact t2, ?_, by rw [hW]; exact hw2, ?_⟩
      · have : ((nuN D u τ j ⟨0, hNj⟩ : ℕ) : ℝ) = ((⌊lamCol D u τ 0⌋.toNat + ⌊wJ D u τ j⌋.toNat : ℕ) : ℝ) := by
          rw [b_nuN_cast D u τ hj, Nat.cast_add, hA, hW]
          unfold lamLiftN
          rw [if_pos hk]
        exact_mod_cast this
      · intro i hi
        have hC2 : 3 * b' ≤ (2 + C₀) * b' := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          have := abs_nonneg Cper; have := abs_nonneg Cth; have := abs_nonneg C2
          linarith
        refine le_trans ?_ hC2
        by_cases hik : i.1 < D.R.k
        · rw [b_nuN_cast D u τ hj]
          unfold lamLiftN
          rw [if_pos hik]
          have hi0 : 0 < i.1 := Nat.pos_of_ne_zero fun h => hi (Fin.ext h)
          by_cases hl : i.1 < D.R.k - 1
          · have := (t5 i.1 hi0 hl).2
            linarith
          · have : i.1 = D.R.k - 1 := by omega
            rw [this]
            linarith
        · have := b_nu_tail hw τ hj i hik
          linarith)
    (fun τ hτ hτ' i => by
      have ht : ¬ IsTop D τ := fun h => hτ ((b_mem_tops D τ).2 h)
      have ht' : ¬ IsThick D τ := fun h => hτ' ((b_mem_thicks D τ).2 h)
      obtain ⟨-, -, w3, -, w5, -, -, -⟩ := hw τ
      have hC2 : (2 + Cn) * b' ≤ (2 + C₀) * b' := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        have := abs_nonneg Cper; have := abs_nonneg Cth; have := abs_nonneg C2
        linarith
      refine le_trans ?_ hC2
      by_cases hik : i.1 < D.R.k
      · rw [b_nuN_cast D u τ hj]
        unfold lamLiftN
        rw [if_pos hik]
        have h3 := (w3 ht i.1 hik).2
        have h4 := w5 ht' j hj
        have h5 : Cn * Sc ≤ Cn * b' := mul_le_mul_of_nonneg_left (by linarith) hCn
        linarith
      · have := b_nu_tail hw τ hj i hik
        nlinarith)
    (fun τ => h1.1 τ τ0)
    (le_trans (h1.2 u b L b' Sc eta hn τ0) (mul_le_mul_of_nonneg_right (by
      have := abs_nonneg Cth; have := abs_nonneg C2; have := le_abs_self Cper
      linarith) (by linarith)))
    (by
      refine le_trans (h2 u b L b' Sc eta hn j hj).2 ?_
      rw [D.what₂.card_Tau]
      have e1 : Cth * D.R.f * (D.R.N j : ℝ) * (D.R.N (j + 1) : ℝ) * L =
          Cth * (D.R.f * (D.R.N j : ℝ) * (D.R.N (j + 1) : ℝ) * L) := by ring
      have e2 : C₀ * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * L = C₀ * (D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * L) := by ring
      rw [e1, e2]
      refine b_coef (by
        have := abs_nonneg Cper; have := abs_nonneg C2
        linarith) (by positivity) ?_
      rw [pow_two, ← mul_assoc]
      gcongr)
    (fun s => by
      unfold Z1rhs
      rw [D.what₂.card_Tau, Finset.sum_congr rfl fun τ _ => b_placeTerm D u τ hj (Real.log (D.gx.Om τ s))]
      have e1 : C2 * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N (j + 1) : ℝ) ^ 2 *
          (L + Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) =
          C2 * (D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N (j + 1) : ℝ) ^ 2 *
          (L + Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1))) := by ring
      have e2 : C₀ * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) ^ 2 *
          (L + Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) =
          C₀ * (D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) ^ 2 *
          (L + Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1))) := by ring
      rw [e1, e2]
      have : C2 * (D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N (j + 1) : ℝ) ^ 2 *
          (L + Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1))) ≤
          C₀ * (D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) ^ 2 *
          (L + Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1))) := by
        refine b_coef (by
          have := abs_nonneg Cper; have := abs_nonneg Cth
          linarith) (by positivity) ?_
        gcongr
      linarith)
  rw [D.what₂.card_Tau] at key
  refine le_trans key (le_of_eq ?_)
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun τ hτ => ?_
    have ht := (b_mem_tops D τ).1 hτ
    obtain ⟨w1, w2, -⟩ := hw τ
    have hA : ((⌊lamCol D u τ 0⌋.toNat : ℕ) : ℝ) = (lamCol D u τ 0 : ℝ) :=
      b_toNat_cast _ (w1 0 hk) (by
        have : (0 : ℝ) ≤ (lamCol D u τ 0 : ℝ) := by have := (w2 ht).1; linarith
        exact_mod_cast this)
    unfold Formalism.HermitianLattices.TraceIntegrality.topTerm aT
    rw [hA, h1.1 τ τ0]
  · unfold LOW
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [b_placeTerm D u τ hj, h1.1 τ τ0]

end PF

section PG
open Formalism.BasicNotions NumberField Finset

def Prhs (D : D7) (u : D.what₂.Word) (CP L b' Sc eta : ℝ) : ℝ :=
  -(∑ t ∈ tops D, aT D u t * Real.log (Tu D u)) +
    CP * D.host.TT.card * b' * (Real.log (Tu D u) + D.R.N D.R.m * L) +
    CP * D.R.f * (eta + 3 * Sc + D.R.m * D.R.t) * (Real.log (Tu D u) + D.R.N D.R.m * L) +
    CP * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * L

theorem b_Prhs_le {D : D7} {u : D.what₂.Word} {Cn x b L b' Sc eta : ℝ} (CP : ℝ)
    (hn : Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta) :
    Prhs D u CP L b' Sc eta ≤ -(∑ t ∈ tops D, aT D u t * Real.log (Tu D u)) +
      |CP| * (4 * Cn + 5) * (D.R.f * D.R.m * D.R.N D.R.m * b' * L) := by
  obtain ⟨hL1, hCn, hb4, hbb, hN, hsm, hL, h8⟩ := b_nums hn
  have hSc : 1 ≤ Sc := hn.2.2.2.2.2.2.1
  have heta : 1 ≤ eta := hn.2.2.2.2.2.2.2.1
  have hT := hn.2.2.1
  have hlogT : 0 ≤ Real.log (Tu D u : ℝ) := Real.log_natCast_nonneg _
  have hm1 : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hN1 : (1 : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast D.R.N_pos D.R.m
  have hf0 : (0 : ℝ) ≤ D.R.f := by positivity
  have hmt : (0 : ℝ) ≤ D.R.m * D.R.t := by positivity
  have hTT : (D.host.TT.card : ℝ) ≤ D.R.f := by
    rw [← b_card_tops, ← D.what₂.card_Tau]
    exact_mod_cast Finset.card_le_univ _
  set f : ℝ := (D.R.f : ℝ)
  set m : ℝ := (D.R.m : ℝ)
  set N : ℝ := (D.R.N D.R.m : ℝ)
  set lT : ℝ := Real.log (Tu D u)
  set Y : ℝ := f * m * N * b' * L with hY
  have hmNL : 0 ≤ m * N * L := by positivity
  have hZ : lT + N * L ≤ (Cn + 1) * (m * N * L) := by
    have h1 : Cn * m * L ≤ Cn * (m * N * L) := by
      have : m * L ≤ m * N * L := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ m) (by linarith : (0:ℝ) ≤ L)]
      calc Cn * m * L = Cn * (m * L) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left this hCn
    have h2 : N * L ≤ m * N * L := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ N) (by linarith : (0:ℝ) ≤ L)]
    linarith
  have hZ0 : 0 ≤ lT + N * L := by positivity
  have p1 : (D.host.TT.card : ℝ) * b' * (lT + N * L) ≤ (Cn + 1) * Y := by
    calc (D.host.TT.card : ℝ) * b' * (lT + N * L) ≤ f * b' * ((Cn + 1) * (m * N * L)) := by gcongr
      _ = _ := by rw [hY]; ring
  have p2 : f * (eta + 3 * Sc + m * D.R.t) * (lT + N * L) ≤ 3 * (Cn + 1) * Y := by
    calc f * (eta + 3 * Sc + m * D.R.t) * (lT + N * L) ≤ f * (3 * b') * ((Cn + 1) * (m * N * L)) := by
          gcongr
          linarith
      _ = _ := by rw [hY]; ring
  have p3 : f * N ^ 2 * L ≤ Y := by
    calc f * N ^ 2 * L = f * 1 * N * N * L := by ring
      _ ≤ f * m * N * b' * L := by gcongr
  have q1 : 0 ≤ (D.host.TT.card : ℝ) * b' * (lT + N * L) := by positivity
  have q2 : 0 ≤ f * (eta + 3 * Sc + m * D.R.t) * (lT + N * L) := by positivity
  have q3 : 0 ≤ f * N ^ 2 * L := by positivity
  have r1 := b_coef (le_refl |CP|) q1 p1
  have r2 := b_coef (le_refl |CP|) q2 p2
  have r3 := b_coef (le_refl |CP|) q3 p3
  unfold Prhs
  calc _ = -(∑ t ∈ tops D, aT D u t * lT) + CP * ((D.host.TT.card : ℝ) * b' * (lT + N * L)) +
        CP * (f * (eta + 3 * Sc + m * D.R.t) * (lT + N * L)) + CP * (f * N ^ 2 * L) := by ring
    _ ≤ -(∑ t ∈ tops D, aT D u t * lT) + |CP| * ((Cn + 1) * Y) + |CP| * (3 * (Cn + 1) * Y) + |CP| * Y := by linarith
    _ = _ := by ring

theorem heckeValue_estimate_of_record_value (Cn Cd Cper Cth C2 CP : ℝ) : ∃ C : ℝ, ∀ (D : D7) (x : ℝ), adm1 D Cn Cper x → adm2 D Cn Cth x →
    Conclusion2 D Cn Cd C2 x → ProjectionOperatorEstimate D Cn CP x → Conclusion4 D Cn Cd C x := by
  obtain ⟨C, hC⟩ := b_meanK Cn Cper Cth C2
  refine ⟨|C| + |CP| * (4 * Cn + 5), fun D x h1 h2 hZ1 hPP u b L b' Sc eta hn hw hs hB hcl X hX1 hX2 hX3 hK hP => ?_⟩
  obtain ⟨hL1, hCn, hb4, hbb, hN, hsm, hL, h8⟩ := b_nums hn
  set F : (D.what₂.LL →+* ℂ) → ℝ := fun s => Prhs D u CP L b' Sc eta + ∑ j ∈ Finset.range D.R.m, Z1rhs D u C2 L j s with hF
  have hpt : ∀ s : D.what₂.LL →+* ℂ, opSqPl D ((D.fm u).lat 0) (D.fm u).ptLat (InfinitePlace.mk s)
      (((D.fm u).PtL hP).comp (chainL D u hK D.R.m le_rfl)) ≤ Real.exp (F s) := by
    intro s
    refine le_trans (b_opSqPl_comp D _ _ _ ((D.fm u).lat_good D.R.m) _ _ _) ?_
    rw [hF, Real.exp_add]
    refine mul_le_mul (hPP u b L b' Sc eta hn hw hs hB hP s) ?_ (b_opSqPl_nonneg _ _ _ _ _) (Real.exp_pos _).le
    exact b_chain_le D u hK (InfinitePlace.mk s) (fun j => Z1rhs D u C2 L j s)
      (fun i hi => hZ1 u b L b' Sc eta hn hw hcl X hX1 hX2 hX3 i hi (hK i hi) s) D.R.m le_rfl
  refine le_trans (b_prod_places _ F (fun v => b_opSqPl_nonneg _ _ _ _ _) hpt) (Real.exp_le_exp.2 ?_)
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hc : (Fintype.card (D.what₂.LL →+* ℂ) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (D.what₂.LL →+* ℂ) := Fintype.card_pos_iff.2 ⟨D.what₂.embLL⟩
    exact_mod_cast this.ne'
  have hmean : (∑ s, F s) / (Fintype.card (D.what₂.LL →+* ℂ) : ℝ) = Prhs D u CP L b' Sc eta +
      ∑ j ∈ Finset.range D.R.m, (∑ s, Z1rhs D u C2 L j s) / (Fintype.card (D.what₂.LL →+* ℂ) : ℝ) := by
    rw [hF, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_comm, add_div, Finset.sum_div, Finset.card_univ,
      nsmul_eq_mul, mul_div_cancel_left₀ _ hc]
  rw [hmean]
  have hsum : ∑ j ∈ Finset.range D.R.m, (∑ s, Z1rhs D u C2 L j s) / (Fintype.card (D.what₂.LL →+* ℂ) : ℝ) ≤
      ∑ j ∈ Finset.range D.R.m, ((∑ t ∈ tops D, (aT D u t * Real.log (aT D u t) - aT D u t - aT D u t * logOm D t)) +
        LOW D u j + C * D.R.f * D.R.N D.R.m * b' * L) :=
    Finset.sum_le_sum fun j hj => hC D x h1 h2 u b L b' Sc eta hn hw j (Finset.mem_range.1 hj)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum ⊢
  have hP' := b_Prhs_le CP hn
  have hY : 0 ≤ (D.R.f : ℝ) * D.R.m * D.R.N D.R.m * b' * L := by positivity
  have hCY : (D.R.m : ℝ) * (C * D.R.f * D.R.N D.R.m * b' * L) ≤ |C| * ((D.R.f : ℝ) * D.R.m * D.R.N D.R.m * b' * L) := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C) hY
    calc _ = C * ((D.R.f : ℝ) * D.R.m * D.R.N D.R.m * b' * L) := by ring
      _ ≤ _ := this
  have e : (|C| + |CP| * (4 * Cn + 5)) * D.R.f * D.R.m * D.R.N D.R.m * b' * L =
      |C| * ((D.R.f : ℝ) * D.R.m * D.R.N D.R.m * b' * L) +
        |CP| * (4 * Cn + 5) * ((D.R.f : ℝ) * D.R.m * D.R.N D.R.m * b' * L) := by ring
  rw [e]
  linarith

theorem familyPropZ_first_of_admissible {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h1 : admF1 Fm) (h2 : admF2 Fm) (hZ : ConclusionF2 Fm) (hP : FamilyProjectionEstimate Fm) :
    FamilyEstimateFour Fm := by
  intro Cn Cd
  obtain ⟨Cper, x1, a1⟩ := h1 Cn
  obtain ⟨Cth, x2, a2⟩ := h2 Cn
  obtain ⟨C2, x3, a3⟩ := hZ Cn Cd
  obtain ⟨CP, x4, a4⟩ := hP Cn
  obtain ⟨C, hC⟩ := heckeValue_estimate_of_record_value Cn Cd Cper Cth C2 CP
  refine ⟨C, max (max x1 x2) (max x3 x4), fun x hx hx1 i => ?_⟩
  have b1 : x1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have b2 : x2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have b3 : x3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have b4 : x4 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  exact hC _ x (a1 x b1 hx1 i) (a2 x b2 hx1 i) (a3 x b3 hx1 i) (a4 x b4 hx1 i)

end PG

section PH
open Formalism.BasicNotions NumberField Finset

def gDim (D : D7) (i : ℕ) : ℕ := D.R.f * D.R.N i * D.R.N (i + 1)

theorem b_card_Gx (D : D7) (i : ℕ) : Fintype.card (Gx D i) = gDim D i := by
  unfold gDim
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, D.what₂.card_Tau, mul_assoc]

theorem b_host_v_pos (D : D7) : 0 < D.host.v := by
  unfold Host.v Host.rdE
  have h : (0 : ℝ) < |(discr D.host.E : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have := Real.rpow_pos_of_pos h ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ))
  linarith

theorem b_one_le_f (D : D7) : 1 ≤ D.R.f := by
  unfold Ranks.f Ranks.n
  have := D.R.ord_pos
  omega

def toEuc (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (w : Gx D i → ℂ) : EuclideanSpace ℂ (Gx D i) :=
  WithLp.toLp 2 fun g => (((Real.sqrt (Real.pi * D.gx.Om g.1 s))⁻¹ : ℝ) : ℂ) * w g

theorem b_toEuc_sq (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (w : Gx D i → ℂ) :
    ‖toEuc D i s w‖ ^ 2 = Hq D i s w := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold Hq toEuc
  refine Finset.sum_congr rfl fun g _ => ?_
  have hp : 0 < Real.pi * D.gx.Om g.1 s := mul_pos Real.pi_pos (D.gx.Om_pos _ _)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, Real.sq_sqrt hp.le]
  field_simp

theorem b_toEuc_sub (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (w w' : Gx D i → ℂ) :
    toEuc D i s w - toEuc D i s w' = toEuc D i s (w - w') := by
  unfold toEuc
  ext g
  simp [mul_sub]

theorem b_finrank_Euc (D : D7) (i : ℕ) : Module.finrank ℝ (EuclideanSpace ℂ (Gx D i)) = 2 * gDim D i := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace, b_card_Gx]

def DiffNorm (D : D7) : Prop :=
  ∀ β : D.host.E, β ≠ 0 →
    (∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (β * (a : D.host.E)) = (n : ℚ)) →
    ((2 * D.host.v) ^ D.R.f)⁻¹ ≤ ∏ τ : D.what₂.Tau, ‖D.host.emb (plc D τ) β‖

theorem b_Hmin (D : D7) (hD : DiffNorm D) (i : ℕ) (s : D.what₂.LL →+* ℂ) (T : Torus D i s)
    (y : Gx D i → ℂ) (hy : y ∈ T.La) (h0 : y ≠ 0) : (D.R.f : ℝ) / D.host.v ≤ Hq D i s y := by
  obtain ⟨β, hβ, htr, hH⟩ := T.Hmin y hy h0
  rw [hH]
  let e : D.what₂.Tau ≃ Fin D.R.f := Fintype.equivFinOfCardEq D.what₂.card_Tau
  have h1 := Formalism.LogVandermondeBounds.flipTwoThree.amgm_period_lattice_bound D.R.f D.host.v (fun k => ‖D.host.emb (plc D (e.symm k)) β‖)
    (b_one_le_f D) (b_host_v_pos D)
    (fun k => norm_pos_iff.2 ((map_ne_zero _).2 hβ))
    (by
      rw [Equiv.prod_comp e.symm (fun τ => ‖D.host.emb (plc D τ) β‖)]
      exact hD β hβ htr)
  rwa [Equiv.sum_comp e.symm (fun τ => ‖D.host.emb (plc D τ) β‖)] at h1

theorem b_count (D : D7) (hD : DiffNorm D) (i : ℕ) (s : D.what₂.LL →+* ℂ) (T : Torus D i s) (u : Gx D i → ℂ)
    (r : ℝ) (hr : 0 ≤ r) (S : Finset T.La) (hS : ∀ y ∈ S, Hq D i s (u + (y : Gx D i → ℂ)) ≤ r) :
    (S.card : ℝ) ≤ 2 ^ gDim D i * (1 + 4 * r * D.host.v) ^ gDim D i := by
  classical
  have hv := b_host_v_pos D
  have hf : (0 : ℝ) < D.R.f := by exact_mod_cast b_one_le_f D
  have hfv : 0 < (D.R.f : ℝ) / D.host.v := div_pos hf hv
  have hinj : Set.InjOn (fun y : T.La => toEuc D i s (u + (y : Gx D i → ℂ))) S := by
    intro y _ y' _ h
    by_contra hne
    have h1 : ((y : Gx D i → ℂ) - y') ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.1 h))
    have h2 := b_Hmin D hD i s T _ (T.La.sub_mem y.2 y'.2) h1
    have h3 : toEuc D i s ((u + (y : Gx D i → ℂ)) - (u + (y' : Gx D i → ℂ))) = 0 := by
      rw [← b_toEuc_sub]; exact sub_eq_zero.2 h
    rw [add_sub_add_left_eq_sub] at h3
    rw [← b_toEuc_sq, h3] at h2
    simp at h2
    linarith
  have h := Formalism.HermitianLattices.TraceIntegrality.separated_set_packing_bound (EuclideanSpace ℂ (Gx D i))
    (S.image fun y : T.La => toEuc D i s (u + (y : Gx D i → ℂ))) (Real.sqrt r)
    (Real.sqrt ((D.R.f : ℝ) / D.host.v)) (Real.sqrt_pos.2 hfv) (Real.sqrt_nonneg _)
    (by
      intro c hc
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
      apply Real.le_sqrt_of_sq_le
      rw [b_toEuc_sq]; exact hS y hy)
    (by
      intro c hc d hd hcd
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hd
      have hne : y ≠ y' := fun h => hcd (by rw [h])
      have h1 : ((y : Gx D i → ℂ) - y') ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.1 h))
      have h2 := b_Hmin D hD i s T _ (T.La.sub_mem y.2 y'.2) h1
      rw [b_toEuc_sub, add_sub_add_left_eq_sub]
      apply Real.sqrt_le_iff.2 ⟨norm_nonneg _, ?_⟩
      rw [b_toEuc_sq]; exact h2)
  rw [Finset.card_image_of_injOn hinj, b_finrank_Euc] at h
  exact le_trans h (Formalism.HermitianLattices.TraceIntegrality.first_zeta_count D.R.f (gDim D i) r D.host.v (b_one_le_f D) hv hr)

theorem b_latsum (D : D7) (hD : DiffNorm D) (i : ℕ) (s : D.what₂.LL →+* ℂ) (T : Torus D i s) (u : Gx D i → ℂ) :
    Summable (fun y : T.La => Real.exp (-Real.pi * Hq D i s (u + (y : Gx D i → ℂ)))) ∧
    2 ^ gDim D i * ∑' y : T.La, Real.exp (-Real.pi * Hq D i s (u + (y : Gx D i → ℂ))) ≤
      4 ^ gDim D i * (2 + 8 * (gDim D i : ℝ) * D.host.v) ^ gDim D i := by
  classical
  have h := Formalism.HermitianLattices.TraceIntegrality.layer_cake_bound T.La (fun y => Hq D i s (u + (y : Gx D i → ℂ))) (gDim D i) D.host.v
    (b_host_v_pos D).le (fun y => by rw [← b_toEuc_sq]; positivity)
    (fun r hr => by
      have hfin : {y : T.La | Hq D i s (u + (y : Gx D i → ℂ)) ≤ r}.Finite := by
        by_contra hinf
        obtain ⟨S, hS, hc⟩ := Set.Infinite.exists_subset_card_eq hinf
          (⌈(2 : ℝ) ^ gDim D i * (1 + 4 * r * D.host.v) ^ gDim D i⌉₊ + 1)
        have h1 := b_count D hD i s T u r hr S (fun y hy => hS hy)
        rw [hc] at h1
        have h2 := Nat.le_ceil ((2 : ℝ) ^ gDim D i * (1 + 4 * r * D.host.v) ^ gDim D i)
        push_cast at h1
        linarith
      refine ⟨hfin, ?_⟩
      rw [Set.ncard_eq_toFinset_card _ hfin]
      exact b_count D hD i s T u r hr _ (fun y hy => by simpa using hy))
  exact ⟨h.1, h.2.2⟩

def SupUnfold (D : D7) : Prop :=
  ∀ (i : ℕ) (s : D.what₂.LL →+* ℂ) (T : Torus D i s) (Th : (Gx D i → ℂ) → ℂ), T.Admis Th → ∀ (B : ℝ),
    (∀ u, Summable (fun y : T.La => Real.exp (-Real.pi * Hq D i s (u + (y : Gx D i → ℂ)))) ∧
      ∑' y : T.La, Real.exp (-Real.pi * Hq D i s (u + (y : Gx D i → ℂ))) ≤ B) →
    ∀ z, dens D i s Th z ≤ 2 ^ gDim D i * B * T.l2Sq Th

theorem supBound_of_unfold_diffNorm (D : D7) (hU : SupUnfold D) (hD : DiffNorm D) : ThetaSupremumBound D := by
  intro i s T Th hA z
  have h2 : (0 : ℝ) < 2 ^ gDim D i := by positivity
  have h := hU i s T Th hA ((4 ^ gDim D i * (2 + 8 * (gDim D i : ℝ) * D.host.v) ^ gDim D i) / 2 ^ gDim D i)
    (fun u => ⟨(b_latsum D hD i s T u).1, by
      rw [le_div_iff₀ h2, mul_comm]; exact (b_latsum D hD i s T u).2⟩) z
  rw [mul_div_cancel₀ _ h2.ne'] at h
  exact h

end PH

section PI
open Formalism.BasicNotions NumberField Finset

theorem b_norm_dual {K : Type} [Field K] [NumberField K] (β : K) (hβ : β ≠ 0)
    (htr : ∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (β * (a : K)) = (n : ℚ)) :
    1 ≤ |Algebra.norm ℚ β| * |(discr K : ℚ)| := by
  classical
  have hmem : β ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0)]
    intro a ha
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨n, hn⟩ := htr a'
    exact ⟨n, by rw [Algebra.traceForm_apply]; exact hn.symm⟩
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) β ≤
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
    (FractionalIdeal.spanSingleton_le_iff_mem).2 hmem
  have hd0 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have hle1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) β *
      ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≤ 1 := by
    rw [coeIdeal_differentIdeal ℤ ℚ]
    calc _ ≤ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
          (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))⁻¹ :=
          mul_le_mul_left hle _
      _ = 1 := mul_inv_cancel₀ hd0
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle1
  have hJ0 : J ≠ ⊥ := by
    intro h
    rw [h, FractionalIdeal.coeIdeal_bot] at hJ
    have := mul_eq_zero.1 hJ.symm
    rcases this with h1 | h1
    · exact hβ (FractionalIdeal.spanSingleton_eq_zero_iff.1 h1)
    · exact differentIdeal_ne_bot ((FractionalIdeal.coeIdeal_eq_zero (K := K)).1 h1)
  have habs := congrArg FractionalIdeal.absNorm hJ
  rw [map_mul, FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm,
    FractionalIdeal.absNorm_span_singleton, NumberField.absNorm_differentIdeal (K := K)] at habs
  have hJ1 : (1 : ℚ) ≤ (Ideal.absNorm J : ℚ) := by
    have : 0 < Ideal.absNorm J := Nat.pos_of_ne_zero fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast this
  rw [habs] at hJ1
  have e : (((discr K).natAbs : ℕ) : ℚ) = |(discr K : ℚ)| := by
    rw [Nat.cast_natAbs]; push_cast; rfl
  rwa [e] at hJ1

theorem b_prod_emb {K : Type} [Field K] [NumberField K] (x : K) :
    ∏ φ : K →+* ℂ, ‖φ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  classical
  rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm,
    ← Finset.prod_fiberwise (s := Finset.univ) (g := fun φ : K →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_congr rfl (g := fun _ => v x) (fun φ hφ => by
      rw [← (Finset.mem_filter.1 hφ).2]; rfl),
    Finset.prod_const, InfinitePlace.card_filter_mk_eq]

theorem b_finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have hb := (factEmb D.R D.host).1
  have h1 : Nat.card (D.R.GG) = Nat.card (D.host.E →+* ℂ) := Nat.card_congr (Equiv.ofBijective _ hb)
  have h2 : Nat.card (D.host.E →+* ℂ) = Module.finrank ℚ D.host.E := by
    rw [Nat.card_eq_fintype_card]; exact NumberField.Embeddings.card D.host.E ℂ
  have h4 : Nat.card (D.R.GG) = 4 * D.R.ord := D.R.natCard_GG
  rw [← h2, ← h1, h4]
  simp only [Ranks.f, Ranks.n]
  ring

theorem b_two_v_pow (D : D7) : (2 * D.host.v) ^ (2 * D.R.f) = |(discr D.host.E : ℝ)| := by
  have h : (0 : ℝ) ≤ |(discr D.host.E : ℝ)| := abs_nonneg _
  have hf : ((2 * D.R.f : ℕ) : ℝ) ≠ 0 := by
    have := b_one_le_f D
    exact_mod_cast (by omega : 2 * D.R.f ≠ 0)
  unfold Host.v Host.rdE
  rw [b_finrank_host, mul_div_cancel₀ _ (two_ne_zero), ← Real.rpow_natCast, ← Real.rpow_mul h,
    one_div_mul_cancel hf, Real.rpow_one]

theorem b_prod_Tau_sq (D : D7) (β : D.host.E) :
    (∏ τ : D.what₂.Tau, ‖D.host.emb (plc D τ) β‖) ^ 2 = ∏ φ : D.host.E →+* ℂ, ‖φ β‖ := by
  classical
  have hE := factEmb D.R D.host
  have hC : ∀ φ : D.host.E →+* ℂ, φ ∈ D.host.cmType ↔ (starRingEnd ℂ).comp φ ∉ D.host.cmType :=
    D.host.der.cmType.1
  set Φ := D.host.cmType with hΦ
  have hA : ∏ τ : D.what₂.Tau, ‖D.host.emb (plc D τ) β‖ = ∏ φ ∈ Finset.univ.filter (fun φ => φ ∈ Φ), ‖φ β‖ := by
    refine Finset.prod_bij (fun τ _ => D.host.emb (plc D τ)) ?_ ?_ ?_ ?_
    · intro τ _
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hE.2 _).2 (D.eTau τ).2⟩
    · intro τ _ τ' _ h
      exact D.eTau.injective (Subtype.ext (hE.1.1 h))
    · intro φ hφ
      obtain ⟨g, rfl⟩ := hE.1.2 φ
      have hg := (hE.2 g).1 (Finset.mem_filter.1 hφ).2
      refine ⟨D.eTau.symm ⟨g, hg⟩, Finset.mem_univ _, ?_⟩
      unfold plc
      rw [Equiv.apply_symm_apply]
    · intro τ _
      rfl
  have hB : ∏ φ ∈ Finset.univ.filter (fun φ => ¬ φ ∈ Φ), ‖φ β‖ = ∏ φ ∈ Finset.univ.filter (fun φ => φ ∈ Φ), ‖φ β‖ := by
    refine Finset.prod_bij (fun φ _ => (starRingEnd ℂ).comp φ) ?_ ?_ ?_ ?_
    · intro φ hφ
      have h1 := (Finset.mem_filter.1 hφ).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      by_contra h2
      exact h1 ((hC φ).2 h2)
    · intro φ _ φ' _ h
      ext x
      have := congrArg (fun ψ : D.host.E →+* ℂ => (starRingEnd ℂ) (ψ x)) h
      simpa using this
    · intro φ hφ
      have h1 := (Finset.mem_filter.1 hφ).2
      refine ⟨(starRingEnd ℂ).comp φ, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hC φ).1 h1⟩, ?_⟩
      ext x
      simp
    · intro φ _
      simp
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun φ : D.host.E →+* ℂ => φ ∈ Φ), hB, ← hA, pow_two]

theorem diffNorm_holds (D : D7) : DiffNorm D := by
  intro β hβ htr
  have h1 := b_norm_dual β hβ htr
  have h2 : (1 : ℝ) ≤ |((Algebra.norm ℚ β : ℚ) : ℝ)| * |(discr D.host.E : ℝ)| := by
    have := (Rat.cast_le (K := ℝ)).2 h1
    push_cast at this
    exact this
  rw [← b_prod_emb, ← b_prod_Tau_sq, ← b_two_v_pow, pow_mul'] at h2
  have hv : 0 < (2 * D.host.v) ^ D.R.f := pow_pos (by have := b_host_v_pos D; linarith) _
  have hP : 0 ≤ ∏ τ : D.what₂.Tau, ‖D.host.emb (plc D τ) β‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  rw [← mul_pow] at h2
  have h3 : 1 ≤ (∏ τ : D.what₂.Tau, ‖D.host.emb (plc D τ) β‖) * (2 * D.host.v) ^ D.R.f := by
    by_contra hlt
    rw [not_le] at hlt
    have := pow_lt_one₀ (mul_nonneg hP hv.le) hlt (two_ne_zero)
    linarith
  rw [inv_le_iff_one_le_mul₀ hv]
  exact h3

theorem supBound_of_unfold (D : D7) (hU : SupUnfold D) : ThetaSupremumBound D := by
  exact supBound_of_unfold_diffNorm D hU (diffNorm_holds D)

end PI

section Z2
open Formalism.BasicNotions

theorem hook_eq_hookF {N : ℕ} (nu : Fin N → ℚ) (nn : Fin N → ℕ) (h : ∀ i, nu i = nn i) :
    hook nu = Formalism.LogVandermondeBounds.flipTwoThree.hookF nn := by
  rw [b_hook_eq nu (fun i => by rw [h i]; exact Int.floor_nonneg.2 (Nat.cast_nonneg _))]
  congr 1
  funext i
  simp [h i]

theorem propZ_second_holds : HookLengthFactorialBound := by
  intro N nu hint hanti
  choose nn hnn using hint
  have hf : ∀ i, ⌊nu i⌋ = (nn i : ℤ) := fun i => by rw [hnn i]; exact Int.floor_natCast _
  have hant : Antitone nn := by
    intro i j hij
    have := hanti hij
    rw [hnn i, hnn j] at this
    exact_mod_cast this
  rw [hook_eq_hookF nu nn hnn]
  simp only [hf, Int.toNat_natCast]
  cases N with
  | zero =>
    refine ⟨?_, fun h => absurd h (lt_irrefl _)⟩
    simp [Formalism.LogVandermondeBounds.flipTwoThree.hookF]
  | succ M =>
    obtain ⟨h1, h2, -⟩ := Formalism.LogVandermondeBounds.hook_gamma_amgm_multinomial_bounds.2.2.2.2.1 M nn hant
    have he : ∀ i : Fin (M + 1), nn i + (M + 1) - 1 - (i : ℕ) = nn i + M - i := fun i => by omega
    simp only [he]
    refine ⟨h1, fun h => ?_⟩
    have h0 : (nu ⟨0, h⟩ : ℝ) = (nn 0 : ℝ) := by
      have : nu ⟨0, h⟩ = nn 0 := hnn 0
      rw [this]; norm_cast
    rw [h0]
    have e1 : (((M + 1 : ℕ) : ℝ)) = (M : ℝ) + 1 := by push_cast; ring
    rw [e1, ← add_assoc]
    exact h2

end Z2

section Z56a
open Formalism.BasicNotions NumberField
open Formalism.HermitianLattices.TraceIntegrality (Numbers wt plus MeanSquareWeightBound)

def colAbs (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  ∑ i ∈ Finset.range D.R.k, (lamCol D u τ i : ℝ)

def colAbsP (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  ∑ i ∈ Finset.range D.R.k, ((lamCol D u τ i : ℝ) - (lamCol D u τ (D.R.k - 1) : ℝ))

def firstColumnSpread (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  (lamCol D u τ 0 : ℝ) - (lamCol D u τ (D.R.k - 1) : ℝ)

theorem nums_basic {D : D7} {T g1 g2 : ℕ} {Cn x b L b' Sc eta : ℝ}
    (h : Nums D T g1 g2 Cn x b L b' Sc eta) : 1 ≤ L ∧ 0 ≤ Cn ∧ 4 ≤ b' ∧ b' ≤ b := by
  obtain ⟨h1, h2, h3, h4, -⟩ := b_nums h
  exact ⟨h1, h2, h3, h4⟩

theorem numbers_of_nums {D : D7} {T g1 g2 : ℕ} {Cn x b L b' Sc eta : ℝ} (K : ℝ) (hK1 : 1 ≤ K) (hKx : K ≤ x)
    (h : Nums D T g1 g2 Cn x b L b' Sc eta) :
    Numbers (2 * Cn + 4) (x * b) b' L D.host.v (Real.log T) (Real.log ((g1 : ℝ) * g2)) eta (K * Sc)
      D.R.k D.R.m D.R.t (D.R.N D.R.m) := by
  obtain ⟨hL1, hCn, h4, hbb⟩ := nums_basic h
  obtain ⟨hb, hL, hT, hg1, hg2, hb', hSc, heta, hsm, hsq, hlin, hmn, hdl, hx, hv, hpow⟩ := h
  have hx0 : (0 : ℝ) < x := by linarith
  have hmt : (0 : ℝ) ≤ (D.R.m : ℝ) * D.R.t := by positivity
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := by positivity
  refine ⟨hL1, hv, hL, by linarith, ?_, Real.log_natCast_nonneg _, ?_, ?_, ?_, ?_, ?_, rfl, by linarith,
    by positivity, ?_, hsq, hlin, hpow⟩
  · nlinarith
  · have : 0 ≤ (D.R.m : ℝ) * L := by positivity
    nlinarith
  · have : ((g1 : ℝ) * g2) = ((g1 * g2 : ℕ) : ℝ) := by push_cast; ring
    rw [this]; exact Real.log_natCast_nonneg _
  · by_cases h1 : (g1 : ℝ) = 0
    · rw [h1, zero_mul, Real.log_zero]; positivity
    by_cases h2 : (g2 : ℝ) = 0
    · rw [h2, mul_zero, Real.log_zero]; positivity
    rw [Real.log_mul h1 h2]
    nlinarith
  · have := D.R.m_add_three_le_k; omega
  · have := D.R.two_le_m; omega
  · have h1 : x * (Sc + eta + (D.R.m : ℝ) * D.R.t) ≤ b' := by
      rw [le_div_iff₀ hx0] at hsm; linarith
    have h2 : K * (Sc + eta + (D.R.m : ℝ) * D.R.t) ≤ x * (Sc + eta + (D.R.m : ℝ) * D.R.t) :=
      mul_le_mul_of_nonneg_right hKx (by linarith)
    nlinarith

theorem lamCol_stepB (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) (h : i + 1 < D.R.k) :
    lamCol D u τ (i + 1) < lamCol D u τ i + 1 := by
  unfold lamCol
  rw [dif_pos h, dif_pos (show i < D.R.k by omega)]
  simp only [hcToWeightQ, rhoVec]
  have h1 := (D.hcW u τ).u_gt_v ⟨i, by omega⟩
  have h2 := (D.hcW u τ).v_gt_u ⟨i, by omega⟩
  push_cast
  linarith

theorem mem_tops (D : D7) (τ : D.what₂.Tau) : τ ∈ tops D ↔ IsTop D τ := by
  exact b_mem_tops D τ

theorem tops_card (D : D7) : (tops D).card = D.host.TT.card := by
  exact b_card_tops D

theorem col_setup (D : D7) (u : D.what₂.Word) (Cn x b L b' Sc eta K : ℝ) (hK1 : 1 ≤ K) (hKC : Cn ≤ K)
    (hN : Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta) (hW : Wts D u Cn x b b' Sc eta) :
    ∃ (κ : ℕ) (lam : D.what₂.Tau → Fin (κ + 1 + 1) → ℤ),
      D.R.k = κ + 1 + 1 ∧ (∀ τ, Antitone (lam τ)) ∧
      (∀ τ, colAbs D u τ = (wt (lam τ) : ℝ)) ∧ (∀ τ, colAbsP D u τ = (wt (plus (lam τ)) : ℝ)) ∧
      (∀ τ, firstColumnSpread D u τ = (plus (lam τ) 0 : ℝ)) ∧
      (∀ τ, (lamCol D u τ (D.R.k - 1) : ℝ) = (lam τ (Fin.last (κ + 1)) : ℝ)) ∧
      (∀ τ ∈ tops D, x * b ≤ aT D u τ ∧ aT D u τ ≤ 2 * (x * b) ∧ b' ≤ bT D u τ ∧ bT D u τ ≤ 2 * b') ∧
      (∀ τ ∈ tops D, (wt (lam τ) : ℝ) ≤ aT D u τ + (((κ + 1 : ℕ) : ℝ) + 1) * (K * Sc)) ∧
      (∀ τ ∈ tops D, (wt (plus (lam τ)) : ℝ) ≤ aT D u τ + (((κ + 1 : ℕ) : ℝ) + 1) * (bT D u τ + K * Sc)) ∧
      (∀ τ, τ ∉ tops D → (wt (plus (lam τ)) : ℝ) ≤ (((κ + 1 : ℕ) : ℝ) + 1 + 3) * (K * Sc)) ∧
      (∀ τ, τ ∉ tops D → (wt (lam τ) : ℝ) ≤ (2 * Cn + 4) * (((κ + 1 : ℕ) : ℝ) + 1) * (K * Sc)) ∧
      (∀ τ, τ ∉ tops D → |(lam τ (Fin.last (κ + 1)) : ℝ)| ≤ (2 * Cn + 4) * (K * Sc)) := by
  obtain ⟨hL1, hCn, h4, hbb⟩ := nums_basic hN
  have hSc : 1 ≤ Sc := hN.2.2.2.2.2.2.1
  obtain ⟨κ, hκ⟩ : ∃ κ, D.R.k = κ + 1 + 1 := ⟨D.R.k - 2, by have := D.R.m_add_three_le_k; omega⟩
  have hint : ∀ τ (i : Fin (κ + 1 + 1)), ∃ z : ℤ, lamCol D u τ i = z :=
    fun τ i => (hW τ).1 i (by have := i.2; omega)
  choose lam hlam using hint
  have hl : ∀ τ (i : Fin (κ + 1 + 1)), (lamCol D u τ i : ℝ) = (lam τ i : ℝ) := fun τ i => by
    rw [hlam τ i]; norm_cast
  have hk1 : D.R.k - 1 = κ + 1 := by omega
  have hlk : ∀ τ, (lamCol D u τ (D.R.k - 1) : ℝ) = (lam τ (Fin.last (κ + 1)) : ℝ) := fun τ => by
    rw [← hl τ (Fin.last (κ + 1)), hk1, Fin.val_last]
  have hl0 : ∀ τ, (lamCol D u τ 0 : ℝ) = (lam τ 0 : ℝ) := fun τ => by
    rw [← hl τ 0]; rfl
  have hanti : ∀ τ, Antitone (lam τ) := fun τ => by
    refine Fin.antitone_iff_succ_le.2 fun i => ?_
    have h1 := lamCol_stepB D u τ i (by have := i.2; omega)
    have h2 := hlam τ i.succ
    have h3 := hlam τ i.castSucc
    rw [Fin.val_succ] at h2
    rw [Fin.val_castSucc] at h3
    rw [h2, h3] at h1
    have h4 : lam τ i.succ < lam τ i.castSucc + 1 := by exact_mod_cast h1
    omega
  have hKSc : Sc ≤ K * Sc := by nlinarith
  have hwt : ∀ τ, colAbs D u τ = (wt (lam τ) : ℝ) := fun τ => by
    unfold colAbs wt
    rw [hκ, Finset.sum_range]
    push_cast
    exact Finset.sum_congr rfl fun i _ => hl τ i
  have hwtp : ∀ τ, colAbsP D u τ = (wt (plus (lam τ)) : ℝ) := fun τ => by
    unfold colAbsP wt plus
    rw [hlk τ, hκ, Finset.sum_range]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [hl τ i]
  have hp1 : ∀ τ, firstColumnSpread D u τ = (plus (lam τ) 0 : ℝ) := fun τ => by
    unfold firstColumnSpread plus
    rw [hlk τ, hl0 τ]; push_cast; ring
  have htop : ∀ τ ∈ tops D, ((wt (lam τ) : ℝ) ≤ aT D u τ + (((κ + 1 : ℕ) : ℝ) + 1) * (K * Sc)) ∧
      ((wt (plus (lam τ)) : ℝ) ≤ aT D u τ + (((κ + 1 : ℕ) : ℝ) + 1) * (bT D u τ + K * Sc)) := by
    intro τ hτ
    obtain ⟨-, -, hb1, -, hmid⟩ := (hW τ).2.1 ((mem_tops D τ).1 hτ)
    rw [hlk τ] at hb1
    have hbt : (0 : ℤ) ≤ -lam τ (Fin.last (κ + 1)) := by
      have : (0 : ℝ) ≤ ((-lam τ (Fin.last (κ + 1)) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hS0 : (0 : ℤ) ≤ ⌊K * Sc⌋ := Int.floor_nonneg.2 (by positivity)
    obtain ⟨c1, c2⟩ := Formalism.HermitianLattices.TraceIntegrality.column_top_entry κ (lam τ) (lam τ 0) (-lam τ (Fin.last (κ + 1))) ⌊K * Sc⌋
      hbt hS0 rfl (by ring) (fun i hi0 hil => by
        have hi1 : 0 < (i : ℕ) := Nat.pos_of_ne_zero fun h => hi0 (Fin.ext h)
        have hi2 : (i : ℕ) < D.R.k - 1 := by
          rw [hk1]
          have h5 : (i : ℕ) ≠ κ + 1 := fun h => hil (Fin.ext (by rw [h, Fin.val_last]))
          have := i.2
          omega
        obtain ⟨m1, m2⟩ := hmid i hi1 hi2
        rw [hl τ i] at m1 m2
        refine ⟨by exact_mod_cast m1, Int.le_floor.2 (by linarith)⟩)
    have hfl : (⌊K * Sc⌋ : ℝ) ≤ K * Sc := Int.floor_le _
    have c1' : (wt (lam τ) : ℝ) ≤ (lam τ 0 : ℝ) + ((κ : ℝ) + 2) * (⌊K * Sc⌋ : ℝ) := by exact_mod_cast c1
    have c2' : (wt (plus (lam τ)) : ℝ) ≤
        (lam τ 0 : ℝ) + ((κ : ℝ) + 2) * (-(lam τ (Fin.last (κ + 1)) : ℝ) + (⌊K * Sc⌋ : ℝ)) := by
      exact_mod_cast c2
    have hκ0 : (0 : ℝ) ≤ (κ : ℝ) + 2 := by positivity
    unfold aT bT
    rw [hl0 τ, hlk τ]
    push_cast
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hfl hκ0]
    · nlinarith [mul_le_mul_of_nonneg_left hfl hκ0]
  have hnt : ∀ τ, τ ∉ tops D → ∀ i : Fin (κ + 1 + 1), 0 ≤ (lam τ i : ℝ) ∧ (lam τ i : ℝ) ≤ Cn * Sc := by
    intro τ hτ i
    have := (hW τ).2.2.1 (fun h => hτ ((mem_tops D τ).2 h)) i (by have := i.2; omega)
    rwa [hl τ i] at this
  have hCS : Cn * Sc ≤ K * Sc := mul_le_mul_of_nonneg_right hKC (by linarith)
  have hKS0 : 0 ≤ K * Sc := by positivity
  refine ⟨κ, lam, hκ, hanti, hwt, hwtp, hp1, hlk, ?_, fun τ hτ => (htop τ hτ).1, fun τ hτ => (htop τ hτ).2,
    ?_, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨t1, t2, t3, t4, -⟩ := (hW τ).2.1 ((mem_tops D τ).1 hτ)
    exact ⟨t1, t2, t3, t4.le⟩
  · intro τ hτ
    have h1 : (wt (plus (lam τ)) : ℝ) ≤ ∑ _i : Fin (κ + 1 + 1), K * Sc := by
      unfold wt plus
      push_cast
      refine Finset.sum_le_sum fun i _ => ?_
      have := hnt τ hτ i
      have := hnt τ hτ (Fin.last (κ + 1))
      linarith
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    push_cast at h1 ⊢
    nlinarith
  · intro τ hτ
    have h1 : (wt (lam τ) : ℝ) ≤ ∑ _i : Fin (κ + 1 + 1), K * Sc := by
      unfold wt
      push_cast
      refine Finset.sum_le_sum fun i _ => ?_
      have := hnt τ hτ i
      linarith
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    push_cast at h1 ⊢
    have hκ0 : (0 : ℝ) ≤ ((κ : ℝ) + 1 + 1) * (K * Sc) := by positivity
    nlinarith
  · intro τ hτ
    have := hnt τ hτ (Fin.last (κ + 1))
    rw [abs_of_nonneg this.1]
    nlinarith

end Z56a

section Z56
open Formalism.BasicNotions NumberField
open Formalism.HermitianLattices.TraceIntegrality (Numbers wt plus MeanSquareWeightBound)

def SlopeLow (D : D7) (u : D.what₂.Word) : Prop :=
  -(∑ τ, colAbs D u τ / D.R.k * Real.log (Tu D u)) -
      ∑ τ, (colAbsP D u τ * Real.log D.R.k + (D.R.k : ℝ) ^ 2 * Real.log (firstColumnSpread D u τ + D.R.k)) ≤
    ((D.fm u).lat 0).mu

def SlopeMax (D : D7) (u : D.what₂.Word) (C5 : ℝ) : Prop :=
  ((D.fm u).lat 0).muMax ≤
    ∑ τ, (colAbsP D u τ * (C5 * Real.log (D.R.k * D.host.v)) +
      (D.R.k : ℝ) ^ 2 * Real.log (firstColumnSpread D u τ + D.R.k) +
      |(lamCol D u τ (D.R.k - 1) : ℝ)| * Real.log (Tu D u))

def SlopeLowerOpenPart (D : D7) : Prop := ∀ u, ColVal D u → SlopeLow D u

def SlopeMaxOpenPart (D : D7) (C5 : ℝ) : Prop := ∀ u, ColVal D u → SlopeMax D u C5

private theorem mulmax_lemma (C K P X Y : ℝ) (hP : 0 ≤ P) (hX : 0 ≤ X) (hXY : X ≤ K * Y) :
    C * (P * X) ≤ max C 0 * K * (P * Y) := by
  have h0 : 0 ≤ max C 0 := le_max_right _ _
  calc C * (P * X) ≤ max C 0 * (P * X) := mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hP hX)
    _ ≤ max C 0 * (P * (K * Y)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXY hP) h0
    _ = max C 0 * K * (P * Y) := by ring

theorem arith5 (C K n a lk f k b' Sc lT L : ℝ) (hK1 : 1 ≤ K) (hn : 0 ≤ n) (ha : 0 ≤ a) (hlk : 0 ≤ lk)
    (hf : 0 ≤ f) (hk : 0 ≤ k) (hb : 0 ≤ b') (hS : 0 ≤ Sc) (hT : 0 ≤ lT) (hL : 0 ≤ L) :
    C * n * a * lk ≤ max C 0 * K * n * a * lk ∧
    C * f * k * (b' + K * Sc) * lk ≤ max C 0 * K * f * k * (b' + Sc) * lk ∧
    C * f * (K * Sc) * lT ≤ max C 0 * K * f * Sc * lT ∧
    C * f * k ^ 2 * L ≤ max C 0 * K * f * k ^ 2 * L := by
  have hK0 : 0 ≤ K := by linarith
  have hX2 : b' + K * Sc ≤ K * (b' + Sc) := by nlinarith [mul_nonneg (sub_nonneg.2 hK1) hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc C * n * a * lk = C * ((n * a * lk) * 1) := by ring
      _ ≤ max C 0 * K * ((n * a * lk) * 1) :=
        mulmax_lemma C K _ 1 1 (mul_nonneg (mul_nonneg hn ha) hlk) zero_le_one (by linarith)
      _ = max C 0 * K * n * a * lk := by ring
  · calc C * f * k * (b' + K * Sc) * lk = C * ((f * k * lk) * (b' + K * Sc)) := by ring
      _ ≤ max C 0 * K * ((f * k * lk) * (b' + Sc)) :=
        mulmax_lemma C K _ _ _ (mul_nonneg (mul_nonneg hf hk) hlk) (add_nonneg hb (mul_nonneg hK0 hS)) hX2
      _ = max C 0 * K * f * k * (b' + Sc) * lk := by ring
  · calc C * f * (K * Sc) * lT = C * ((f * lT) * (K * Sc)) := by ring
      _ ≤ max C 0 * K * ((f * lT) * Sc) :=
        mulmax_lemma C K _ _ _ (mul_nonneg hf hT) (mul_nonneg hK0 hS) le_rfl
      _ = max C 0 * K * f * Sc * lT := by ring
  · calc C * f * k ^ 2 * L = C * ((f * k ^ 2 * L) * 1) := by ring
      _ ≤ max C 0 * K * ((f * k ^ 2 * L) * 1) :=
        mulmax_lemma C K _ 1 1 (mul_nonneg (mul_nonneg hf (sq_nonneg k)) hL) zero_le_one (by linarith)
      _ = max C 0 * K * f * k ^ 2 * L := by ring

theorem ramifiedLattice_of_chain_estimates (Cn : ℝ) : ∃ C : ℝ, ∀ (D : D7) (x : ℝ), max Cn 1 ≤ x → SlopeLowerOpenPart D → Conclusion5 D Cn C x := by
  classical
  obtain ⟨C, hC⟩ := Formalism.HermitianLattices.TraceIntegrality.zeta_proposition_second (2 * max Cn 0 + 4) (by positivity)
  refine ⟨max C 0 * max Cn 1, fun D x hx hZ u b L b' Sc eta hN hW Y => ?_⟩
  obtain ⟨hL1, hCn, h4, hbb⟩ := nums_basic hN
  rw [max_eq_left hCn] at hC
  set K := max Cn 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hSc : 1 ≤ Sc := hN.2.2.2.2.2.2.1
  have hb0 : 0 < b := hN.1
  have hx2 : 2 ≤ x := hN.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨κ, lam, hκ, hanti, hwt, hwtp, hp1, hlk, ht0, ht1, ht2, hn1, hn2, hn3⟩ :=
    col_setup D u Cn x b L b' Sc eta K hK1 (le_max_left _ _) hN hW
  have hNum := numbers_of_nums K hK1 hx hN
  rw [hκ] at hNum
  have hkR : (D.R.k : ℝ) = ((κ + 1 : ℕ) : ℝ) + 1 := by rw [hκ]; push_cast; ring
  have hf : (Fintype.card D.what₂.Tau : ℝ) = D.R.f := by rw [D.what₂.card_Tau]
  have hf0 : (0 : ℝ) < (Fintype.card D.what₂.Tau : ℝ) := by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; positivity
  have hlow := hZ u Y
  unfold SlopeLow at hlow
  set mu := ((D.fm u).lat 0).mu with hmu
  set lT := Real.log (Tu D u) with hlT
  have hZ4 : ∀ τ, colAbsP D u τ * Real.log D.R.k + (D.R.k : ℝ) ^ 2 * Real.log (firstColumnSpread D u τ + D.R.k) =
      MeanSquareWeightBound (lam τ) := fun τ => by
    unfold MeanSquareWeightBound
    have e : ((plus (lam τ) 0 : ℤ) : ℝ) + (((κ + 1 : ℕ) : ℝ) + 1) =
        ((plus (lam τ) 0 : ℤ) : ℝ) + ((κ + 1 : ℕ) : ℝ) + 1 := by ring
    rw [hwtp τ, hp1 τ, hkR, e]
  simp only [hZ4, hwt] at hlow
  set δ := mu + (∑ τ, (wt (lam τ) : ℝ) / D.R.k * lT) + ∑ τ, MeanSquareWeightBound (lam τ) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have key := hC D.what₂.Tau Unit (tops D) (κ + 1) D.R.m D.R.t (D.R.N D.R.m) lam (aT D u) (bT D u)
    (x * b) b' L D.host.v lT (Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) eta (K * Sc) mu (fun _ => mu)
    (fun τ => -MeanSquareWeightBound (lam τ) + δ / (Fintype.card D.what₂.Tau : ℝ))
    (fun τ => MeanSquareWeightBound (lam τ) - δ / (Fintype.card D.what₂.Tau : ℝ))
    (fun τ => MeanSquareWeightBound (lam τ) - δ / (Fintype.card D.what₂.Tau : ℝ))
    hNum hanti ht0 ht1 ht2 hn1 hn2 (by simp [Formalism.HermitianLattices.TraceIntegrality.mean])
    (fun _ => by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_div_cancel₀ _ hf0.ne', Finset.sum_neg_distrib, hδ, ← hkR]
      ring)
    (fun τ => by ring) (fun τ => le_rfl)
    (fun τ => by have : 0 ≤ δ / (Fintype.card D.what₂.Tau : ℝ) := by positivity
                 linarith)
  rw [← hkR, hf, tops_card] at key
  refine le_trans ?_ key
  have hlk0 : 0 ≤ Real.log (D.R.k : ℝ) := Real.log_natCast_nonneg _
  have hlT0 : 0 ≤ lT := Real.log_natCast_nonneg _
  obtain ⟨e1, e2, e3, e4⟩ := arith5 C K (D.host.TT.card : ℝ) (x * b) (Real.log D.R.k) D.R.f D.R.k b' Sc lT L hK1
    (by positivity) (by positivity) hlk0 (by positivity) (by positivity) (by linarith) (by linarith) hlT0 (by linarith)
  linarith

theorem arith6 (C K n a l f k b' Sc lT L : ℝ) (hK1 : 1 ≤ K) (hn : 0 ≤ n) (ha : 0 ≤ a) (hl : 0 ≤ l)
    (hf : 0 ≤ f) (hk : 0 ≤ k) (hb : 0 ≤ b') (hS : 0 ≤ Sc) (hT : 0 ≤ lT) (hL : 0 ≤ L) :
    C * n * a * l + C * f * (b' + K * Sc) * (k * l + lT) + C * f * k ^ 2 * L ≤
      max C 0 * K * n * a * l + max C 0 * K * f * (b' + Sc) * (k * l + lT) + max C 0 * K * f * k ^ 2 * L := by
  have hK0 : 0 ≤ K := by linarith
  have hX2 : b' + K * Sc ≤ K * (b' + Sc) := by nlinarith [mul_nonneg (sub_nonneg.2 hK1) hb]
  have h1 : C * n * a * l ≤ max C 0 * K * n * a * l := by
    calc C * n * a * l = C * ((n * a * l) * 1) := by ring
      _ ≤ max C 0 * K * ((n * a * l) * 1) :=
        mulmax_lemma C K _ 1 1 (mul_nonneg (mul_nonneg hn ha) hl) zero_le_one (by linarith)
      _ = max C 0 * K * n * a * l := by ring
  have h2 : C * f * (b' + K * Sc) * (k * l + lT) ≤ max C 0 * K * f * (b' + Sc) * (k * l + lT) := by
    calc C * f * (b' + K * Sc) * (k * l + lT) = C * ((f * (k * l + lT)) * (b' + K * Sc)) := by ring
      _ ≤ max C 0 * K * ((f * (k * l + lT)) * (b' + Sc)) :=
        mulmax_lemma C K _ _ _ (mul_nonneg hf (add_nonneg (mul_nonneg hk hl) hT)) (add_nonneg hb (mul_nonneg hK0 hS)) hX2
      _ = max C 0 * K * f * (b' + Sc) * (k * l + lT) := by ring
  have h3 : C * f * k ^ 2 * L ≤ max C 0 * K * f * k ^ 2 * L := by
    calc C * f * k ^ 2 * L = C * ((f * k ^ 2 * L) * 1) := by ring
      _ ≤ max C 0 * K * ((f * k ^ 2 * L) * 1) :=
        mulmax_lemma C K _ 1 1 (mul_nonneg (mul_nonneg hf (sq_nonneg k)) hL) zero_le_one (by linarith)
      _ = max C 0 * K * f * k ^ 2 * L := by ring
  linarith

theorem classMap_estimate_of_partial (Cn C5 : ℝ) : ∃ C : ℝ, ∀ (D : D7) (x : ℝ), max Cn 1 ≤ x → SlopeMaxOpenPart D C5 → Conclusion6 D Cn C x := by
  classical
  obtain ⟨C, hC⟩ := Formalism.HermitianLattices.TraceIntegrality.zeta_proposition_third (2 * max Cn 0 + 4) (by positivity)
  refine ⟨max C 0 * max Cn 1 * max 1 (C5 / (2 * max Cn 0 + 4)), fun D x hx hZ u b L b' Sc eta hN hW Y => ?_⟩
  obtain ⟨hL1, hCn, h4, hbb⟩ := nums_basic hN
  rw [max_eq_left hCn] at hC ⊢
  set K := max Cn 1 with hK
  set K' := max 1 (C5 / (2 * Cn + 4)) with hK'
  have hC0 : 0 < 2 * Cn + 4 := by linarith
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK'1 : 1 ≤ K' := le_max_left _ _
  have hK'0 : 0 < K' := by linarith
  have hC5 : C5 ≤ K' * (2 * Cn + 4) := by
    have : C5 / (2 * Cn + 4) ≤ K' := le_max_right _ _
    rwa [div_le_iff₀ hC0] at this
  have hSc : 1 ≤ Sc := hN.2.2.2.2.2.2.1
  have hb0 : 0 < b := hN.1
  have hx2 : 2 ≤ x := hN.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv1 : 1 ≤ D.host.v := hN.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨κ, lam, hκ, hanti, hwt, hwtp, hp1, hlk, ht0, ht1, ht2, hn1, hn2, hn3⟩ :=
    col_setup D u Cn x b L b' Sc eta K hK1 (le_max_left _ _) hN hW
  have hNum := numbers_of_nums K hK1 hx hN
  rw [hκ] at hNum
  have hkR : (D.R.k : ℝ) = ((κ + 1 : ℕ) : ℝ) + 1 := by rw [hκ]; push_cast; ring
  have hf : (Fintype.card D.what₂.Tau : ℝ) = D.R.f := by rw [D.what₂.card_Tau]
  have hmax := hZ u Y
  unfold SlopeMax at hmax
  set mM := ((D.fm u).lat 0).muMax with hmM
  set lT := Real.log (Tu D u) with hlT
  have hlT0 : 0 ≤ lT := Real.log_natCast_nonneg _
  have hk1 : (1 : ℝ) ≤ (D.R.k : ℝ) := by rw [hkR]; have : (0 : ℝ) ≤ ((κ + 1 : ℕ) : ℝ) := by positivity
                                         linarith
  have hlkv : 0 ≤ Real.log ((D.R.k : ℝ) * D.host.v) := Real.log_nonneg (by nlinarith)
  have hplus0 : ∀ τ i, 0 ≤ plus (lam τ) i := fun τ i => by
    unfold plus
    have := hanti τ (Fin.le_last i)
    omega
  have hwp0 : ∀ τ, (0 : ℝ) ≤ (wt (plus (lam τ)) : ℝ) := fun τ => by
    have : 0 ≤ wt (plus (lam τ)) := Finset.sum_nonneg fun i _ => hplus0 τ i
    exact_mod_cast this
  have hterm : ∀ τ, colAbsP D u τ * (C5 * Real.log (D.R.k * D.host.v)) +
      (D.R.k : ℝ) ^ 2 * Real.log (firstColumnSpread D u τ + D.R.k) + |(lamCol D u τ (D.R.k - 1) : ℝ)| * lT ≤
      K' * ((wt (plus (lam τ)) : ℝ) * ((2 * Cn + 4) * Real.log ((((κ + 1 : ℕ) : ℝ) + 1) * D.host.v))
        + (((κ + 1 : ℕ) : ℝ) + 1) ^ 2 * Real.log ((plus (lam τ) 0 : ℝ) + ((κ + 1 : ℕ) : ℝ) + 1)
        + |(lam τ (Fin.last (κ + 1)) : ℝ)| * lT) := fun τ => by
    have e : ((plus (lam τ) 0 : ℤ) : ℝ) + ((κ + 1 : ℕ) : ℝ) + 1 =
        ((plus (lam τ) 0 : ℤ) : ℝ) + (((κ + 1 : ℕ) : ℝ) + 1) := by ring
    rw [e, ← hkR, hwtp τ, hp1 τ, hlk τ]
    have hp0 : (0 : ℝ) ≤ ((plus (lam τ) 0 : ℤ) : ℝ) := by exact_mod_cast hplus0 τ 0
    have hlog : 0 ≤ Real.log (((plus (lam τ) 0 : ℤ) : ℝ) + D.R.k) := Real.log_nonneg (by linarith)
    have t1 : (wt (plus (lam τ)) : ℝ) * (C5 * Real.log (D.R.k * D.host.v)) ≤
        K' * ((wt (plus (lam τ)) : ℝ) * ((2 * Cn + 4) * Real.log (D.R.k * D.host.v))) := by
      calc (wt (plus (lam τ)) : ℝ) * (C5 * Real.log (D.R.k * D.host.v))
          = C5 * ((wt (plus (lam τ)) : ℝ) * Real.log (D.R.k * D.host.v)) := by ring
        _ ≤ K' * (2 * Cn + 4) * ((wt (plus (lam τ)) : ℝ) * Real.log (D.R.k * D.host.v)) :=
            mul_le_mul_of_nonneg_right hC5 (mul_nonneg (hwp0 τ) hlkv)
        _ = _ := by ring
    have t2 : (D.R.k : ℝ) ^ 2 * Real.log (((plus (lam τ) 0 : ℤ) : ℝ) + D.R.k) ≤
        K' * ((D.R.k : ℝ) ^ 2 * Real.log (((plus (lam τ) 0 : ℤ) : ℝ) + D.R.k)) :=
      le_mul_of_one_le_left (by positivity) hK'1
    have t3 : |(lam τ (Fin.last (κ + 1)) : ℝ)| * lT ≤ K' * (|(lam τ (Fin.last (κ + 1)) : ℝ)| * lT) :=
      le_mul_of_one_le_left (by positivity) hK'1
    linarith
  have hmax2 := le_trans hmax (Finset.sum_le_sum fun τ _ => hterm τ)
  rw [← Finset.mul_sum] at hmax2
  have key := hC D.what₂.Tau Unit (tops D) (κ + 1) D.R.m D.R.t (D.R.N D.R.m) lam (aT D u) (bT D u)
    (x * b) b' L D.host.v lT (Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) eta (K * Sc) (mM / K')
    (fun _ => ∑ τ, ((wt (plus (lam τ)) : ℝ) * ((2 * Cn + 4) * Real.log ((((κ + 1 : ℕ) : ℝ) + 1) * D.host.v))
        + (((κ + 1 : ℕ) : ℝ) + 1) ^ 2 * Real.log ((plus (lam τ) 0 : ℝ) + ((κ + 1 : ℕ) : ℝ) + 1)
        + |(lam τ (Fin.last (κ + 1)) : ℝ)| * lT))
    hNum hanti ht0 ht2
    (fun τ hτ => by
      have h1 := (ht0 τ hτ).2.2.1
      unfold bT at h1 ⊢
      rw [hlk τ] at h1 ⊢
      rw [abs_of_nonpos (by linarith)])
    hn1 hn3 ⟨(), by rw [div_le_iff₀ hK'0]; linarith⟩ (fun _ => le_rfl)
  rw [← hkR, hf, tops_card, div_le_iff₀ hK'0] at key
  have ar := arith6 C K (D.host.TT.card : ℝ) (x * b) (Real.log ((D.R.k : ℝ) * D.host.v)) D.R.f D.R.k b' Sc lT L hK1
    (by positivity) (by positivity) hlkv (by positivity) (by positivity) (by linarith) (by linarith) hlT0 (by linarith)
  have := le_trans key (mul_le_mul_of_nonneg_right ar hK'0.le)
  refine le_trans this (le_of_eq ?_)
  ring

def FamilySlopeLowerOpenPart {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := fam0 Fm SlopeLowerOpenPart

def FamilySlopeMaxOpenPart {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C5 : ℝ) : Prop := fam0 Fm fun D => SlopeMaxOpenPart D C5

theorem familySlopeLower_of_open {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : FamilySlopeLowerOpenPart Fm) : ConclusionF5 Fm := by
  intro Cn
  obtain ⟨C, hC⟩ := ramifiedLattice_of_chain_estimates Cn
  obtain ⟨x0, h0⟩ := h
  exact ⟨C, max x0 (max Cn 1), fun x hx hx1 i =>
    hC _ x (le_trans (le_max_right _ _) hx) (h0 x (le_trans (le_max_left _ _) hx) hx1 i)⟩

theorem familySlopeMax_of_open {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C5 : ℝ) (h : FamilySlopeMaxOpenPart Fm C5) : ConclusionF6 Fm := by
  intro Cn
  obtain ⟨C, hC⟩ := classMap_estimate_of_partial Cn C5
  obtain ⟨x0, h0⟩ := h
  exact ⟨C, max x0 (max Cn 1), fun x hx hx1 i =>
    hC _ x (le_trans (le_max_right _ _) hx) (h0 x (le_trans (le_max_left _ _) hx) hx1 i)⟩

end Z56

section Ms
open Formalism.BasicNotions NumberField

def msBound (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * (2 * D.R.f * Real.log (C₀ * (C₀ * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2))) +
    4 * D.R.f * n * ((n : ℝ) + 1) * (Real.log (C₀ * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2) / 2) +
    2 * D.R.f * (n : ℝ) ^ 2 * (Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1))

def MsCount (D : D7) (C₀ : ℝ) : Prop :=
  ∀ u, ClsTie D u →
    (∀ i ≤ D.R.m, Real.log (Fintype.card ((D.mem u).C.cls i) : ℝ) ≤ msBound D u C₀ (D.R.N i)) ∧
    Real.log (Fintype.card (D.fm u).clsP : ℝ) ≤ msBound D u C₀ (D.R.N D.R.m - 1)

theorem baseChange_preserves_unitary_of (C₀ : ℝ) (h2 : 2 ≤ C₀) (Cn : ℝ) : ∃ C : ℝ, ∀ (D : D7) (x : ℝ), MsCount D C₀ → Conclusion1 D Cn C x := by
  obtain ⟨C, hC⟩ := Formalism.HermitianLattices.TraceIntegrality.moduli_arithmetic_bound C₀ (by linarith)
  refine ⟨2 * max C 0, fun D x hM u b L b' Sc eta hN hT => ?_⟩
  obtain ⟨hL1, hCn, h4, hbb⟩ := nums_basic hN
  have hNum := numbers_of_nums 1 le_rfl (by have := hN.2.2.2.2.2.2.2.2.2.2.2.2.2.1; linarith) hN
  have hb0 : 0 < b := hN.1
  have hx2 : 2 ≤ x := hN.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv1 : 1 ≤ D.host.v := hNum.one_le_v
  set lT := Real.log (Tu D u) with hlT
  set lg := Real.log ((D.host.g 0 : ℝ) * D.host.g 1) with hlg
  have hlT0 : 0 ≤ lT := hNum.logT_nonneg
  have hlg0 : 0 ≤ lg := hNum.logg_nonneg
  have hT1 : (1 : ℝ) ≤ (Tu D u : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  have hxb : b ≤ x * b := by nlinarith
  have hxbv : x * b ≤ x * b * D.host.v := le_mul_of_one_le_right (by positivity) hv1
  have hNle : (D.R.N D.R.m : ℝ) ≤ x * b * D.host.v := by
    have h1 := hNum.lin
    have h0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by positivity
    have : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * L := le_mul_of_one_le_right h0 hL1
    linarith
  have hlogn : ∀ n : ℕ, 1 ≤ n → n ≤ D.R.N D.R.m → Real.log n ≤ L := fun n h1 h2 => by
    refine le_trans (Real.log_le_log (by exact_mod_cast h1) ?_) hNum.log_av
    have : (n : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast h2
    linarith
  have hf1 : 1 ≤ D.R.f := b_one_le_f D
  have hfN : D.R.f ≤ D.R.N D.R.m := by
    have := D.R.f_le_k
    unfold Ranks.f Ranks.n Ranks.N
    omega
  have hlv : Real.log D.host.v ≤ L := by
    refine le_trans (Real.log_le_log (by linarith) ?_) hNum.log_av
    have : (1 : ℝ) ≤ x * b := by nlinarith
    exact le_mul_of_one_le_left (by linarith) this
  have step : ∀ (n : ℕ) (logh : ℝ), 1 ≤ n → n ≤ D.R.N D.R.m → logh ≤ msBound D u C₀ n →
      logh ≤ 2 * max C 0 * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * (L + lT + lg) := by
    intro n logh hn1 hnN hh
    have hfn : (0 : ℝ) ≤ (D.R.f : ℝ) * (n : ℝ) ^ 2 := by positivity
    have key := hC D.R.f n D.host.v (Tu D u) L (lT + lg) _ logh hf1 hn1 hv1 hT1 hL1 (by linarith)
      (hlogn _ hf1 hfN) (hlogn _ hn1 hnN) hlv rfl (by
        refine le_trans hh ?_
        unfold msBound
        have e1 : 2 * (D.R.f : ℝ) * (n : ℝ) ^ 2 * (lT + lg) ≤
            (D.R.f : ℝ) * n * lT + C₀ * D.R.f * (n : ℝ) ^ 2 * (lT + lg) := by
          have a1 : 0 ≤ (D.R.f : ℝ) * n * lT := by positivity
          have a2 : 2 * ((D.R.f : ℝ) * (n : ℝ) ^ 2 * (lT + lg)) ≤ C₀ * ((D.R.f : ℝ) * (n : ℝ) ^ 2 * (lT + lg)) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
          linarith
        linarith)
    refine le_trans key ?_
    have hn2 : (n : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 2 := by
      have : (n : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hnN
      exact pow_le_pow_left₀ (by positivity) this 2
    have hCp : C ≤ max C 0 := le_max_left _ _
    have hCp0 : 0 ≤ max C 0 := le_max_right _ _
    generalize max C 0 = Cp at hCp hCp0
    calc C * D.R.f * (n : ℝ) ^ 2 * (L + lT + (lT + lg))
        = C * ((D.R.f : ℝ) * (n : ℝ) ^ 2 * (L + lT + (lT + lg))) := by ring
      _ ≤ Cp * ((D.R.f : ℝ) * (n : ℝ) ^ 2 * (L + lT + (lT + lg))) :=
          mul_le_mul_of_nonneg_right hCp (by positivity)
      _ ≤ Cp * ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * (2 * (L + lT + lg))) := by
          refine mul_le_mul_of_nonneg_left ?_ hCp0
          refine mul_le_mul (mul_le_mul_of_nonneg_left hn2 (by positivity)) (by linarith) (by positivity)
            (by positivity)
      _ = 2 * Cp * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * (L + lT + lg) := by ring
  obtain ⟨m1, m2⟩ := hM u hT
  have hk := D.R.m_add_three_le_k
  refine ⟨fun i hi => step _ _ ?_ ?_ (m1 i hi), step _ _ ?_ (Nat.sub_le _ _) m2⟩
  · unfold Ranks.N; omega
  · unfold Ranks.N; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  · unfold Ranks.N; omega

def MsCountF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C₀ : ℝ) : Prop := fam0 Fm fun D => MsCount D C₀

theorem familyMass_of_massCount {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C₀ : ℝ) (h2 : 2 ≤ C₀) (h : MsCountF Fm C₀) : ConclusionF1 Fm := by
  intro Cn
  obtain ⟨C, hC⟩ := baseChange_preserves_unitary_of C₀ h2 Cn
  obtain ⟨x0, h0⟩ := h
  exact ⟨C, x0, fun x hx hx1 i => hC _ x (h0 x hx hx1 i)⟩

end Ms

section Z1a
open Formalism.BasicNotions NumberField

theorem Hq_sub (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (z x : Gx D i → ℂ) :
    Hq D i s (z - x) = Hq D i s z + Hq D i s x - 2 * (Hherm D i s z x).re := by
  unfold Hq Hherm
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Complex.div_ofReal_re, Pi.sub_apply, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
  have : (z g * star (x g)).re = (z g * (starRingEnd ℂ) (x g)).re := rfl
  rw [this]
  ring

theorem dens_trans (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (x : Gx D i → ℂ) (Th : (Gx D i → ℂ) → ℂ) (z : Gx D i → ℂ) :
    dens D i s (flipTwoThree.trans D i s x Th) z = dens D i s Th (z - x) := by
  unfold dens flipTwoThree.trans
  rw [norm_mul, mul_pow, Complex.norm_exp, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, Hq_sub]
  congr 2
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  push_cast
  ring

theorem dens_le_of_sum (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (Th e0 : (Gx D i → ℂ) → ℂ) (κ : ℂ) (n : ℕ) (c : Fin n → ℂ)
    (x : Fin n → Gx D i → ℂ) (h : ∀ z, Th z = κ * ∑ k, c k * flipTwoThree.trans D i s (x k) e0 z) (M : ℝ)
    (hM : ∀ z, dens D i s e0 z ≤ M) (z : Gx D i → ℂ) :
    dens D i s Th z ≤ ‖κ‖ ^ 2 * (∑ k, ‖c k‖) ^ 2 * M := by
  have hM0 : 0 ≤ M := le_trans (by unfold dens; positivity) (hM 0)
  set E := Real.exp (-Real.pi * Hq D i s z) with hE
  have hEp : 0 < E := Real.exp_pos _
  have hk : ∀ k, ‖trans D i s (x k) e0 z‖ ≤ Real.sqrt (M / E) := by
    intro k
    have h1 : dens D i s (flipTwoThree.trans D i s (x k) e0) z ≤ M := by rw [dens_trans]; exact hM _
    unfold dens at h1
    rw [← hE] at h1
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hEp]; exact h1
  have h2 : ‖Th z‖ ≤ ‖κ‖ * ((∑ k, ‖c k‖) * Real.sqrt (M / E)) := by
    rw [h z, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hk k) (norm_nonneg _)
  have h3 : ‖Th z‖ ^ 2 ≤ (‖κ‖ * ((∑ k, ‖c k‖) * Real.sqrt (M / E))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h4 : (‖κ‖ * ((∑ k, ‖c k‖) * Real.sqrt (M / E))) ^ 2 = ‖κ‖ ^ 2 * (∑ k, ‖c k‖) ^ 2 * (M / E) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hM0 hEp.le)]; ring
  unfold dens
  rw [← hE]
  calc ‖Th z‖ ^ 2 * E ≤ ‖κ‖ ^ 2 * (∑ k, ‖c k‖) ^ 2 * (M / E) * E :=
        mul_le_mul_of_nonneg_right (h4 ▸ h3) hEp.le
    _ = ‖κ‖ ^ 2 * (∑ k, ‖c k‖) ^ 2 * M := by field_simp

theorem Th_tied (D : D7) (u : D.what₂.Word) (X : KerData D u) (Cd : ℝ) (h5 : adm5 X Cd) (hS : ThetaSupremumBound D)
    (i : ℕ) (hi : i < D.R.m) (s) (L) (L') (hth : (D.fm u).thFree i s L L' = thetaLocalFactorAtIndex D u i s) (z) :
    dens D i s (X.Th i s L L') z ≤ Real.exp (Cd * D.R.f *
      ((D.R.m : ℝ) ^ 2 * D.R.N (i + 1) + (D.R.N i : ℝ) * D.R.N (i + 1)) *
      (Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1))) *
      ((4 : ℝ) ^ (D.R.f * D.R.N i * D.R.N (i + 1)) *
      (2 + 8 * ((D.R.f * D.R.N i * D.R.N (i + 1) : ℕ) : ℝ) * D.host.v) ^ (D.R.f * D.R.N i * D.R.N (i + 1)) *
      thetaLocalFactorAtIndex D u i s ^ 2) := by
  obtain ⟨κ, n, c, x, hid, hb⟩ := h5 i hi s L L'
  have hM := fun z => hS i s (X.tor i s L L') (X.e0 i s L L') (X.initial_theta_admissible i hi s L L') z
  rw [← X.levelZeroComparison_norm i hi s L L', hth] at hM
  refine le_trans (dens_le_of_sum D i s _ _ κ n c x hid _ hM z) ?_
  refine mul_le_mul_of_nonneg_right hb ?_
  exact le_trans (by unfold dens; positivity) (hM 0)

theorem jet_sq_le {σ : Type} (cf : (σ →₀ ℕ) → ℂ) (Q : MvPolynomial σ ℂ) :
    ‖jet cf Q‖ ^ 2 ≤ fockSq Q * ∑ e ∈ Q.support, (e.prod fun _ n => (n.factorial : ℝ)) * ‖cf e‖ ^ 2 := by
  unfold jet fockSq
  have hw : ∀ e : σ →₀ ℕ, ‖(e.prod fun _ n => (n.factorial : ℂ))‖ = (e.prod fun _ n => (n.factorial : ℝ)) := by
    intro e; simp [Finsupp.prod, norm_prod]
  have hw0 : ∀ e : σ →₀ ℕ, 0 ≤ (e.prod fun _ n => (n.factorial : ℝ)) := by
    intro e; exact Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)
  have h1 : ‖∑ e ∈ Q.support, Q.coeff e * (e.prod fun _ n => (n.factorial : ℂ)) * cf e‖ ≤
      ∑ e ∈ Q.support, (‖Q.coeff e‖ * Real.sqrt (e.prod fun _ n => (n.factorial : ℝ))) *
        (Real.sqrt (e.prod fun _ n => (n.factorial : ℝ)) * ‖cf e‖) := by
    refine le_trans (norm_sum_le _ _) (le_of_eq (Finset.sum_congr rfl (fun e _ => ?_)))
    rw [norm_mul, norm_mul, hw]
    nth_rewrite 1 [← Real.mul_self_sqrt (hw0 e)]
    ring
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Q.support
    (fun e => ‖Q.coeff e‖ * Real.sqrt (e.prod fun _ n => (n.factorial : ℝ)))
    (fun e => Real.sqrt (e.prod fun _ n => (n.factorial : ℝ)) * ‖cf e‖)
  refine le_trans (pow_le_pow_left₀ (norm_nonneg _) h1 2) (le_trans h2 (le_of_eq ?_))
  congr 1
  · exact Finset.sum_congr rfl (fun e _ => by rw [mul_pow, Real.sq_sqrt (hw0 e)])
  · exact Finset.sum_congr rfl (fun e _ => by rw [mul_pow, Real.sq_sqrt (hw0 e)])

def jetN (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (cf : (Gx D i →₀ ℕ) → ℂ) (n : D.what₂.Tau → ℕ)
    (E : Finset (Gx D i →₀ ℕ)) : ℝ :=
  (∑ e ∈ E, (e.prod fun _ k => (k.factorial : ℝ)) * ‖cf e‖ ^ 2) * ∏ τ, D.gx.Om τ s ^ n τ

def JetInt (D : D7) : Prop :=
  ∀ (i : ℕ) (s : D.what₂.LL →+* ℂ) (Th : (Gx D i → ℂ) → ℂ) (cf : (Gx D i →₀ ℕ) → ℂ) (S2 : ℝ),
    (∀ z, HasSum (fun e => cf e * e.prod fun g k => z g ^ k) (Th z)) → (∀ z, dens D i s Th z ≤ S2) →
    ∀ (n : D.what₂.Tau → ℕ) (E : Finset (Gx D i →₀ ℕ)),
      (∀ e ∈ E, ∀ τ, ∑ ac : Fin (D.R.N i) × Fin (D.R.N (i + 1)), e (τ, ac) = n τ) →
      jetN D i s cf n E *
          ∏ τ, ((1 + (if n τ = 0 then (1 : ℝ) else min 1 (((D.R.N i * D.R.N (i + 1) : ℕ) : ℝ) / n τ))) ^
            (n τ + D.R.N i * D.R.N (i + 1)))⁻¹ ≤
        S2 * ∏ τ, ((if n τ = 0 then (1 : ℝ) else min 1 (((D.R.N i * D.R.N (i + 1) : ℕ) : ℝ) / n τ)) ^
            (D.R.N i * D.R.N (i + 1)))⁻¹

def jetF (D : D7) (i : ℕ) (n : D.what₂.Tau → ℕ) : ℝ :=
  ∏ τ, (2 * Real.exp 1 * max 1 ((n τ : ℝ) / ((D.R.N i * D.R.N (i + 1) : ℕ) : ℝ))) ^ (D.R.N i * D.R.N (i + 1))

theorem N_pos' (D : D7) (i : ℕ) : 1 ≤ D.R.N i := by
  have := D.R.m_add_three_le_k
  unfold Ranks.N; omega

theorem jet_bd (D : D7) (hJ : JetInt D) (i : ℕ) (s : D.what₂.LL →+* ℂ) (Th : (Gx D i → ℂ) → ℂ)
    (cf : (Gx D i →₀ ℕ) → ℂ) (S2 : ℝ)
    (h1 : ∀ z, HasSum (fun e => cf e * e.prod fun g k => z g ^ k) (Th z)) (h2 : ∀ z, dens D i s Th z ≤ S2)
    (n : D.what₂.Tau → ℕ) (E : Finset (Gx D i →₀ ℕ))
    (hE : ∀ e ∈ E, ∀ τ, ∑ ac : Fin (D.R.N i) × Fin (D.R.N (i + 1)), e (τ, ac) = n τ) :
    jetN D i s cf n E ≤ S2 * jetF D i n :=
  Formalism.HermitianLattices.TraceIntegrality.product_of_jets D.what₂.Tau n (D.R.N i * D.R.N (i + 1)) _ S2
    (Nat.mul_pos (N_pos' D i) (N_pos' D (i + 1)))
    (le_trans (by unfold dens; positivity) (h2 0)) (hJ i s Th cf S2 h1 h2 n E hE)

def supB (D : D7) (u : D.what₂.Word) (Cd : ℝ) (i : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  Real.exp (Cd * D.R.f *
      ((D.R.m : ℝ) ^ 2 * D.R.N (i + 1) + (D.R.N i : ℝ) * D.R.N (i + 1)) *
      (Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1))) *
      ((4 : ℝ) ^ (D.R.f * D.R.N i * D.R.N (i + 1)) *
      (2 + 8 * ((D.R.f * D.R.N i * D.R.N (i + 1) : ℕ) : ℝ) * D.host.v) ^ (D.R.f * D.R.N i * D.R.N (i + 1)) *
      thetaLocalFactorAtIndex D u i s ^ 2)

theorem le_sq_of_le_sqrt_mul {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (h : t ≤ Real.sqrt t * r) : t ≤ r ^ 2 := by
  have hs := Real.sqrt_nonneg t
  have ht2 := Real.sq_sqrt ht
  nlinarith [sq_nonneg (r - Real.sqrt t)]

def blockB (D : D7) (u : D.what₂.Word) (Cd : ℝ) (i : ℕ) (s : D.what₂.LL →+* ℂ) (n : D.what₂.Tau → ℕ) : ℝ :=
  max (∏ τ, hook (nuLift D u τ i)) 0 * (supB D u Cd i s * jetF D i n * (∏ τ, D.gx.Om τ s ^ n τ)⁻¹)

theorem supB_nonneg (D : D7) (u : D.what₂.Word) (Cd : ℝ) (i : ℕ) (s : D.what₂.LL →+* ℂ) (hv : 0 ≤ D.host.v) :
    0 ≤ supB D u Cd i s := by
  unfold supB
  exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg (by positivity)
    (pow_nonneg (add_nonneg (by norm_num) (mul_nonneg (by positivity) hv)) _)) (sq_nonneg _))

theorem jetF_nonneg (D : D7) (i : ℕ) (n : D.what₂.Tau → ℕ) : 0 ≤ jetF D i n := by
  unfold jetF
  apply Finset.prod_nonneg
  intro τ _
  apply pow_nonneg
  exact mul_nonneg (by positivity) (le_trans zero_le_one (le_max_left _ _))

theorem prod_om_pow_pos (D : D7) (s : D.what₂.LL →+* ℂ) (n : D.what₂.Tau → ℕ) : 0 < ∏ τ, D.gx.Om τ s ^ n τ :=
  Finset.prod_pos fun τ _ => pow_pos (D.gx.Om_pos τ s) _

theorem opNormSq_eq_of_integral_weight (D : D7) (u : D.what₂.Word) (X : KerData D u) (hCM : X.ConjMetric) (hG : AdmittedGaloisConjugateKernels X) (Cd : ℝ)
    (h5 : adm5 X Cd) (hS : ThetaSupremumBound D) (hJ : JetInt D) (hv : 0 ≤ D.host.v) (i : ℕ) (hi : i < D.R.m)
    (hth : ∀ s L L', (D.fm u).thFree i s L L' = thetaLocalFactorAtIndex D u i s) (hK : (D.fm u).KRat i)
    (s : D.what₂.LL →+* ℂ) (n : D.what₂.Tau → ℕ) (hn : ∀ τ, ((n τ : ℕ) : ℚ) = absQ (nuLift D u τ i)) :
    opSq D ((D.fm u).lat i) ((D.fm u).lat (i + 1)) s ((D.fm u).KL i hK) ≤
      (Fintype.card ((D.mem u).C.cls (i + 1)) : ℝ) * ((Fintype.card ((D.mem u).C.cls i) : ℝ) * blockB D u Cd i s n) := by
  have hM0 : 0 ≤ blockB D u Cd i s n := by
    unfold blockB
    have := supB_nonneg D u Cd i s hv
    have := jetF_nonneg D i n
    have := (prod_om_pow_pos D s n).le
    positivity
  set M := blockB D u Cd i s n with hM
  refine opNormAt_sq_le _ _ _ _ ((D.fm u).lat_good i).1 (InfinitePlace.mk s)
    (IsTotallyComplex.isComplex _) ((D.fm u).KL i hK) _ (by positivity) (fun x => ?_)
  rw [hCM.2.2 (i + 1) (by omega) s _, hCM.2.2 i hi.le s x]
  set y := (D.fm u).KL i hK x with hy
  have ha0 : ∀ c, 0 ≤ X.nrm i s c x := fun c => hCM.2.1 i hi.le s c x
  have ha'0 : ∀ c, 0 ≤ X.nrm (i + 1) s c y := fun c => hCM.2.1 (i + 1) (by omega) s c y
  have hw0 : ∀ c, 0 ≤ ((Nat.card ((D.mem u).C.stab i c) : ℝ))⁻¹ := fun c => by positivity
  have hw1 : ∀ c, ((Nat.card ((D.mem u).C.stab i c) : ℝ))⁻¹ ≤ 1 := fun c => Nat.cast_inv_le_one _
  have hw'0 : ∀ c, 0 ≤ ((Nat.card ((D.mem u).C.stab (i + 1) c) : ℝ))⁻¹ := fun c => by positivity
  have hw'1 : ∀ c, ((Nat.card ((D.mem u).C.stab (i + 1) c) : ℝ))⁻¹ ≤ 1 := fun c => Nat.cast_inv_le_one _
  set Sx := ∑ c, ((Nat.card ((D.mem u).C.stab i c) : ℝ))⁻¹ * X.nrm i s c x with hSx
  have hSx0 : 0 ≤ Sx := Finset.sum_nonneg fun c _ => mul_nonneg (hw0 c) (ha0 c)
  obtain ⟨hker, hQ⟩ := hG s i hi hK x y
  have hjet : ∀ L L', ‖jet (X.cf i s L L') (X.Q i s L L' x y)‖ ≤
      Real.sqrt M * (Real.sqrt (X.nrm i s L x) * Real.sqrt (X.nrm (i + 1) s L' y)) := by
    intro L L'
    obtain ⟨hdeg, hfock⟩ := hQ L L'
    have hb := jet_bd D hJ i s (X.Th i s L L') (X.cf i s L L') (supB D u Cd i s) (X.cf_sum i hi s L L')
      (fun z => Th_tied D u X Cd h5 hS i hi s L L' (hth s L L') z) n (X.Q i s L L' x y).support
      (fun e he τ => by
        have := hdeg e he τ
        rw [← hn τ] at this
        exact_mod_cast this)
    unfold jetN at hb
    have hJs : (∑ e ∈ (X.Q i s L L' x y).support, (e.prod fun _ k => (k.factorial : ℝ)) * ‖X.cf i s L L' e‖ ^ 2) ≤
        supB D u Cd i s * jetF D i n * (∏ τ, D.gx.Om τ s ^ n τ)⁻¹ := by
      rwa [le_mul_inv_iff₀ (prod_om_pow_pos D s n)]
    have hJ0 : 0 ≤ supB D u Cd i s * jetF D i n * (∏ τ, D.gx.Om τ s ^ n τ)⁻¹ := by
      have := supB_nonneg D u Cd i s hv
      have := jetF_nonneg D i n
      have := (prod_om_pow_pos D s n).le
      positivity
    have hf0 : 0 ≤ fockSq (X.Q i s L L' x y) := by
      unfold fockSq
      refine Finset.sum_nonneg fun e _ => mul_nonneg (by positivity) ?_
      exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    have haa : 0 ≤ X.nrm i s L x * X.nrm (i + 1) s L' y := mul_nonneg (ha0 L) (ha'0 L')
    have hf1 : fockSq (X.Q i s L L' x y) ≤
        max (∏ τ, hook (nuLift D u τ i)) 0 * (X.nrm i s L x * X.nrm (i + 1) s L' y) := by
      refine le_trans hfock ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) haa
    have hsq : ‖jet (X.cf i s L L') (X.Q i s L L' x y)‖ ^ 2 ≤ M * (X.nrm i s L x * X.nrm (i + 1) s L' y) := by
      refine le_trans (jet_sq_le _ _) (le_trans (mul_le_mul hf1 hJs ?_ ?_) (le_of_eq ?_))
      · refine Finset.sum_nonneg fun e _ => mul_nonneg ?_ (by positivity)
        exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
      · exact mul_nonneg (le_max_right _ _) haa
      · rw [hM]; unfold blockB; ring
    have := Real.le_sqrt_of_sq_le hsq
    rwa [Real.sqrt_mul hM0, Real.sqrt_mul (ha0 L)] at this
  have per : ∀ L', X.nrm (i + 1) s L' y ≤ (Fintype.card ((D.mem u).C.cls i) : ℝ) * M * Sx := by
    intro L'
    set r := Real.sqrt M * ∑ L, ((Nat.card ((D.mem u).C.stab i L) : ℝ))⁻¹ * Real.sqrt (X.nrm i s L x) with hr
    have hr0 : 0 ≤ r := mul_nonneg (Real.sqrt_nonneg _)
      (Finset.sum_nonneg fun c _ => mul_nonneg (hw0 c) (Real.sqrt_nonneg _))
    have h1 : X.nrm (i + 1) s L' y ≤ Real.sqrt (X.nrm (i + 1) s L' y) * r := by
      have e1 : X.nrm (i + 1) s L' y =
          (∑ L, ((Nat.card ((D.mem u).C.stab i L) : ℂ))⁻¹ * jet (X.cf i s L L') (X.Q i s L L' x y)).re := by
        rw [← hker L']; rfl
      refine le_trans (le_of_eq e1) (le_trans (Complex.re_le_norm _) (le_trans (norm_sum_le _ _) ?_))
      rw [hr, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun L _ => ?_
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc ((Nat.card ((D.mem u).C.stab i L) : ℝ))⁻¹ * ‖jet (X.cf i s L L') (X.Q i s L L' x y)‖
          ≤ ((Nat.card ((D.mem u).C.stab i L) : ℝ))⁻¹ *
            (Real.sqrt M * (Real.sqrt (X.nrm i s L x) * Real.sqrt (X.nrm (i + 1) s L' y))) :=
            mul_le_mul_of_nonneg_left (hjet L L') (hw0 L)
        _ = _ := by ring
    have h2 := le_sq_of_le_sqrt_mul (ha'0 L') hr0 h1
    refine le_trans h2 ?_
    rw [hr, mul_pow, Real.sq_sqrt hM0]
    have h3 : (∑ L, ((Nat.card ((D.mem u).C.stab i L) : ℝ))⁻¹ * Real.sqrt (X.nrm i s L x)) ^ 2 ≤
        (Fintype.card ((D.mem u).C.cls i) : ℝ) * Sx := by
      refine le_trans sq_sum_le_card_mul_sum_sq ?_
      rw [Finset.card_univ]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun L _ => ?_) (by positivity)
      rw [mul_pow, Real.sq_sqrt (ha0 L), sq]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (hw0 L) (hw1 L)) (ha0 L)
    calc M * _ ≤ M * ((Fintype.card ((D.mem u).C.cls i) : ℝ) * Sx) := mul_le_mul_of_nonneg_left h3 hM0
      _ = _ := by ring
  calc ∑ c, ((Nat.card ((D.mem u).C.stab (i + 1) c) : ℝ))⁻¹ * X.nrm (i + 1) s c y
      ≤ ∑ _c : (D.mem u).C.cls (i + 1), (Fintype.card ((D.mem u).C.cls i) : ℝ) * M * Sx :=
        Finset.sum_le_sum fun c _ => le_trans (mul_le_of_le_one_left (ha'0 c) (hw'1 c)) (per c)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Z1a

section Z1b
open Formalism.BasicNotions NumberField

theorem abs_le_exp_log (x : ℝ) : |x| ≤ Real.exp (Real.log x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Real.exp_log_eq_abs hx]

theorem pow_eq_exp {a : ℝ} (ha : 0 < a) (n : ℕ) : a ^ n = Real.exp (n * Real.log a) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos ha, mul_comm]

theorem nums_logs {D : D7} {T g1 g2 : ℕ} {Cn x b L b' Sc eta : ℝ}
    (hN : Nums D T g1 g2 Cn x b L b' Sc eta) :
    (∀ n : ℕ, 1 ≤ n → n ≤ D.R.N D.R.m → Real.log n ≤ L) ∧ Real.log D.host.v ≤ L ∧ Real.log (x * b) ≤ L ∧
      8 ≤ x * b ∧ Sc ≤ b' ∧ eta + 1 ≤ b' := by
  obtain ⟨hL1, hCn, hb'4, hbb', hNb, hSe, hL, h8⟩ := b_nums hN
  obtain ⟨hb, -, -, -, -, -, hSc, heta, -, -, -, -, -, hx, hv, -⟩ := hN
  have hmt : (0 : ℝ) ≤ D.R.m * D.R.t := by positivity
  have hxb : 8 ≤ x * b := by nlinarith [mul_le_mul hx (hb'4.trans hbb') (by norm_num) (by linarith)]
  have hxbv : x * b ≤ x * b * D.host.v := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x * b) (by linarith : (0 : ℝ) ≤ D.host.v - 1)]
  have hbxb : b ≤ x * b := by nlinarith
  refine ⟨fun n hn1 hnN => ?_, ?_, ?_, hxb, by linarith, by linarith⟩
  · have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
    have hnN' : (n : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast hnN
    have hle : (n : ℝ) ≤ x * b * D.host.v := by linarith
    exact (Real.log_le_log hn hle).trans hL
  · have hle : D.host.v ≤ x * b * D.host.v := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x * b - 1) (by linarith : (0 : ℝ) ≤ D.host.v)]
    exact (Real.log_le_log (by linarith) hle).trans hL
  · exact (Real.log_le_log (by linarith) hxbv).trans hL

theorem wJ_mono {D : D7} {u : D.what₂.Word} {Cn x b b' Sc eta : ℝ} (hW : Wts D u Cn x b b' Sc eta)
    (τ : D.what₂.Tau) : ∀ j, j < D.R.m → wJ D u τ 0 ≤ wJ D u τ j
  | 0, _ => le_rfl
  | j + 1, h => le_trans (wJ_mono hW τ j (by omega)) ((hW τ).2.2.2.1 j h)

theorem nuLift_le {D : D7} {u : D.what₂.Word} {Cn x b L b' Sc eta : ℝ}
    (hN : Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta) (hW : Wts D u Cn x b b' Sc eta)
    (τ : D.what₂.Tau) (i : ℕ) (hi : i < D.R.m) (a : Fin (D.R.N i)) :
    (nuLift D u τ i a : ℝ) ≤ (3 + Cn) * (x * b) := by
  classical
  obtain ⟨hL1, hCn, h4, hbb⟩ := nums_basic hN
  obtain ⟨-, -, -, h8, hScb, hetab⟩ := nums_logs hN
  have hx2 : 2 ≤ x := hN.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb0 : 0 < b := hN.1
  have hSc : 1 ≤ Sc := hN.2.2.2.2.2.2.1
  have h2b : 2 * b ≤ x * b := mul_le_mul_of_nonneg_right hx2 hb0.le
  have hk := D.R.m_add_three_le_k
  have hw : (wJ D u τ i : ℝ) ≤ x * b := by
    by_cases ht : IsThick D τ
    · have := ((hW τ).2.2.2.2.2.1 ht i hi).2
      linarith
    · have := (hW τ).2.2.2.2.1 ht i hi
      linarith
  have hcol : ∀ c, c < D.R.k → (lamCol D u τ c : ℝ) ≤ (2 + Cn) * (x * b) := by
    intro c hc
    have hCxb : 0 ≤ Cn * (x * b) := by positivity
    by_cases ht : IsTop D τ
    · obtain ⟨-, t2, t3, -, t5⟩ := (hW τ).2.1 ht
      by_cases h0 : c = 0
      · subst h0; linarith
      by_cases h1 : c = D.R.k - 1
      · subst h1; linarith
      · have := (t5 c (by omega) (by omega)).2
        linarith
    · have h1 := ((hW τ).2.2.1 ht c hc).2
      have h2 : Cn * Sc ≤ Cn * (x * b) := mul_le_mul_of_nonneg_left (by linarith) hCn
      linarith
  have hlift : (lamLiftN D u τ a : ℝ) ≤ (2 + Cn) * (x * b) := by
    unfold lamLiftN
    split_ifs with hc
    · exact hcol _ hc
    · by_cases hj : ((a : ℕ) - D.R.k) / (D.R.t + 1) < D.R.m
      · have h1 := wJ_mono hW τ _ hj
        have h2 := (hW τ).2.2.2.2.2.2.1
        have h3 : -wJ D u τ (((a : ℕ) - D.R.k) / (D.R.t + 1)) ≤ lamCol D u τ (D.R.k - 1) := by linarith
        have h4 : ((-wJ D u τ (((a : ℕ) - D.R.k) / (D.R.t + 1)) : ℚ) : ℝ) ≤ (lamCol D u τ (D.R.k - 1) : ℝ) := by
          exact_mod_cast h3
        exact le_trans h4 (hcol _ (by omega))
      · have : wJ D u τ (((a : ℕ) - D.R.k) / (D.R.t + 1)) = 0 := by unfold wJ; rw [dif_neg hj]
        rw [this]; simp; positivity
  unfold nuLift
  push_cast
  linarith

theorem blockB_le (D : D7) (u : D.what₂.Word) (Cd : ℝ) (i : ℕ) (s : D.what₂.LL →+* ℂ) (n : D.what₂.Tau → ℕ)
    (hv : 0 ≤ D.host.v) :
    blockB D u Cd i s n ≤ Real.exp (Cd * D.R.f *
        ((D.R.m : ℝ) ^ 2 * D.R.N (i + 1) + (D.R.N i : ℝ) * D.R.N (i + 1)) *
        (Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) +
      ((∑ τ, (Real.log (hook (nuLift D u τ i)) - n τ * Real.log (D.gx.Om τ s))) +
        ((((D.R.f : ℝ) * D.R.N i * D.R.N (i + 1)) * Real.log 4 +
          ((D.R.f : ℝ) * D.R.N i * D.R.N (i + 1)) *
            Real.log (2 + 8 * ((D.R.f : ℝ) * D.R.N i * D.R.N (i + 1)) * D.host.v) +
          Real.log (thetaLocalFactorAtIndex D u i s ^ 2)) +
        ∑ τ, ((D.R.N i : ℝ) * D.R.N (i + 1)) *
          Real.log (2 * Real.exp 1 * max 1 ((n τ : ℝ) / ((D.R.N i : ℝ) * D.R.N (i + 1))))))) := by
  have eH : max (∏ τ, hook (nuLift D u τ i)) 0 ≤ Real.exp (∑ τ, Real.log (hook (nuLift D u τ i))) := by
    refine max_le ?_ (Real.exp_pos _).le
    refine le_trans (le_abs_self _) ?_
    rw [Finset.abs_prod, Real.exp_sum]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun τ _ => abs_le_exp_log _
  have hth : 0 < thetaLocalFactorAtIndex D u i s ^ 2 := by
    unfold thetaLocalFactorAtIndex
    have := D.gx.thOne_pos s
    positivity
  have eS : supB D u Cd i s = Real.exp (Cd * D.R.f *
        ((D.R.m : ℝ) ^ 2 * D.R.N (i + 1) + (D.R.N i : ℝ) * D.R.N (i + 1)) *
        (Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) +
        (((D.R.f : ℝ) * D.R.N i * D.R.N (i + 1)) * Real.log 4 +
          ((D.R.f : ℝ) * D.R.N i * D.R.N (i + 1)) *
            Real.log (2 + 8 * ((D.R.f : ℝ) * D.R.N i * D.R.N (i + 1)) * D.host.v) +
          Real.log (thetaLocalFactorAtIndex D u i s ^ 2))) := by
    unfold supB
    rw [pow_eq_exp (by norm_num : (0 : ℝ) < 4), pow_eq_exp (a := 2 + 8 * _ * D.host.v) (by positivity),
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hth]
    push_cast
    ring_nf
  have eJ : jetF D i n = Real.exp (∑ τ, ((D.R.N i : ℝ) * D.R.N (i + 1)) *
          Real.log (2 * Real.exp 1 * max 1 ((n τ : ℝ) / ((D.R.N i : ℝ) * D.R.N (i + 1))))) := by
    unfold jetF
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [pow_eq_exp (by positivity)]
    push_cast
    ring_nf
  have eO : (∏ τ, D.gx.Om τ s ^ n τ)⁻¹ = Real.exp (-∑ τ, (n τ : ℝ) * Real.log (D.gx.Om τ s)) := by
    rw [Real.exp_neg, Real.exp_sum]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => pow_eq_exp (D.gx.Om_pos τ s) _
  unfold blockB
  rw [eS, eJ, eO, ← Real.exp_add, ← Real.exp_add]
  refine le_trans (mul_le_mul_of_nonneg_right eH (Real.exp_pos _).le) ?_
  rw [← Real.exp_add, Finset.sum_sub_distrib]
  exact Real.exp_le_exp.2 (le_of_eq (by ring))

end Z1b

section continuousCocycles
open Formalism.BasicNotions NumberField

theorem opNormSq_le_of_not_integral_weight (D : D7) (u : D.what₂.Word) (X : KerData D u) (hCM : X.ConjMetric) (hG : AdmittedGaloisConjugateKernels X)
    (i : ℕ) (hi : i < D.R.m) (hK : (D.fm u).KRat i) (s : D.what₂.LL →+* ℂ)
    (hn : ¬ ∃ n : D.what₂.Tau → ℕ, ∀ τ, ((n τ : ℕ) : ℚ) = absQ (nuLift D u τ i)) (c : ℝ) (hc : 0 ≤ c) :
    opSq D ((D.fm u).lat i) ((D.fm u).lat (i + 1)) s ((D.fm u).KL i hK) ≤ c := by
  refine opNormAt_sq_le _ _ _ _ ((D.fm u).lat_good i).1 (InfinitePlace.mk s)
    (IsTotallyComplex.isComplex _) ((D.fm u).KL i hK) _ hc (fun x => ?_)
  rw [hCM.2.2 (i + 1) (by omega) s _, hCM.2.2 i hi.le s x]
  obtain ⟨hker, hQ⟩ := hG s i hi hK x ((D.fm u).KL i hK x)
  have hz : ∀ L', X.nrm (i + 1) s L' ((D.fm u).KL i hK x) = 0 := by
    intro L'
    have e1 : X.nrm (i + 1) s L' ((D.fm u).KL i hK x) =
        (∑ L, ((Nat.card ((D.mem u).C.stab i L) : ℂ))⁻¹ *
          jet (X.cf i s L L') (X.Q i s L L' x ((D.fm u).KL i hK x))).re := by
      rw [← hker L']; rfl
    rw [e1, Finset.sum_eq_zero, Complex.zero_re]
    intro L _
    have hs : (X.Q i s L L' x ((D.fm u).KL i hK x)).support = ∅ := by
      by_contra hne
      obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.2 hne
      exact hn ⟨_, fun τ => (hQ L L').1 e he τ⟩
    unfold jet
    rw [hs, Finset.sum_empty, mul_zero]
  simp only [hz, mul_zero, Finset.sum_const_zero]
  exact mul_nonneg hc (Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (hCM.2.1 i hi.le s c x))

def lBl (D : D7) (u : D.what₂.Word) (i : ℕ) (s : D.what₂.LL →+* ℂ) (n : D.what₂.Tau → ℕ) : ℝ :=
  ∑ τ, (Real.log (hook (nuLift D u τ i)) - n τ * Real.log (D.gx.Om τ s))

def logSupBoundLevelFree (D : D7) (u : D.what₂.Word) (i : ℕ) (s : D.what₂.LL →+* ℂ) : ℝ :=
  ((D.R.f : ℝ) * D.R.N i * D.R.N (i + 1)) * Real.log 4 +
    ((D.R.f : ℝ) * D.R.N i * D.R.N (i + 1)) *
      Real.log (2 + 8 * ((D.R.f : ℝ) * D.R.N i * D.R.N (i + 1)) * D.host.v) +
    Real.log (thetaLocalFactorAtIndex D u i s ^ 2)

def lJ (D : D7) (i : ℕ) (n : D.what₂.Tau → ℕ) : ℝ :=
  ∑ τ, ((D.R.N i : ℝ) * D.R.N (i + 1)) *
    Real.log (2 * Real.exp 1 * max 1 ((n τ : ℝ) / ((D.R.N i : ℝ) * D.R.N (i + 1))))

theorem ranks_facts (D : D7) (i : ℕ) (hi : i < D.R.m) :
    1 ≤ D.R.N i ∧ 1 ≤ D.R.N (i + 1) ∧ D.R.N i ≤ D.R.N (i + 1) ∧ D.R.N (i + 1) ≤ D.R.N D.R.m ∧ 1 ≤ D.R.m ∧
      1 ≤ D.R.f ∧ D.R.f ≤ D.R.N D.R.m ∧ D.R.N D.R.m ≤ D.R.m * D.R.N (i + 1) := by
  have hm1 : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  refine ⟨N_pos' D i, N_pos' D (i + 1), ?_, ?_, hm1, ?_, ?_, ?_⟩
  · unfold Ranks.N; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ i)) _
  · unfold Ranks.N; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  · exact b_one_le_f D
  · have := D.R.f_le_k
    unfold Ranks.f Ranks.n Ranks.N
    omega
  · unfold Ranks.N
    have a1 : D.R.k ≤ D.R.m * D.R.k := Nat.le_mul_of_pos_left _ hm1
    have a2 : D.R.m * (D.R.t + 1) ≤ D.R.m * ((i + 1) * (D.R.t + 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos i))
    calc D.R.k + D.R.m * (D.R.t + 1) ≤ D.R.m * D.R.k + D.R.m * ((i + 1) * (D.R.t + 1)) := Nat.add_le_add a1 a2
      _ = D.R.m * (D.R.k + (i + 1) * (D.R.t + 1)) := (Nat.mul_add _ _ _).symm

theorem n_size {D : D7} {u : D.what₂.Word} {Cn x b L b' Sc eta : ℝ}
    (hN : Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta) (hW : Wts D u Cn x b b' Sc eta)
    (i : ℕ) (hi : i < D.R.m) (n : D.what₂.Tau → ℕ) (hnR : ∀ τ, (n τ : ℝ) = (absQ (nuLift D u τ i) : ℝ)) (τ : D.what₂.Tau) :
    Real.log (max 1 ((n τ : ℝ) / ((D.R.N i : ℝ) * D.R.N (i + 1)))) ≤ (Cn + 4) * L := by
  obtain ⟨hL1, hCn, h4, hbb⟩ := nums_basic hN
  obtain ⟨hlogn, hlv, hlxb, h8, -, -⟩ := nums_logs hN
  obtain ⟨hN1, hN'1, -⟩ := ranks_facts D i hi
  have hNR : (1 : ℝ) ≤ (D.R.N i : ℝ) := by exact_mod_cast hN1
  have hN'R : (1 : ℝ) ≤ (D.R.N (i + 1) : ℝ) := by exact_mod_cast hN'1
  have h1 : (n τ : ℝ) ≤ (D.R.N i : ℝ) * ((3 + Cn) * (x * b)) := by
    rw [hnR τ]
    unfold absQ
    push_cast
    refine le_trans (Finset.sum_le_sum fun a _ => nuLift_le hN hW τ i hi a) ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hxb0 : 0 < x * b := by linarith
  have hU : 0 ≤ (3 + Cn) * (x * b) := by positivity
  have h2 : (n τ : ℝ) / ((D.R.N i : ℝ) * D.R.N (i + 1)) ≤ (3 + Cn) * (x * b) := by
    rw [div_le_iff₀ (by positivity)]
    calc (n τ : ℝ) ≤ (D.R.N i : ℝ) * ((3 + Cn) * (x * b)) := h1
      _ ≤ (D.R.N i : ℝ) * ((3 + Cn) * (x * b)) * D.R.N (i + 1) :=
          le_mul_of_one_le_right (by positivity) hN'R
      _ = _ := by ring
  have h3 : max 1 ((n τ : ℝ) / ((D.R.N i : ℝ) * D.R.N (i + 1))) ≤ (3 + Cn) * (x * b) :=
    max_le (by nlinarith) h2
  refine le_trans (Real.log_le_log (by positivity) h3) ?_
  rw [Real.log_mul (by positivity) hxb0.ne']
  have h4 : Real.log (3 + Cn) ≤ 3 + Cn := Real.log_le_self (by linarith)
  nlinarith

theorem arith_log_constant_combination (C C1 Cd f m N N' Nm L lT lg : ℝ) (hf : 0 ≤ f) (hm : 1 ≤ m) (hN : 0 ≤ N) (hNN : N ≤ N')
    (hN' : 1 ≤ N') (hNm0 : 0 ≤ Nm) (hNm : Nm ≤ m * N') (hL : 0 ≤ L) (hT : 0 ≤ lT) (hg : 0 ≤ lg) :
    C1 * f * Nm ^ 2 * (L + lT + lg) + (C1 * f * Nm ^ 2 * (L + lT + lg) +
        (Cd * f * (m ^ 2 * N' + N * N') * (lT + lg) + C * f * m ^ 2 * N' ^ 2 * (L + lT + lg))) ≤
      (max C 0 + 2 * max C1 0 + 2 * |Cd|) * f * m ^ 2 * N' ^ 2 * (L + lT + lg) := by
  have hP0 : 0 ≤ L + lT + lg := by linarith
  obtain ⟨W, hWd⟩ : ∃ W, W = f * m ^ 2 * N' ^ 2 * (L + lT + lg) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hWd]; positivity
  have c1 : C1 * f * Nm ^ 2 * (L + lT + lg) ≤ max C1 0 * W := by
    have hsq : Nm ^ 2 ≤ m ^ 2 * N' ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hNm0 hNm 2
    calc C1 * f * Nm ^ 2 * (L + lT + lg) = C1 * (f * Nm ^ 2 * (L + lT + lg)) := by ring
      _ ≤ max C1 0 * (f * Nm ^ 2 * (L + lT + lg)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C1 0 * W := by
          refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
          rw [hWd]
          calc f * Nm ^ 2 * (L + lT + lg) ≤ f * (m ^ 2 * N' ^ 2) * (L + lT + lg) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hf) hP0
            _ = _ := by ring
  have c5 : Cd * f * (m ^ 2 * N' + N * N') * (lT + lg) ≤ 2 * |Cd| * W := by
    have hm2 : 1 ≤ m ^ 2 := one_le_pow₀ hm
    have hN'0 : 0 ≤ N' := by linarith
    have hNsq : N' ≤ N' ^ 2 := by nlinarith
    have b1 : m ^ 2 * N' ≤ m ^ 2 * N' ^ 2 := mul_le_mul_of_nonneg_left hNsq (by positivity)
    have b2 : N * N' ≤ m ^ 2 * N' ^ 2 := by
      have h1 : N * N' ≤ N' ^ 2 := by nlinarith
      have h' : N' ^ 2 ≤ m ^ 2 * N' ^ 2 := le_mul_of_one_le_left (by positivity) hm2
      linarith
    calc Cd * f * (m ^ 2 * N' + N * N') * (lT + lg) = Cd * (f * (m ^ 2 * N' + N * N') * (lT + lg)) := by ring
      _ ≤ |Cd| * (f * (m ^ 2 * N' + N * N') * (lT + lg)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Cd| * (f * (2 * (m ^ 2 * N' ^ 2)) * (L + lT + lg)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hf) (by linarith)
            (by positivity) (by positivity)
      _ = 2 * |Cd| * W := by rw [hWd]; ring
  have cC : C * f * m ^ 2 * N' ^ 2 * (L + lT + lg) ≤ max C 0 * W := by
    calc C * f * m ^ 2 * N' ^ 2 * (L + lT + lg) = C * W := by rw [hWd]; ring
      _ ≤ max C 0 * W := mul_le_mul_of_nonneg_right (le_max_left _ _) hW0
  have fin : (max C 0 + 2 * max C1 0 + 2 * |Cd|) * f * m ^ 2 * N' ^ 2 * (L + lT + lg) =
      max C 0 * W + 2 * (max C1 0 * W) + 2 * |Cd| * W := by rw [hWd]; ring
  rw [fin]
  linarith

theorem log_opNorm_sup_bound (Cn : ℝ) : ∃ C : ℝ, ∀ (D : D7) (u : D.what₂.Word) (x b L b' Sc eta : ℝ),
    Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn x b L b' Sc eta → Wts D u Cn x b b' Sc eta →
    ∀ i < D.R.m, ∀ (s : D.what₂.LL →+* ℂ) (n : D.what₂.Tau → ℕ), (∀ τ, (n τ : ℝ) = (absQ (nuLift D u τ i) : ℝ)) →
      lBl D u i s n + (logSupBoundLevelFree D u i s + lJ D i n) ≤ lBl D u i s n + Real.log (thetaLocalFactorAtIndex D u i s ^ 2) +
        C * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N (i + 1) : ℝ) ^ 2 *
          (L + Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) := by
  obtain ⟨C, hC⟩ := Formalism.HermitianLattices.TraceIntegrality.first_zeta_arithmetic_bound (max Cn 0 + 4) (by positivity)
  refine ⟨C, fun D u x b L b' Sc eta hN hW i hi s n hnR => ?_⟩
  obtain ⟨hL1, hCn, h4, hbb⟩ := nums_basic hN
  rw [max_eq_left hCn] at hC
  obtain ⟨hlogn, hlv, hlxb, h8, -, -⟩ := nums_logs hN
  have hx2 : 2 ≤ x := hN.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hNum := numbers_of_nums 1 le_rfl (by linarith) hN
  obtain ⟨hN1, hN'1, hNN', hN'm, hm1, hf1, hfN, -⟩ := ranks_facts D i hi
  have hN'R : (1 : ℝ) ≤ (D.R.N (i + 1) : ℝ) := by exact_mod_cast hN'1
  have hfR : (1 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast hf1
  have hlT0 := hNum.logT_nonneg
  have hlg0 := hNum.logg_nonneg
  have key := hC D.what₂.Tau (D.R.N i) (D.R.N (i + 1)) D.R.m n (fun τ => Real.log (hook (nuLift D u τ i)))
    (fun τ => Real.log (D.gx.Om τ s)) D.host.v L (Real.log (Tu D u)) (Real.log ((D.host.g 0 : ℝ) * D.host.g 1))
    (lBl D u i s n + (logSupBoundLevelFree D u i s + lJ D i n)) 0 0 0 (lBl D u i s n + (logSupBoundLevelFree D u i s + lJ D i n))
    (logSupBoundLevelFree D u i s + lJ D i n) (logSupBoundLevelFree D u i s) (Real.log (thetaLocalFactorAtIndex D u i s ^ 2))
  rw [D.what₂.card_Tau] at key
  have hlfN : 0 ≤ Real.log ((D.R.f : ℝ) * D.R.N (i + 1)) := Real.log_nonneg (by nlinarith)
  exact key hf1 hN1 hNN' hm1 hNum.one_le_v hL1 hlT0 hlg0 (hlogn _ hf1 hfN) (hlogn _ hN'1 hN'm) hlv
    (n_size hN hW i hi n hnR) (by linarith) (by positivity) (by positivity) (by positivity) le_rfl le_rfl le_rfl

theorem slopeEstimate_of_lemmaB_slopeLine (Cn Cd C1 : ℝ) : ∃ C : ℝ, ∀ (D : D7) (x Cth : ℝ),
    ThetaSupremumBound D → JetInt D → adm2 D Cn Cth x → Conclusion1 D Cn C1 x → Conclusion2 D Cn Cd C x := by
  obtain ⟨C, hC⟩ := log_opNorm_sup_bound Cn
  refine ⟨max C 0 + 2 * max C1 0 + 2 * |Cd|,
    fun D x Cth hS hJ h2 h1 u b L b' Sc eta hN hW hT X hCM hG h5 i hi hK s => ?_⟩
  obtain ⟨hL1, hCn, h4, hbb⟩ := nums_basic hN
  have hx2 : 2 ≤ x := hN.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hNum := numbers_of_nums 1 le_rfl (by linarith) hN
  have hv1 : 1 ≤ D.host.v := hNum.one_le_v
  by_cases hn : ∃ n : D.what₂.Tau → ℕ, ∀ τ, ((n τ : ℕ) : ℚ) = absQ (nuLift D u τ i)
  swap
  · exact opNormSq_le_of_not_integral_weight D u X hCM hG i hi hK s hn _ (Real.exp_pos _).le
  obtain ⟨n, hn⟩ := hn
  have hnR : ∀ τ, (n τ : ℝ) = (absQ (nuLift D u τ i) : ℝ) := fun τ => by rw [← hn τ]; norm_cast
  have hex := opNormSq_eq_of_integral_weight D u X hCM hG Cd h5 hS hJ (by linarith) i hi
    (fun s' c c' => (h2 u b L b' Sc eta hN i hi).1 s' c c') hK s n hn
  obtain ⟨hcl, -⟩ := h1 u b L b' Sc eta hN hT
  have key2 := hC D u x b L b' Sc eta hN hW i hi s n hnR
  have hlT0 := hNum.logT_nonneg
  have hlg0 := hNum.logg_nonneg
  obtain ⟨hN1, hN'1, hNN', hN'm, hm1, hf1, hfN, hNmm⟩ := ranks_facts D i hi
  have hh : ∀ j ≤ D.R.m, (Fintype.card ((D.mem u).C.cls j) : ℝ) ≤
      Real.exp (C1 * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 *
        (L + Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1))) := fun j hj =>
    le_trans (le_trans (le_abs_self _) (abs_le_exp_log _)) (Real.exp_le_exp.2 (hcl j hj))
  have hB : blockB D u Cd i s n ≤ Real.exp (Cd * D.R.f *
        ((D.R.m : ℝ) ^ 2 * D.R.N (i + 1) + (D.R.N i : ℝ) * D.R.N (i + 1)) *
        (Real.log (Tu D u) + Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) +
      (lBl D u i s n + (logSupBoundLevelFree D u i s + lJ D i n))) := blockB_le D u Cd i s n (by linarith)
  have hB0 : 0 ≤ blockB D u Cd i s n := by
    unfold blockB
    have := supB_nonneg D u Cd i s (by linarith)
    have := jetF_nonneg D i n
    have := (prod_om_pow_pos D s n).le
    positivity
  refine le_trans hex ?_
  refine le_trans (mul_le_mul (hh (i + 1) hi) (mul_le_mul (hh i hi.le) hB hB0 (Real.exp_pos _).le)
    (by positivity) (Real.exp_pos _).le) ?_
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hsum : (∑ τ, (Real.log (hook (nuLift D u τ i)) - (absQ (nuLift D u τ i) : ℝ) * Real.log (D.gx.Om τ s))) =
      lBl D u i s n := by
    unfold lBl
    exact Finset.sum_congr rfl fun τ _ => by rw [hnR τ]
  rw [hsum]
  have ar := arith_log_constant_combination C C1 Cd D.R.f D.R.m (D.R.N i) (D.R.N (i + 1)) (D.R.N D.R.m) L (Real.log (Tu D u))
    (Real.log ((D.host.g 0 : ℝ) * D.host.g 1)) (by positivity) (by exact_mod_cast hm1) (by positivity)
    (by exact_mod_cast hNN') (by exact_mod_cast hN'1) (by positivity) (by exact_mod_cast hNmm) (by linarith) hlT0 hlg0
  linarith

def JetIntF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ (x : ℝ) (i : Fm.Ix x), JetInt (Fm.D x i)

theorem familyOpNorm_of_sup_jet {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hS : FamilySupremumBound Fm) (hJ : JetIntF Fm) (h2 : admF2 Fm)
    (h1 : ConclusionF1 Fm) : ConclusionF2 Fm := by
  intro Cn Cd
  obtain ⟨C1, x1, H1⟩ := h1 Cn
  obtain ⟨Cth, x2, H2⟩ := h2 Cn
  obtain ⟨C, hC⟩ := slopeEstimate_of_lemmaB_slopeLine Cn Cd C1
  exact ⟨C, max x1 x2, fun x hx hx1 i => hC _ x Cth (hS x i) (hJ x i)
    (H2 x (le_trans (le_max_right _ _) hx) hx1 i) (H1 x (le_trans (le_max_left _ _) hx) hx1 i)⟩

end continuousCocycles

section JI
open Formalism.BasicNotions NumberField

def GaussBessel : Prop :=
  ∀ (ι : Type) [Fintype ι] (ε : ι → ℝ) (F : (ι → ℂ) → ℂ) (c : (ι →₀ ℕ) → ℂ) (S2 : ℝ),
    (∀ g, 0 < ε g) → (∀ z, HasSum (fun e => c e * e.prod fun g k => z g ^ k) (F z)) →
    (∀ z, ‖F z‖ ^ 2 * Real.exp (-∑ g, ‖z g‖ ^ 2) ≤ S2) →
    ∀ E : Finset (ι →₀ ℕ),
      ∑ e ∈ E, ‖c e‖ ^ 2 * ∏ g, (((e g).factorial : ℝ) * ((1 + ε g) ^ (e g + 1))⁻¹) ≤ S2 * ∏ g, (ε g)⁻¹

theorem jetInt_of (hG : GaussBessel) (D : D7) : JetInt D := by
  classical
  intro i s Th cf S2 h1 h2 n E hE
  have hg1 : 1 ≤ D.R.N i * D.R.N (i + 1) := Nat.mul_pos (N_pos' D i) (N_pos' D (i + 1))
  have hcard : (Finset.univ : Finset (Fin (D.R.N i) × Fin (D.R.N (i + 1)))).card = D.R.N i * D.R.N (i + 1) := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, g₀ = D.R.N i * D.R.N (i + 1) := ⟨_, rfl⟩
  rw [← hg₀] at hg1 hcard ⊢
  obtain ⟨ε, hε⟩ : ∃ ε : D.what₂.Tau → ℝ, ∀ τ, ε τ = if n τ = 0 then (1 : ℝ) else min 1 ((g₀ : ℝ) / n τ) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hε]
  have hε0 : ∀ τ, 0 < ε τ := fun τ => by
    rw [hε τ]
    split_ifs with h
    · exact one_pos
    · have h1 : (0 : ℝ) < (n τ : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
      have h2 : (0 : ℝ) < (g₀ : ℝ) := by exact_mod_cast hg1
      exact lt_min one_pos (div_pos h2 h1)
  have hom : ∀ g : Gx D i, 0 < D.gx.Om g.1 s := fun g => D.gx.Om_pos g.1 s
  obtain ⟨r, hr⟩ : ∃ r : Gx D i → ℝ, ∀ g, r g = Real.sqrt (D.gx.Om g.1 s) := ⟨_, fun _ => rfl⟩
  have hr2 : ∀ g, r g ^ 2 = D.gx.Om g.1 s := fun g => by rw [hr g]; exact Real.sq_sqrt (hom g).le
  have key := hG (Gx D i) (fun g => ε g.1) (fun z => Th fun g => (r g : ℂ) * z g)
    (fun e => cf e * e.prod fun g k => (r g : ℂ) ^ k) S2 (fun g => hε0 g.1)
    (fun z => by
      have h := h1 fun g => (r g : ℂ) * z g
      have e1 : (fun e : Gx D i →₀ ℕ => (cf e * e.prod fun g k => (r g : ℂ) ^ k) * e.prod fun g k => z g ^ k) =
          fun e => cf e * e.prod fun g k => ((r g : ℂ) * z g) ^ k := by
        funext e
        rw [mul_assoc, ← Finsupp.prod_mul]
        simp only [mul_pow]
      rw [e1]; exact h)
    (fun z => by
      have h := h2 fun g => (r g : ℂ) * z g
      unfold dens at h
      have hH : -Real.pi * Hq D i s (fun g => (r g : ℂ) * z g) = -∑ g, ‖z g‖ ^ 2 := by
        unfold Hq
        rw [neg_mul, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hr2 g]
        have := hom g
        have := Real.pi_pos
        field_simp
      rwa [hH] at h) E
  have hR : ∏ g : Gx D i, (ε g.1)⁻¹ = ∏ τ, ((ε τ) ^ g₀)⁻¹ := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun τ _ => ?_
    dsimp only
    rw [Finset.prod_const, hcard, inv_pow]
  rw [hR] at key
  refine le_trans (le_of_eq ?_) key
  unfold jetN
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  have a1 : ‖cf e * e.prod fun g k => (r g : ℂ) ^ k‖ ^ 2 = ‖cf e‖ ^ 2 * ∏ τ, D.gx.Om τ s ^ n τ := by
    rw [norm_mul, mul_pow]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), norm_prod, ← Finset.prod_pow, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← hE e he τ, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun ac _ => ?_
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, ← pow_mul, mul_comm, pow_mul, sq_abs, hr2]
  have a2 : (e.prod fun _ k => (k.factorial : ℝ)) = ∏ g, ((e g).factorial : ℝ) :=
    Finsupp.prod_fintype _ _ (fun _ => by simp)
  have a3 : ∏ g : Gx D i, ((1 + ε g.1) ^ (e g + 1))⁻¹ = ∏ τ, ((1 + ε τ) ^ (n τ + g₀))⁻¹ := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun τ _ => ?_
    dsimp only
    rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, hE e he τ,
      Finset.sum_const, hcard, smul_eq_mul, mul_one]
  rw [a1, Finset.prod_mul_distrib, a3, a2]
  ring

end JI

section JG
open MeasureTheory

theorem gauss1 (a : ℝ) (ha : 0 < a) (p : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ (2 * p) * Real.exp (-(a * ‖z‖ ^ 2))) ∧
    ∫ z : ℂ, ‖z‖ ^ (2 * p) * Real.exp (-(a * ‖z‖ ^ 2)) = (p.factorial : ℝ) * (a ^ (p + 1))⁻¹ * Real.pi := by
  obtain ⟨h1, h2⟩ := Formalism.HermitianLattices.TraceIntegrality.fock_monomial_orthogonality a⁻¹ p p (inv_pos.2 ha)
  have e : (fun z : ℂ => z ^ p * (starRingEnd ℂ z) ^ p * (Real.exp (-‖z‖ ^ 2 / a⁻¹) : ℂ)) =
      fun z : ℂ => ((‖z‖ ^ (2 * p) * Real.exp (-(a * ‖z‖ ^ 2)) : ℝ) : ℂ) := by
    funext z
    rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, div_inv_eq_mul]
    push_cast
    rw [pow_mul]
    congr 2
    ring_nf
  rw [e] at h1 h2
  refine ⟨?_, ?_⟩
  · have := h1.re
    simpa only [RCLike.re_to_complex, Complex.ofReal_re] using this
  · rw [integral_complex_ofReal, if_pos rfl] at h2
    have := Complex.ofReal_injective h2
    rw [this, pow_succ, inv_pow]
    field_simp

theorem gauss0 (a : ℝ) (ha : 0 < a) :
    Integrable (fun z : ℂ => Real.exp (-(a * ‖z‖ ^ 2))) ∧ ∫ z : ℂ, Real.exp (-(a * ‖z‖ ^ 2)) = a⁻¹ * Real.pi := by
  have h := gauss1 a ha 0
  simpa using h

def PolyBessel : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : (ι → ℂ) → ℂ) (c : (ι →₀ ℕ) → ℂ) (B : ℝ) (z : ι → ℂ),
    (∀ w, HasSum (fun e => c e * e.prod fun g k => w g ^ k) (F w)) →
    (∀ w, (∀ g, ‖w g‖ = ‖z g‖) → ‖F w‖ ^ 2 ≤ B) →
    ∀ E : Finset (ι →₀ ℕ), ∑ e ∈ E, ‖c e‖ ^ 2 * ∏ g, ‖z g‖ ^ (2 * e g) ≤ B

theorem gaussBessel_of (h : PolyBessel) : GaussBessel := by
  intro ι _ ε F c S2 hε hF hb E
  have hε1 : ∀ g, 0 < 1 + ε g := fun g => by have := hε g; linarith
  have hpt : ∀ z : ι → ℂ,
      ∑ e ∈ E, ‖c e‖ ^ 2 * ∏ g, (‖z g‖ ^ (2 * e g) * Real.exp (-((1 + ε g) * ‖z g‖ ^ 2))) ≤
        S2 * ∏ g, Real.exp (-(ε g * ‖z g‖ ^ 2)) := by
    intro z
    have h1 := h ι F c (S2 * Real.exp (∑ g, ‖z g‖ ^ 2)) z hF (fun w hw => by
      have h0 := hb w
      have e : ∑ g, ‖w g‖ ^ 2 = ∑ g, ‖z g‖ ^ 2 := Finset.sum_congr rfl fun g _ => by rw [hw g]
      rw [e, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)] at h0
      exact h0) E
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-∑ g, (1 + ε g) * ‖z g‖ ^ 2)).le
    refine le_trans (le_of_eq ?_) (le_trans h2 (le_of_eq ?_))
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib]
      ring
    · rw [← Real.exp_sum, mul_assoc, ← Real.exp_add]
      congr 2
      rw [Finset.sum_neg_distrib, ← sub_eq_add_neg, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun g _ => by ring
  have hLi : ∀ e ∈ E, Integrable (fun z : ι → ℂ =>
      ‖c e‖ ^ 2 * ∏ g, (‖z g‖ ^ (2 * e g) * Real.exp (-((1 + ε g) * ‖z g‖ ^ 2)))) := fun e _ =>
    (Integrable.fintype_prod (f := fun g (x : ℂ) => ‖x‖ ^ (2 * e g) * Real.exp (-((1 + ε g) * ‖x‖ ^ 2)))
      fun g => (gauss1 (1 + ε g) (hε1 g) (e g)).1).const_mul _
  have hRi : Integrable (fun z : ι → ℂ => S2 * ∏ g, Real.exp (-(ε g * ‖z g‖ ^ 2))) :=
    (Integrable.fintype_prod (f := fun g (x : ℂ) => Real.exp (-(ε g * ‖x‖ ^ 2)))
      fun g => (gauss0 (ε g) (hε g)).1).const_mul _
  have hmono := integral_mono (integrable_finsetSum E hLi) hRi hpt
  rw [integral_finsetSum E hLi, integral_const_mul,
    integral_fintype_prod_volume_eq_prod (fun g (x : ℂ) => Real.exp (-(ε g * ‖x‖ ^ 2)))] at hmono
  have eL : ∀ e, ∫ z : ι → ℂ, ‖c e‖ ^ 2 * ∏ g, (‖z g‖ ^ (2 * e g) * Real.exp (-((1 + ε g) * ‖z g‖ ^ 2))) =
      (‖c e‖ ^ 2 * ∏ g, (((e g).factorial : ℝ) * ((1 + ε g) ^ (e g + 1))⁻¹)) * Real.pi ^ Fintype.card ι := by
    intro e
    rw [integral_const_mul,
      integral_fintype_prod_volume_eq_prod (fun g (x : ℂ) => ‖x‖ ^ (2 * e g) * Real.exp (-((1 + ε g) * ‖x‖ ^ 2)))]
    simp only [(gauss1 _ (hε1 _) _).2]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    ring
  simp only [eL, (gauss0 _ (hε _)).2] at hmono
  rw [← Finset.sum_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← mul_assoc] at hmono
  exact le_of_mul_le_mul_right hmono (by positivity)

end JG

section GrowthPolynomialOperator
open MeasureTheory Complex

def mu1 : Measure ℝ := (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Set.Ioc 0 (2 * Real.pi))

instance : IsProbabilityMeasure mu1 := ⟨by
  unfold mu1
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc, sub_zero,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top⟩

def E1 (k : ℤ) (t : ℝ) : ℂ := cexp ((((k : ℝ) * t : ℝ) : ℂ) * I)

theorem norm_circleChar (k : ℤ) (t : ℝ) : ‖E1 k t‖ = 1 := by
  unfold E1
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_circleChar (k : ℤ) : Continuous (E1 k) := by
  unfold E1
  fun_prop

theorem conj_circleChar_mul (p q : ℤ) (t : ℝ) : (starRingEnd ℂ) (E1 p t) * E1 q t = E1 (q - p) t := by
  unfold E1
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem cexp_mul_I_pow_eq_circleChar (n : ℕ) (t : ℝ) : cexp ((t : ℂ) * I) ^ n = E1 n t := by
  rw [← Complex.exp_nat_mul]
  unfold E1
  congr 1
  push_cast
  ring

theorem integrable_circleChar (k : ℤ) : Integrable (E1 k) mu1 := by
  exact Integrable.mono' (integrable_const (1 : ℝ)) (continuous_circleChar k).aestronglyMeasurable
    (ae_of_all _ fun t => (norm_circleChar k t).le)

theorem integral_circleChar (k : ℤ) : ∫ t, E1 k t ∂mu1 = if k = 0 then 1 else 0 := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hc : ((ENNReal.ofReal (2 * Real.pi))⁻¹).toReal = (2 * Real.pi)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal h2pi.le]
  unfold mu1
  rw [integral_smul_measure, hc, ← intervalIntegral.integral_of_le h2pi.le]
  split_ifs with hk
  · subst hk
    simp only [E1, Int.cast_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
      intervalIntegral.integral_const, sub_zero]
    rw [smul_smul, inv_mul_cancel₀ h2pi.ne', one_smul]
  · have hkc : (k : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
    have hE : ∀ t : ℝ, E1 k t = Complex.exp ((k : ℂ) * Complex.I * t) := fun t => by
      unfold E1
      congr 1
      push_cast
      ring
    simp_rw [hE]
    rw [integral_exp_mul_complex hkc]
    have e2 : Complex.exp ((k : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show (k : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ) = k * (2 * Real.pi * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [e2]
    simp

end GrowthPolynomialOperator

section HilbertSchmidtNorm
open MeasureTheory Complex

variable {ι : Type} [Fintype ι]

def muT (ι : Type) [Fintype ι] : Measure (ι → ℝ) := Measure.pi fun _ => mu1

instance : IsProbabilityMeasure (muT ι) := by unfold muT; infer_instance

def chi (e : ι →₀ ℕ) (θ : ι → ℝ) : ℂ := ∏ g, E1 (e g) (θ g)

theorem chi_norm (e : ι →₀ ℕ) (θ : ι → ℝ) : ‖chi e θ‖ = 1 := by
  unfold chi
  rw [norm_prod]
  simp [norm_circleChar]

theorem chi_cont (e : ι →₀ ℕ) : Continuous (chi e) := by
  unfold chi
  exact continuous_finset_prod _ fun g _ => (continuous_circleChar _).comp (continuous_apply g)

theorem chi_conj_mul (e e' : ι →₀ ℕ) (θ : ι → ℝ) :
    (starRingEnd ℂ) (chi e θ) * chi e' θ = ∏ g, E1 ((e' g : ℤ) - (e g : ℤ)) (θ g) := by
  unfold chi
  rw [map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun g _ => conj_circleChar_mul _ _ _

theorem chi_orth (e e' : ι →₀ ℕ) :
    ∫ θ, (starRingEnd ℂ) (chi e θ) * chi e' θ ∂(muT ι) = if e' = e then 1 else 0 := by
  simp_rw [chi_conj_mul]
  unfold muT
  refine (integral_fintype_prod_eq_prod (μ := fun _ => mu1)
    (fun g t => E1 ((e' g : ℤ) - (e g : ℤ)) t)).trans ?_
  simp only [integral_circleChar]
  split_ifs with h
  · subst h
    simp
  · obtain ⟨g, hg⟩ : ∃ g, e' g ≠ e g := by
      by_contra hc
      push_neg at hc
      exact h (Finsupp.ext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ g) (by simp [sub_eq_zero, hg])

theorem chi_conj_mul_integrable (e e' : ι →₀ ℕ) :
    Integrable (fun θ => (starRingEnd ℂ) (chi e θ) * chi e' θ) (muT ι) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    ((Complex.continuous_conj.comp (chi_cont e)).mul (chi_cont e')).aestronglyMeasurable (ae_of_all _ fun θ => ?_)
  simp [chi_norm]

theorem fourier_coeff (b : (ι →₀ ℕ) → ℂ) (hb : Summable fun e => ‖b e‖) (e : ι →₀ ℕ) :
    ∫ θ, (starRingEnd ℂ) (chi e θ) * ∑' e', b e' * chi e' θ ∂(muT ι) = b e := by
  have hint : ∀ e', Integrable (fun θ => (starRingEnd ℂ) (chi e θ) * (b e' * chi e' θ)) (muT ι) := fun e' => by
    have := (chi_conj_mul_integrable e e').const_mul (b e')
    refine this.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp only; ring
  have hnorm : ∀ e', ∫ θ, ‖(starRingEnd ℂ) (chi e θ) * (b e' * chi e' θ)‖ ∂(muT ι) = ‖b e'‖ := fun e' => by
    simp only [norm_mul, RCLike.norm_conj, chi_norm, one_mul, mul_one]
    simp
  have h1 := hasSum_integral_of_summable_integral_norm hint (by simp only [hnorm]; exact hb)
  have hval : ∀ e', ∫ θ, (starRingEnd ℂ) (chi e θ) * (b e' * chi e' θ) ∂(muT ι) = if e' = e then b e else 0 := fun e' => by
    have : (fun θ => (starRingEnd ℂ) (chi e θ) * (b e' * chi e' θ)) =
        fun θ => b e' * ((starRingEnd ℂ) (chi e θ) * chi e' θ) := by funext θ; ring
    rw [this, integral_const_mul, chi_orth]
    split_ifs with h
    · subst h; simp
    · simp
  simp only [hval, tsum_mul_left] at h1
  exact h1.unique (hasSum_ite_eq e (b e))

end HilbertSchmidtNorm

section PB3
open MeasureTheory Complex

theorem re_conj_le (φ p : ℂ) : ((starRingEnd ℂ) p * (2 * φ - p)).re ≤ ‖φ‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  nlinarith [sq_nonneg (φ.re - p.re), sq_nonneg (φ.im - p.im)]

theorem polyBessel_holds : PolyBessel := by
  classical
  intro ι _ F c B z hF hB E
  obtain ⟨a, ha_def⟩ : ∃ a : (ι →₀ ℕ) → ℂ, ∀ e, a e = c e * e.prod fun g k => z g ^ k := ⟨_, fun _ => rfl⟩
  have ha : Summable fun e => ‖a e‖ := by
    simp only [ha_def]; exact (hF z).summable.norm
  obtain ⟨w, hw_def⟩ : ∃ w : (ι → ℝ) → ι → ℂ, ∀ θ g, w θ g = cexp ((θ g : ℂ) * I) * z g := ⟨_, fun _ _ => rfl⟩
  have hw : ∀ θ g, ‖w θ g‖ = ‖z g‖ := fun θ g => by
    rw [hw_def, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hterm : ∀ θ e, c e * (e.prod fun g k => w θ g ^ k) = a e * chi e θ := by
    intro θ e
    rw [ha_def, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      mul_assoc]
    unfold chi
    rw [← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [hw_def, mul_pow, cexp_mul_I_pow_eq_circleChar, mul_comm]
  have hΦ : ∀ θ, HasSum (fun e => a e * chi e θ) (F (w θ)) := fun θ => by
    simpa only [hterm] using hF (w θ)
  obtain ⟨b, hb_def⟩ : ∃ b : (ι →₀ ℕ) → ℂ, ∀ e, b e = 2 * a e - (if e ∈ E then a e else 0) := ⟨_, fun _ => rfl⟩
  have hbs : Summable fun e => ‖b e‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun e => ?_) (ha.mul_left 3)
    rw [hb_def]
    have h2 : ‖2 * a e‖ = 2 * ‖a e‖ := by rw [norm_mul]; simp
    split_ifs
    · have := norm_sub_le (2 * a e) (a e)
      linarith
    · rw [sub_zero, h2]
      have := norm_nonneg (a e)
      linarith
  obtain ⟨P, hP_def⟩ : ∃ P : (ι → ℝ) → ℂ, ∀ θ, P θ = ∑ e ∈ E, a e * chi e θ := ⟨_, fun _ => rfl⟩
  have hP : ∀ θ, HasSum (fun e => (if e ∈ E then a e else 0) * chi e θ) (P θ) := by
    intro θ
    have h : HasSum (fun e => (if e ∈ E then a e else 0) * chi e θ)
        (∑ e ∈ E, (if e ∈ E then a e else 0) * chi e θ) :=
      hasSum_sum_of_ne_finset_zero (fun e he => by simp [he])
    rw [hP_def]
    convert h using 1
    exact Finset.sum_congr rfl fun e he => by simp [he]
  have hΨ : ∀ θ, ∑' e, b e * chi e θ = 2 * F (w θ) - P θ := fun θ => by
    have h := ((hΦ θ).mul_left 2).sub (hP θ)
    have e1 : (fun e => 2 * (a e * chi e θ) - (if e ∈ E then a e else 0) * chi e θ) = fun e => b e * chi e θ := by
      funext e; rw [hb_def]; ring
    rw [e1] at h
    exact h.tsum_eq
  have hI : ∀ e, ∫ θ, (starRingEnd ℂ) (chi e θ) * (2 * F (w θ) - P θ) ∂(muT ι) = b e := fun e => by
    simpa only [hΨ] using fourier_coeff b hbs e
  have hcont : Continuous fun θ : ι → ℝ => ∑' e, b e * chi e θ :=
    continuous_tsum (fun e => continuous_const.mul (chi_cont e)) hbs
      (fun e θ => by rw [norm_mul, chi_norm, mul_one])
  have hInt : ∀ e, Integrable (fun θ => (starRingEnd ℂ) (chi e θ) * (2 * F (w θ) - P θ)) (muT ι) := fun e => by
    simp only [← hΨ]
    refine Integrable.of_bound ((Complex.continuous_conj.comp (chi_cont e)).mul hcont).aestronglyMeasurable
      (∑' e, ‖b e‖) (Filter.Eventually.of_forall fun θ => ?_)
    rw [norm_mul, RCLike.norm_conj, chi_norm, one_mul]
    have hs : (fun e => ‖b e * chi e θ‖) = fun e => ‖b e‖ := by funext e; rw [norm_mul, chi_norm, mul_one]
    refine le_trans (norm_tsum_le_tsum_norm (by rw [hs]; exact hbs)) (le_of_eq (by rw [hs]))
  have hG : ∀ θ, (starRingEnd ℂ) (P θ) * (2 * F (w θ) - P θ) =
      ∑ e ∈ E, (starRingEnd ℂ) (a e) * ((starRingEnd ℂ) (chi e θ) * (2 * F (w θ) - P θ)) := by
    intro θ
    have hgen : ∀ Ψ : ℂ, (starRingEnd ℂ) (P θ) * Ψ =
        ∑ e ∈ E, (starRingEnd ℂ) (a e) * ((starRingEnd ℂ) (chi e θ) * Ψ) := fun Ψ => by
      rw [hP_def θ, map_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun e _ => by rw [map_mul]; ring
    exact hgen _
  have hGint : Integrable (fun θ => (starRingEnd ℂ) (P θ) * (2 * F (w θ) - P θ)) (muT ι) := by
    simp only [hG]
    exact integrable_finsetSum _ fun e _ => (hInt e).const_mul _
  have hGval : ∫ θ, (starRingEnd ℂ) (P θ) * (2 * F (w θ) - P θ) ∂(muT ι) = ((∑ e ∈ E, ‖a e‖ ^ 2 : ℝ) : ℂ) := by
    simp only [hG]
    rw [integral_finsetSum _ (fun e _ => (hInt e).const_mul _)]
    push_cast
    refine Finset.sum_congr rfl fun e he => ?_
    rw [integral_const_mul, hI, hb_def, if_pos he, show 2 * a e - a e = a e by ring, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have hmono := integral_mono (Complex.reCLM.integrable_comp hGint) (integrable_const B)
    (fun θ => le_trans (re_conj_le (F (w θ)) (P θ)) (hB (w θ) (hw θ)))
  rw [Complex.reCLM.integral_comp_comm hGint, hGval] at hmono
  simp only [Complex.reCLM_apply, Complex.ofReal_re, integral_const, probReal_univ, one_smul] at hmono
  refine le_trans (le_of_eq ?_) hmono
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [ha_def, norm_mul, mul_pow, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), norm_prod, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [norm_pow, ← pow_mul, mul_comm]

theorem jetInt_holds (D : Formalism.BasicNotions.D7) : JetInt D := by
  exact jetInt_of (gaussBessel_of polyBessel_holds) D

end PB3

section Z1d
open Formalism.BasicNotions

theorem opNorm_estimate_of_sup_theta_mass (Cn Cd C1 : ℝ) : ∃ C : ℝ, ∀ (D : D7) (x Cth : ℝ),
    ThetaSupremumBound D → adm2 D Cn Cth x → Conclusion1 D Cn C1 x → Conclusion2 D Cn Cd C x := by
  obtain ⟨C, hC⟩ := slopeEstimate_of_lemmaB_slopeLine Cn Cd C1
  exact ⟨C, fun D x Cth hS h2 h1 => hC D x Cth hS (jetInt_holds D) h2 h1⟩

theorem familyOpNorm_of_sup {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hS : FamilySupremumBound Fm) (h2 : admF2 Fm) (h1 : ConclusionF1 Fm) : ConclusionF2 Fm := by
  exact familyOpNorm_of_sup_jet Fm hS (fun x i => jetInt_holds _) h2 h1

end Z1d

section UF
open Formalism.BasicNotions NumberField MeasureTheory

instance dz_inv (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) : (dz D i s).IsAddLeftInvariant := by
  unfold dz; infer_instance

instance dz_vadd (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (T : Torus D i s) :
    VAddInvariantMeasure T.La (Gx D i → ℂ) (dz D i s) :=
  ⟨fun c A _ => measure_preimage_add (dz D i s) (c : Gx D i → ℂ) A⟩

theorem Hq_cont (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) : Continuous (Hq D i s) := by unfold Hq; fun_prop

theorem dens_cont (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (Th : (Gx D i → ℂ) → ℂ) (h : Continuous Th) :
    Continuous (dens D i s Th) := by
  unfold dens
  have := Hq_cont D i s
  fun_prop

theorem dens_nonneg (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (Th : (Gx D i → ℂ) → ℂ) (z : Gx D i → ℂ) :
    0 ≤ dens D i s Th z := by unfold dens; positivity

theorem unfold_le (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (T : Torus D i s) (Th : (Gx D i → ℂ) → ℂ)
    (hA : T.Admis Th) (B : ℝ)
    (hB : ∀ u, Summable (fun y : T.La => Real.exp (-Real.pi * Hq D i s (u + (y : Gx D i → ℂ)))) ∧
      ∑' y : T.La, Real.exp (-Real.pi * Hq D i s (u + (y : Gx D i → ℂ))) ≤ B) (z : Gx D i → ℂ) :
    ∫⁻ w, ENNReal.ofReal (dens D i s Th (z + w) * Real.exp (-Real.pi * Hq D i s w)) ∂(dz D i s) ≤
      ENNReal.ofReal (B * T.l2Sq Th) := by
  have hcount : Countable T.La := by
    have h := (hB 0).1.countable_support
    have hs : Function.support (fun y : T.La => Real.exp (-Real.pi * Hq D i s (0 + (y : Gx D i → ℂ)))) = Set.univ :=
      Set.eq_univ_of_forall fun y => (Real.exp_pos _).ne'
    rw [hs] at h
    exact Set.countable_univ_iff.1 h
  have hdc := dens_cont D i s Th hA.1.continuous
  have hHc := Hq_cont D i s
  have hB0 : 0 ≤ B := le_trans (tsum_nonneg fun _ => (Real.exp_pos _).le) (hB 0).2
  obtain ⟨f, hf⟩ : ∃ f : (Gx D i → ℂ) → ENNReal, ∀ w,
      f w = ENNReal.ofReal (dens D i s Th w * Real.exp (-Real.pi * Hq D i s (w - z))) := ⟨_, fun _ => rfl⟩
  have e1 : (fun w => ENNReal.ofReal (dens D i s Th (z + w) * Real.exp (-Real.pi * Hq D i s w))) =
      fun w => f (z + w) := by
    funext w; rw [hf, add_sub_cancel_left]
  rw [e1, lintegral_add_left_eq_self f z, T.fund.lintegral_eq_tsum'' f]
  have e2 : ∀ (y : T.La) (x : Gx D i → ℂ), f (y +ᵥ x) =
      ENNReal.ofReal (dens D i s Th x) * ENNReal.ofReal (Real.exp (-Real.pi * Hq D i s ((x - z) + (y : Gx D i → ℂ)))) := by
    intro y x
    rw [hf, AddSubgroup.vadd_def, vadd_eq_add, add_comm (y : Gx D i → ℂ) x, hA.2.1 y y.2 x,
      ENNReal.ofReal_mul (dens_nonneg D i s Th x)]
    congr 3
    abel_nf
  simp only [e2]
  rw [← lintegral_tsum (fun y => by
    refine (Measurable.aemeasurable ?_)
    fun_prop)]
  have e3 : ∀ x, ∑' y : T.La, ENNReal.ofReal (dens D i s Th x) *
      ENNReal.ofReal (Real.exp (-Real.pi * Hq D i s ((x - z) + (y : Gx D i → ℂ)))) ≤
      ENNReal.ofReal B * ENNReal.ofReal (dens D i s Th x) := by
    intro x
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) (hB (x - z)).1, mul_comm]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hB (x - z)).2) _
  refine le_trans (lintegral_mono e3) ?_
  rw [lintegral_const_mul _ (by fun_prop), ENNReal.ofReal_mul hB0]
  refine le_of_eq ?_
  congr 1
  unfold Torus.l2Sq
  exact (ofReal_integral_eq_lintegral_ofReal hA.2.2 (Filter.Eventually.of_forall fun x => dens_nonneg D i s Th x)).symm

end UF

section MV1
open Formalism.BasicNotions NumberField MeasureTheory Complex

theorem integrable_of_continuous_circleMeasure {E : Type} [NormedAddCommGroup E] (f : ℝ → E) (hf : Continuous f) : Integrable f mu1 := by
  unfold mu1
  refine Integrable.smul_measure ?_ ?_
  · exact hf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  · rw [ENNReal.inv_ne_top]
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

theorem mean1 (g : ℂ → ℂ) (hg : Differentiable ℂ g) : ∫ θ : ℝ, g (cexp ((θ : ℂ) * I)) ∂mu1 = g 0 := by
  have h := DiffContOnCl.circleAverage (f := g) (c := 0) (R := 1) hg.diffContOnCl
  rw [Real.circleAverage_def] at h
  unfold mu1
  rw [integral_smul_measure, ← intervalIntegral.integral_of_le (by positivity), ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity)]
  rw [← h]
  congr 2
  funext θ
  simp [circleMap]

theorem normSq_at_zero_le_circle_mean (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    ENNReal.ofReal (‖g 0‖ ^ 2) ≤ ∫⁻ θ : ℝ, ENNReal.ofReal (‖g (cexp ((θ : ℂ) * I))‖ ^ 2) ∂mu1 := by
  have hc : Continuous fun θ : ℝ => g (cexp ((θ : ℂ) * I)) := hg.continuous.comp (by fun_prop)
  have hi := integrable_of_continuous_circleMeasure _ hc
  have hi2 : Integrable (fun θ : ℝ => ‖g (cexp ((θ : ℂ) * I))‖ ^ 2) mu1 := integrable_of_continuous_circleMeasure _ (hc.norm.pow 2)
  have hG : Integrable (fun θ : ℝ => (starRingEnd ℂ) (g 0) * (2 * g (cexp ((θ : ℂ) * I)) - g 0)) mu1 :=
    integrable_of_continuous_circleMeasure _ (continuous_const.mul ((continuous_const.mul hc).sub continuous_const))
  have hval : ∫ θ : ℝ, (starRingEnd ℂ) (g 0) * (2 * g (cexp ((θ : ℂ) * I)) - g 0) ∂mu1 = ((‖g 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [integral_const_mul, integral_sub (hi.const_mul 2) (integrable_const _), integral_const_mul, mean1 g hg,
      integral_const]
    simp only [probReal_univ, one_smul]
    rw [show 2 * g 0 - g 0 = g 0 by ring, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hmono := integral_mono (Complex.reCLM.integrable_comp hG) hi2
    (fun θ => re_conj_le (g (cexp ((θ : ℂ) * I))) (g 0))
  rw [Complex.reCLM.integral_comp_comm hG, hval] at hmono
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hmono
  rw [← ofReal_integral_eq_lintegral_ofReal hi2 (Filter.Eventually.of_forall fun θ => by positivity)]
  exact ENNReal.ofReal_le_ofReal hmono

theorem rot_mp (ι : Type) [Fintype ι] (θ : ℝ) :
    MeasurePreserving (fun (w : ι → ℂ) g => cexp ((θ : ℂ) * I) * w g) volume volume := by
  have h := volume_preserving_pi (ι := ι) (α' := fun _ => ℂ) (β' := fun _ => ℂ)
    (f := fun _ => (rotation (Circle.exp θ) : ℂ → ℂ)) (fun _ => (rotation (Circle.exp θ)).measurePreserving)
  simpa [rotation_apply, Circle.coe_exp] using h

end MV1

section MV2
open Formalism.BasicNotions NumberField MeasureTheory Complex

def rho (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (w : Gx D i → ℂ) : ℝ :=
  2 ^ Fintype.card (Gx D i) * Real.exp (-(2 * Real.pi) * Hq D i s w)

theorem rho_cont (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) : Continuous (rho D i s) := by
  unfold rho
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (Hq_cont D i s)))

theorem rho_nonneg (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (w : Gx D i → ℂ) : 0 ≤ rho D i s w := by
  unfold rho
  positivity

theorem rho_rot (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (θ : ℝ) (w : Gx D i → ℂ) :
    rho D i s (fun g => cexp ((θ : ℂ) * I) * w g) = rho D i s w := by
  unfold rho Hq
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

instance dz_sfinite (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) : SFinite (dz D i s) := by
  unfold dz; infer_instance

theorem gauss_mass (ι : Type) [Fintype ι] (a : ι → ℝ) (ha : ∀ g, 0 < a g) :
    Integrable (fun w : ι → ℂ => ∏ g, Real.exp (-(a g * ‖w g‖ ^ 2))) volume ∧
    ∫ w : ι → ℂ, ∏ g, Real.exp (-(a g * ‖w g‖ ^ 2)) = ∏ g, ((a g)⁻¹ * Real.pi) := by
  refine ⟨Integrable.fintype_prod (f := fun g (x : ℂ) => Real.exp (-(a g * ‖x‖ ^ 2))) fun g => (gauss0 _ (ha g)).1, ?_⟩
  rw [integral_fintype_prod_volume_eq_prod (fun g (x : ℂ) => Real.exp (-(a g * ‖x‖ ^ 2)))]
  simp only [(gauss0 _ (ha _)).2]

theorem rho_mass (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) :
    ∫⁻ w, ENNReal.ofReal (rho D i s w) ∂(dz D i s) = 1 := by
  have hom : ∀ g : Gx D i, 0 < D.gx.Om g.1 s := fun g => D.gx.Om_pos g.1 s
  have ha : ∀ g : Gx D i, 0 < 2 / D.gx.Om g.1 s := fun g => div_pos two_pos (hom g)
  have e : (rho D i s) = fun w => 2 ^ Fintype.card (Gx D i) *
      ∏ g, Real.exp (-((2 / D.gx.Om g.1 s) * ‖w g‖ ^ 2)) := by
    funext w
    unfold rho Hq
    rw [← Real.exp_sum, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun g _ => ?_
    have := hom g
    have := Real.pi_pos
    field_simp
  have hint : Integrable (rho D i s) volume := by
    rw [e]
    exact (gauss_mass (Gx D i) _ ha).1.const_mul _
  have hval : ∫ w, rho D i s w = 2 ^ Fintype.card (Gx D i) * ∏ g : Gx D i, ((2 / D.gx.Om g.1 s)⁻¹ * Real.pi) := by
    rw [e, integral_const_mul, (gauss_mass (Gx D i) _ ha).2]
  unfold dz
  rw [lintegral_smul_measure, ← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun w => rho_nonneg D i s w), hval, smul_eq_mul,
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun g _ => by have := hom g; positivity)]
  rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    Finset.prod_eq_one, ENNReal.ofReal_one]
  intro g _
  have := hom g
  have := Real.pi_pos
  field_simp

theorem gauss_mv (D : D7) (i : ℕ) (s : D.what₂.LL →+* ℂ) (F : (Gx D i → ℂ) → ℂ) (hF : Differentiable ℂ F) :
    ENNReal.ofReal (‖F 0‖ ^ 2) ≤
      ∫⁻ w, ENNReal.ofReal (‖F w‖ ^ 2) * ENNReal.ofReal (rho D i s w) ∂(dz D i s) := by
  have hFc := hF.continuous
  have hρc := rho_cont D i s
  have hρm : Measurable fun w => ENNReal.ofReal (rho D i s w) := hρc.measurable.ennreal_ofReal
  have hhm : Measurable fun w => ENNReal.ofReal (‖F w‖ ^ 2) * ENNReal.ofReal (rho D i s w) :=
    ((hFc.norm.pow 2).measurable.ennreal_ofReal).mul hρm
  have hRc : Continuous fun p : (Gx D i → ℂ) × ℝ => F (fun g => cexp ((p.2 : ℂ) * I) * p.1 g) :=
    hFc.comp (continuous_pi fun g => by fun_prop)
  calc ENNReal.ofReal (‖F 0‖ ^ 2)
      = ∫⁻ w, ENNReal.ofReal (‖F 0‖ ^ 2) * ENNReal.ofReal (rho D i s w) ∂(dz D i s) := by
        rw [lintegral_const_mul _ hρm, rho_mass, mul_one]
    _ ≤ ∫⁻ w, (∫⁻ θ : ℝ, ENNReal.ofReal (‖F (fun g => cexp ((θ : ℂ) * I) * w g)‖ ^ 2) ∂mu1) *
          ENNReal.ofReal (rho D i s w) ∂(dz D i s) := by
        refine lintegral_mono fun w => mul_le_mul_left ?_ _
        have h := normSq_at_zero_le_circle_mean (fun t => F (fun g => t * w g)) (hF.comp (differentiable_pi.2 fun g => by fun_prop))
        have h0 : (fun g => (0 : ℂ) * w g) = (0 : Gx D i → ℂ) := by funext g; simp
        simp only [h0] at h
        exact h
    _ = ∫⁻ w, ∫⁻ θ : ℝ, ENNReal.ofReal (‖F (fun g => cexp ((θ : ℂ) * I) * w g)‖ ^ 2) *
          ENNReal.ofReal (rho D i s w) ∂mu1 ∂(dz D i s) := by
        refine lintegral_congr fun w => ?_
        rw [lintegral_mul_const]
        exact (((hRc.comp (Continuous.prodMk_right w)).norm.pow 2).measurable.ennreal_ofReal)
    _ = ∫⁻ θ : ℝ, ∫⁻ w, ENNReal.ofReal (‖F (fun g => cexp ((θ : ℂ) * I) * w g)‖ ^ 2) *
          ENNReal.ofReal (rho D i s w) ∂(dz D i s) ∂mu1 := by
        refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
        exact ((hRc.norm.pow 2).measurable.ennreal_ofReal).mul (hρm.comp measurable_fst)
    _ = ∫⁻ _θ : ℝ, ∫⁻ w, ENNReal.ofReal (‖F w‖ ^ 2) * ENNReal.ofReal (rho D i s w) ∂(dz D i s) ∂mu1 := by
        refine lintegral_congr fun θ => ?_
        have e : (fun w : Gx D i → ℂ => ENNReal.ofReal (‖F (fun g => cexp ((θ : ℂ) * I) * w g)‖ ^ 2) *
            ENNReal.ofReal (rho D i s w)) =
            fun w => (fun w' => ENNReal.ofReal (‖F w'‖ ^ 2) * ENNReal.ofReal (rho D i s w'))
              (fun g => cexp ((θ : ℂ) * I) * w g) := by
          funext w; simp only [rho_rot]
        rw [e]
        unfold dz
        rw [lintegral_smul_measure, lintegral_smul_measure, (rot_mp (Gx D i) θ).lintegral_comp hhm]
    _ = ∫⁻ w, ENNReal.ofReal (‖F w‖ ^ 2) * ENNReal.ofReal (rho D i s w) ∂(dz D i s) := by
        rw [lintegral_const, measure_univ, mul_one]

theorem supUnfold_holds (D : D7) : SupUnfold D := by
  intro i s T Th hA B hB z
  have hB0 : 0 ≤ B := le_trans (tsum_nonneg fun _ => (Real.exp_pos _).le) (hB 0).2
  have hl0 : 0 ≤ T.l2Sq Th := by
    unfold Torus.l2Sq
    exact integral_nonneg fun x => dens_nonneg D i s Th x
  have hFd : Differentiable ℂ (trans D i s (-z) Th) := by
    unfold trans Hherm
    have h1 : Differentiable ℂ fun w : Gx D i → ℂ => Th (w - -z) := hA.1.comp (by fun_prop)
    refine h1.mul (Differentiable.cexp ?_)
    fun_prop
  have h1 := gauss_mv D i s _ hFd
  have e0 : ‖trans D i s (-z) Th 0‖ ^ 2 = dens D i s Th z := by
    have h := dens_trans D i s (-z) Th 0
    unfold dens at h ⊢
    have hH0 : Hq D i s 0 = 0 := by unfold Hq; simp
    rw [hH0, mul_zero, Real.exp_zero, mul_one, zero_sub, neg_neg] at h
    exact h
  have e1 : ∀ w, ENNReal.ofReal (‖trans D i s (-z) Th w‖ ^ 2) * ENNReal.ofReal (rho D i s w) =
      ENNReal.ofReal (2 ^ gDim D i) *
        ENNReal.ofReal (dens D i s Th (z + w) * Real.exp (-Real.pi * Hq D i s w)) := by
    intro w
    have h := dens_trans D i s (-z) Th w
    rw [sub_neg_eq_add, add_comm w z] at h
    rw [← h, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold dens rho
    rw [b_card_Gx, show -(2 * Real.pi) * Hq D i s w = -Real.pi * Hq D i s w + -Real.pi * Hq D i s w by ring,
      Real.exp_add]
    ring
  simp only [e0, e1] at h1
  rw [lintegral_const_mul _ (by
    have := dens_cont D i s Th hA.1.continuous
    have := Hq_cont D i s
    exact (Continuous.measurable (by fun_prop)).ennreal_ofReal)] at h1
  have h2 := le_trans h1 (mul_le_mul_right (unfold_le D i s T Th hA B hB z) _)
  rw [← ENNReal.ofReal_mul (by positivity)] at h2
  have h3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
  linarith [h3]

theorem supBound_holds (D : D7) : ThetaSupremumBound D := by
  exact supBound_of_unfold D (supUnfold_holds D)

end MV2

section crystallineCocycles
open Formalism.BasicNotions

theorem familySupBound_holds {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilySupremumBound Fm := by
  intro x i
  exact supBound_holds _

theorem opNorm_estimate_of_theta_mass (Cn Cd C1 : ℝ) : ∃ C : ℝ, ∀ (D : D7) (x Cth : ℝ),
    adm2 D Cn Cth x → Conclusion1 D Cn C1 x → Conclusion2 D Cn Cd C x := by
  obtain ⟨C, hC⟩ := opNorm_estimate_of_sup_theta_mass Cn Cd C1
  exact ⟨C, fun D x Cth h2 h1 => hC D x Cth (supBound_holds D) h2 h1⟩

theorem familyOpNorm_of_theta_mass {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h2 : admF2 Fm) (h1 : ConclusionF1 Fm) : ConclusionF2 Fm := by
  exact familyOpNorm_of_sup Fm (familySupBound_holds Fm) h2 h1

end crystallineCocycles

section PJ
open Formalism.BasicNotions NumberField

def Open (D : D7) (C₀ C5 : ℝ) : Prop :=
  MsCount D C₀ ∧ PointsLemma D ∧ SlopeLowerOpenPart D ∧ SlopeMaxOpenPart D C5

theorem stmt_of_open (C₀ C5 : ℝ) (h2 : 2 ≤ C₀) (Cn Cd Cper Cth : ℝ) : ∃ C1 C2 C4 C5' C6 : ℝ, ∀ (D : D7) (x : ℝ),
    max Cn 1 ≤ x → Open D C₀ C5 → Stmt D Cn Cd Cper Cth C1 C2 C4 C5' C6 x := by
  obtain ⟨C1, h1⟩ := baseChange_preserves_unitary_of C₀ h2 Cn
  obtain ⟨C2, hZ1⟩ := opNorm_estimate_of_theta_mass Cn Cd C1
  obtain ⟨CP, hP⟩ := exists_projection_estimate Cn
  obtain ⟨C4, h4⟩ := heckeValue_estimate_of_record_value Cn Cd Cper Cth C2 CP
  obtain ⟨C5', h5⟩ := ramifiedLattice_of_chain_estimates Cn
  obtain ⟨C6, h6⟩ := classMap_estimate_of_partial Cn C5
  refine ⟨C1, C2, C4, C5', C6, fun D x hx ⟨oM, o3, oa, ob⟩ ⟨a1, a2, _, _, a6, _⟩ => ?_⟩
  have p1 := h1 D x oM
  have p2 := hZ1 D x Cth a2 p1
  exact ⟨p1, p2, o3, h4 D x a1 a2 p2 (hP D x a6), h5 D x hx oa, h6 D x hx ob, supBound_holds D, propZ_second_holds⟩

theorem propZ_first_of_mass (Cn Cd Cper Cth C1 : ℝ) : ∃ C : ℝ, ∀ (D : D7) (x : ℝ), adm1 D Cn Cper x → adm2 D Cn Cth x → adm6 D →
    Conclusion1 D Cn C1 x → Conclusion4 D Cn Cd C x := by
  obtain ⟨C2, hZ1⟩ := opNorm_estimate_of_theta_mass Cn Cd C1
  obtain ⟨CP, hP⟩ := exists_projection_estimate Cn
  obtain ⟨C4, h4⟩ := heckeValue_estimate_of_record_value Cn Cd Cper Cth C2 CP
  exact ⟨C4, fun D x a1 a2 a6 p1 => h4 D x a1 a2 (hZ1 D x Cth a2 p1) (hP D x a6)⟩

def OpenF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C₀ C5 : ℝ) : Prop :=
  MsCountF Fm C₀ ∧ ConclusionF3 Fm ∧ FamilySlopeLowerOpenPart Fm ∧ FamilySlopeMaxOpenPart Fm C5

theorem stmtF_of_open {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C₀ C5 : ℝ) (h2 : 2 ≤ C₀) (hO : OpenF Fm C₀ C5) : KudlaFamilyStatement Fm := by
  obtain ⟨oM, o3, oa, ob⟩ := hO
  intro ⟨a1, a2, _, _, a6, _⟩
  have p1 := familyMass_of_massCount Fm C₀ h2 oM
  have p2 := familyOpNorm_of_theta_mass Fm a2 p1
  exact ⟨p1, p2, o3, familyPropZ_first_of_admissible Fm a1 a2 p2 (stmtFP_holds Fm a6), familySlopeLower_of_open Fm oa, familySlopeMax_of_open Fm C5 ob, familySupBound_holds Fm,
    propZ_second_holds⟩

end PJ

end Formalism.MainNotions.flipTwoThree
