import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

noncomputable section

namespace GlobalTheory.Diag.PG

open Formalism.BasicNotions

def bx (x eps : ℝ) : ℝ := Real.exp (x ^ eps)

def aC (x eps : ℝ) : ℝ := x ^ ((11 : ℝ) / 2) * bx x eps

def bpC (x eps : ℝ) : ℝ := aC x eps / Real.exp (x ^ (eps / 3))

variable (D : D7)

def Top (τ : D.what₂.Tau) : Prop :=
  ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t

def uFirst (τ : D.what₂.Tau) : ℝ := (((D.hc τ).u ⟨0, by have := D.R.m_add_three_le_k; omega⟩ : ℚ) : ℝ)

def uLast (τ : D.what₂.Tau) : ℝ := (((D.hc τ).u ⟨D.R.k - 1, by have := D.R.m_add_three_le_k; omega⟩ : ℚ) : ℝ)

def vFirst (τ : D.what₂.Tau) : ℝ := (((D.hc τ).v ⟨0, by have := D.R.m_add_three_le_k; omega⟩ : ℚ) : ℝ)

def vLast (τ : D.what₂.Tau) : ℝ := (((D.hc τ).v ⟨D.R.k - 2, by have := D.R.m_add_three_le_k; omega⟩ : ℚ) : ℝ)

def bFirst (τ : D.what₂.Tau) : ℝ := (((D.hc τ).b ⟨0, by have := D.R.two_le_m; omega⟩ : ℚ) : ℝ)

def bLast (τ : D.what₂.Tau) : ℝ := (((D.hc τ).b ⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩ : ℚ) : ℝ)

structure RankNums (x eps CD m f k lrd Del : ℝ) : Prop where
  m_lo : x ^ ((1 : ℝ) / 4) ≤ m
  mf : m ^ 4 ≤ f
  fk : f ≤ k
  k_lo : x ^ (eps / 2) * (m ^ 5 * f * x ^ eps) ≤ k
  k_hi : k ≤ x ^ (5 : ℝ)
  lrd_lo : Real.log 2 ≤ lrd
  lrd_hi : lrd ≤ x ^ (eps / 2)
  Del_lo : (k * f * x ^ eps) ^ CD ≤ Del
  Del_hi : Real.log Del ≤ x ^ (eps / 2)

structure Glob (x eps CD Cg CT : ℝ) : Prop where
  nums : RankNums x eps CD D.R.m D.R.f D.R.k (Real.log D.host.rdE) (D.s.Del : ℝ)
  rd_lo : 2 ≤ D.host.rdE
  g_win : ∀ i, ((D.R.k : ℝ) * bx x eps) ^ 8 ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ bx x eps ^ Cg
  T_win : ∀ u, bx x eps ^ ((1 / 2 : ℝ) * (D.R.m : ℝ)) ≤ ((D.mem u).A.T : ℝ) ∧
    ((D.mem u).A.T : ℝ) ≤ bx x eps ^ (CT * (D.R.m : ℝ))
  gap : ∀ τ (j : ℕ) (h : j + 1 < D.R.m), x ^ (eps / 100) * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * x ^ eps ≤
    (((D.hc τ).b ⟨j + 1, h⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ)
  cloud : ∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧
    (((D.hc τ).v i : ℚ) : ℝ) ≤ 4 * (D.R.k : ℝ) * (D.s.Del : ℝ)
  off : ∀ τ, ¬ Top D τ → 4 * (D.R.k : ℝ) * (D.s.Del : ℝ) ≤ uFirst D τ - vFirst D τ ∧
    uFirst D τ - vFirst D τ ≤ 8 * (D.R.k : ℝ) * (D.s.Del : ℝ) ∧ uLast D τ = vLast D τ - 1 / 2

structure Nodes (x eps : ℝ) : Prop where
  b_win : ∀ τ j, Real.sqrt (bx x eps) ≤ (((D.hc τ).b j : ℚ) : ℝ) ∧ (((D.hc τ).b j : ℚ) : ℝ) ≤ bx x eps ^ 2
  bm : ∀ τ, bLast D τ ≤ 2 * bFirst D τ
  top : ∀ τ, Top D τ → Real.sqrt (bx x eps) ≤ uFirst D τ ∧ uFirst D τ ≤ bx x eps ^ 2 ∧
    3 ≤ bFirst D τ + uLast D τ ∧ bFirst D τ / 2 ≤ -uLast D τ

structure OneScale (x eps eta : ℝ) : Prop where
  eta_pos : 0 < eta
  eta_hi : Real.log eta ≤ x ^ (eps / 4)
  top : ∀ τ, Top D τ → uFirst D τ = (⌈aC x eps⌉ : ℝ) + ((D.R.k : ℝ) - 1) / 2 ∧
    uLast D τ = -(⌈bpC x eps⌉ : ℝ) - ((D.R.k : ℝ) - 1) / 2 ∧
    bFirst D τ = (⌈bpC x eps⌉ : ℝ) + (⌊bpC x eps / x⌋ : ℝ) ∧
    ∀ j, (((D.hc τ).e j : ℚ) : ℝ) ≤ (⌈bpC x eps⌉ : ℝ) + bpC x eps / x + eta
  off : ∀ τ, ¬ Top D τ → ∀ j, bx x eps ≤ (((D.hc τ).b j : ℚ) : ℝ) ∧ (((D.hc τ).e j : ℚ) : ℝ) ≤ bx x eps + eta + 1

def SplitLab {R : Ranks} (H : Host R) (x eps : ℝ) : Prop :=
  (∃ J : ℝ, 1 ≤ J ∧ ⌊x ^ (eps / J / 5)⌋₊ ≤ H.splitBound) ∧ (R.o : ℝ) ≤ x ^ (eps / 100) ∧
    (H.QS : ℝ) ≤ 4 * R.n * x ^ (eps / 100)

theorem SplitLab.of_one {R : Ranks} {H : Host R} {x eps : ℝ} (h : ⌊x ^ (eps / 5)⌋₊ ≤ H.splitBound)
    (ho : (R.o : ℝ) ≤ x ^ (eps / 100)) (hQ : (H.QS : ℝ) ≤ 4 * R.n * x ^ (eps / 100)) : SplitLab H x eps :=
  ⟨⟨1, le_rfl, by rwa [div_one]⟩, ho, hQ⟩

structure Labels (x eps CG : ℝ) : Prop where
  secondLabelsNonempty : D.host.T2.Nonempty
  j0 : ∃ j0 : ℕ, Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m) ≤ j0 ∧ 10 * j0 + 20 ≤ D.host.Lw
  split : SplitLab D.host x eps
  CG_pos : 0 < CG
  Gam : ∀ u, Real.log (D.mem u).A.GamP = CG * (D.R.m : ℝ) ^ 5 * D.R.f * x ^ eps

def DelInt : Prop := ∃ n : ℕ, D.s.Del = n

structure LiveLabels (x eps CG : ℝ) : Prop where
  split : SplitLab D.host x eps
  CG_pos : 0 < CG
  Gam : ∀ u, Real.log (D.mem u).A.GamP = CG * (D.R.m : ℝ) ^ 5 * D.R.f * x ^ eps

structure DeadLabels {R : Ranks} (H : Host R) : Prop where
  secondLabelsNonempty : H.T2.Nonempty
  j0 : ∃ j0 : ℕ, Real.logb 5 ((R.n : ℝ) * R.N R.m / R.m) ≤ j0 ∧ 10 * j0 + 20 ≤ H.Lw

theorem labels_iff (x eps CG : ℝ) : Labels D x eps CG ↔ DeadLabels D.host ∧ LiveLabels D x eps CG :=
  ⟨fun h => ⟨⟨h.secondLabelsNonempty, h.j0⟩, h.split, h.CG_pos, h.Gam⟩, fun h => ⟨h.1.secondLabelsNonempty, h.1.j0, h.2.split, h.2.CG_pos, h.2.Gam⟩⟩

def relabel {R : Ranks} (H : Host R) (Lw : ℕ) (h : 2 ≤ Lw) : Host R :=
  { H with
    T2 := {0}
    Lw := Lw
    two_le_Lw := h
    second_set_range := fun s hs => by rw [Finset.mem_singleton.1 hs, mul_zero]; exact R.n0_pos
    second_set_no_relation := fun s₁ h₁ s₂ h₂ _ _ h12 =>
      absurd ((Finset.mem_singleton.1 h₁).trans (Finset.mem_singleton.1 h₂).symm) h12 }

theorem exists_deadLabels {R : Ranks} (H : Host R) : ∃ (Lw : ℕ) (h : 2 ≤ Lw), DeadLabels (relabel H Lw h) :=
  ⟨10 * ⌈Real.logb 5 ((R.n : ℝ) * R.N R.m / R.m)⌉₊ + 20, by omega,
    ⟨0, Finset.mem_singleton_self _⟩, _, Nat.le_ceil _, le_rfl⟩

def RefUntwisted : Prop :=
  ∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → D.what₂.Aj j w = 0

structure TopsCoset {R : Ranks} (H : Host R) (J : ℕ) : Prop where
  lo : R.m < 2 * 2 ^ J
  hi : 2 ^ J ≤ R.m
  coset : ∃ c : R.A, ∀ t, t ∈ H.TT ↔ ∃ s : R.A, R.h t = R.h (c + 2 ^ J • s)

theorem TopsCoset.succ_le {R : Ranks} {H : Host R} {J : ℕ} (h : TopsCoset H J) (hm : 2 * R.m ≤ 2 ^ R.e) : J + 1 ≤ R.e := by
  have h1 : 2 ^ (J + 1) ≤ 2 ^ R.e := by
    have := h.hi
    rw [pow_succ]; omega
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1

theorem TopsCoset.card_mul {R : Ranks} {H : Host R} {J : ℕ} (h : TopsCoset H J) (hJ : J ≤ R.e) :
    H.TT.card * 2 ^ J = R.n := by
  classical
  obtain ⟨c, hc⟩ := h.coset
  haveI : IsCyclic (Formalism.FrobeniusOrbits.HGrp R.e) := (Formalism.FrobeniusOrbits.hostGroup R.e).2.2.2.2.2.1
  have hcard : Nat.card (Additive (Formalism.FrobeniusOrbits.HGrp R.e)) = 2 ^ R.e :=
    (Nat.card_congr Additive.toMul).trans (Formalism.FrobeniusOrbits.Group.card_H R.e)
  haveI : Finite (Additive (Formalism.FrobeniusOrbits.HGrp R.e)) := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  set K : AddSubgroup R.A := (nsmulAddMonoidHom (α := Additive (Formalism.FrobeniusOrbits.HGrp R.e)) (2 ^ J)).range.comap R.h with hK
  have hi : K.index = 2 ^ J := by
    rw [hK, AddSubgroup.index_comap_of_surjective _ R.h_surj, IsAddCyclic.index_nsmulAddMonoidHom_range, hcard]
    exact Nat.gcd_eq_right (pow_dvd_pow 2 hJ)
  have hm : ∀ t, t ∈ H.TT ↔ t - c ∈ K := fun t => by
    rw [hc, hK, AddSubgroup.mem_comap, AddMonoidHom.mem_range]
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨R.h s, by rw [map_sub, hs, map_add, map_nsmul, add_sub_cancel_left]; rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨s, rfl⟩ := R.h_surj y
      refine ⟨s, ?_⟩
      rw [map_add, map_nsmul, ← sub_eq_iff_eq_add', ← map_sub, ← hy]; rfl
  have e : Nat.card K = H.TT.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr ((Equiv.addRight c).subtypeEquiv fun t => by simp [hm])
  rw [← e, ← hi, AddSubgroup.card_mul_index, R.natCard_A]; rfl

theorem TopsCoset.card_eq {R : Ranks} {H : Host R} {J : ℕ} (h : TopsCoset H J) (hJ : J ≤ R.e) :
    H.TT.card = R.n / 2 ^ J := by
  rw [← h.card_mul hJ, Nat.mul_div_cancel _ (by positivity)]

theorem TopsCoset.card_even {R : Ranks} {H : Host R} {J : ℕ} (h : TopsCoset H J) (hm : 2 * R.m ≤ 2 ^ R.e) :
    Even H.TT.card := by
  have h1 := h.succ_le hm
  have h2 : 2 ^ (J + 1) ∣ H.TT.card * 2 ^ J := by
    rw [h.card_mul (by omega)]; exact (pow_dvd_pow 2 h1).trans R.two_pow_dvd_ord
  rw [pow_succ'] at h2
  exact even_iff_two_dvd.2 (Nat.dvd_of_mul_dvd_mul_right (by positivity) h2)

theorem two_m_le_two_pow {R : Ranks} (H : Host R) (h : (R.m : ℝ) ^ 4 ≤ R.f) : 2 * R.m ≤ 2 ^ R.e := by
  have h1 : R.m ^ 4 ≤ 2 * R.ord := by exact_mod_cast h
  have h2 := R.ord_le_o_mul_two_pow
  have h3 : R.o ^ 2 ≤ 2 ^ R.e := (Nat.pow_le_pow_right R.o_pos (by norm_num)).trans H.o_pow
  have h4 : 2 ^ 2 ≤ 2 ^ R.e := Nat.pow_le_pow_right (by norm_num) H.two_le_e
  generalize 2 ^ R.e = P at *
  generalize R.o = o at *
  by_contra hc
  have h5 : P ^ 4 < (2 * R.m) ^ 4 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h6 : P ^ 3 * P < 32 * o * P := by nlinarith
  have h7 : P ^ 3 < 32 * o := Nat.lt_of_mul_lt_mul_right h6
  have h8 : (P ^ 3) ^ 2 < (32 * o) ^ 2 := Nat.pow_lt_pow_left h7 (by norm_num)
  have h9 : (2 ^ 2) ^ 5 ≤ P ^ 5 := Nat.pow_le_pow_left h4 5
  have h10 : 1024 * P ≤ P ^ 5 * P := Nat.mul_le_mul_right _ (by simpa using h9)
  nlinarith

open Classical in

def withTops {R : Ranks} (H : Host R) (J : ℕ) (c : R.A) : Host R :=
  { H with TT := Finset.univ.filter (fun t => ∃ s : R.A, R.h t = R.h (c + 2 ^ J • s)) }

theorem topsCoset_withTops {R : Ranks} (H : Host R) (c : R.A) :
    TopsCoset (withTops H (Nat.log 2 R.m) c) (Nat.log 2 R.m) where
  lo := by rw [← pow_succ']; exact Nat.lt_pow_succ_log_self (by norm_num) _
  hi := Nat.pow_log_le_self 2 (by have := R.two_le_m; omega)
  coset := ⟨c, fun t => by simp only [withTops, Finset.mem_filter, Finset.mem_univ, true_and]⟩

def EvenCentres : Prop := ∀ j, ∃ z : ℤ, ∑ τ, (D.hc τ).e j = 2 * z

structure ThreshNums (x eps f k N S eta v d : ℝ) : Prop where
  one_lt : 1 < x
  a_le : aC x eps ≤ bx x eps ^ 2
  av_le : aC x eps * v ≤ bx x eps ^ 2
  mul_mul_rpow_le_exp : k * N * x ^ ((11 : ℝ) / 2) ≤ Real.exp (x ^ (eps / 3))
  SY : (S + eta + f * N ^ 2) ^ 2 * (x ^ ((11 : ℝ) / 2)) ^ 3 ≤ bx x eps
  dY : 2 * x ^ ((11 : ℝ) / 2) < d
  NS : (N + 4 * S + 1) * x * Real.exp (x ^ (eps / 3)) ≤ bx x eps

def Thresholds (x eps eta : ℝ) : Prop :=
  ThreshNums x eps D.R.f D.R.k (D.R.N D.R.m) (4 * (D.R.k : ℝ) * (D.s.Del : ℝ)) eta D.host.v D.host.d

structure OneScaleDatum (x eps eta : ℝ) (J : ℕ) : Prop where
  sizes : OneScale D x eps eta
  tops : TopsCoset D.host J
  even : EvenCentres D
  thresh : Thresholds D x eps eta
  del : DelInt D

example : aC 4 0 = 2048 * Real.exp 1 := by
  unfold aC bx
  rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num), Real.rpow_zero]
  norm_num

example : bpC 1 1 = 1 := by simp [bpC, aC, bx]

end GlobalTheory.Diag.PG

end
