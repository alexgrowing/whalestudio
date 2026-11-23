import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership
import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty

noncomputable section

namespace GlobalTheory.Diag.PG.Wit

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField

def hcMk (R : Ranks) (Del h : ℕ) (U W : ℚ) (B : ℤ) (hDel : 1 ≤ Del) (hh : R.t + 3 ≤ 2 * h)
    (hU : 4 * (Del : ℚ) * ((R.k : ℚ) - 2) < U) (hW : W < 0) (hB : -(B : ℚ) < W)
    (hUi : ∃ z : ℤ, U = z + 1 / 2) (hWi : ∃ z : ℤ, W = z + 1 / 2) : HCParam R where
  u := fun i => if i.1 = 0 then U else if i.1 + 1 = R.k then W else 4 * (Del : ℚ) * ((R.k : ℚ) - 1 - (i.1 : ℚ)) - 1 / 2
  v := fun i => 4 * (Del : ℚ) * ((R.k : ℚ) - 2 - (i.1 : ℚ))
  b := fun j => (B : ℚ) + 2 * (h : ℚ) * (j.1 : ℚ)
  e := fun j => (B : ℚ) + 2 * (h : ℚ) * (j.1 : ℚ) + h
  u_gt_v := fun i => by
    have hi := i.2
    have hD : (1 : ℚ) ≤ Del := by exact_mod_cast hDel
    by_cases h0 : i.1 = 0
    · simp only [h0, if_true]; simpa using hU
    · have h1 : i.1 + 1 ≠ R.k := by omega
      simp only [h0, h1, if_false]; linarith
  v_gt_u := fun i => by
    have hi := i.2
    by_cases h1 : i.1 + 1 + 1 = R.k
    · have : (R.k : ℚ) = (i.1 : ℚ) + 2 := by exact_mod_cast h1.symm
      simp only [h1, if_true, Nat.succ_ne_zero, if_false]; rw [this]; linarith
    · simp only [h1, Nat.succ_ne_zero, if_false]; push_cast; linarith
  u_last_gt := fun h h' => by
    have := R.m_add_three_le_k
    have h0 : R.k - 1 ≠ 0 := by omega
    have h1 : R.k - 1 + 1 = R.k := by omega
    simp only [h0, h1, if_true, if_false]; simpa using hB
  gap_be := fun j => by
    have : (R.t : ℚ) + 3 ≤ 2 * h := by exact_mod_cast hh
    linarith
  gap_eb := fun j hj => by
    have : (R.t : ℚ) + 3 ≤ 2 * h := by exact_mod_cast hh
    push_cast; linarith
  e_int := fun j => ⟨B + 2 * h * j.1 + h, by push_cast; ring⟩
  u_half := fun i => by
    by_cases h0 : i.1 = 0
    · simpa only [h0, if_true] using hUi
    · by_cases h1 : i.1 + 1 = R.k
      · simpa only [h0, h1, if_true, if_false] using hWi
      · simp only [h0, h1, if_false]
        exact ⟨4 * Del * (R.k - 1 - i.1) - 1, by push_cast; ring⟩
  v_int := fun i => ⟨4 * Del * (R.k - 2 - i.1), by push_cast; ring⟩
  b_int := fun j => ⟨B + 2 * h * j.1, by push_cast; ring⟩

structure Num (R : Ranks) (x eps : ℝ) (Del h : ℕ) : Prop where
  Del_pos : 1 ≤ Del
  hh : R.t + 3 ≤ 2 * h
  x_ge : 1 ≤ x
  third : x ^ (eps / 3) ≤ x ^ eps / 2
  a_le : 4 * x ^ ((11 : ℝ) / 2) ≤ bx x eps
  kx : 2 * (R.k : ℝ) * x ≤ Real.exp (x ^ eps / 2)
  eta_le : 2 * (R.m : ℝ) * h ≤ Real.exp (x ^ eps / 2)
  kDel : 4 * (R.k : ℝ) * Del ≤ Real.exp (x ^ eps / 2)
  eta_log : Real.log (2 * (R.m : ℝ) * h) ≤ x ^ (eps / 4)

theorem sqrt_bx (x eps : ℝ) : Real.sqrt (bx x eps) = Real.exp (x ^ eps / 2) := by
  rw [bx, Real.exp_half]

theorem Num.facts {R : Ranks} {x eps : ℝ} {Del h : ℕ} (N : Num R x eps Del h) :
    Real.exp (x ^ eps / 2) ≤ bpC x eps ∧ bpC x eps ≤ aC x eps ∧ Real.exp (x ^ eps / 2) ≤ bx x eps ∧
      bx x eps ≤ aC x eps ∧ 4 * aC x eps ≤ bx x eps ^ 2 ∧ 2 * (R.k : ℝ) ≤ bpC x eps / x ∧ bpC x eps / x ≤ bpC x eps ∧
      (5 : ℝ) ≤ R.k ∧ 2 * (R.k : ℝ) ≤ Real.exp (x ^ eps / 2) := by
  have hx := N.x_ge
  have hL : 0 ≤ x ^ eps := by positivity
  have hb : 0 < bx x eps := Real.exp_pos _
  have hY : 1 ≤ x ^ ((11 : ℝ) / 2) := Real.one_le_rpow hx (by norm_num)
  have hX : 1 ≤ Real.exp (x ^ (eps / 3)) := Real.one_le_exp (by positivity)
  have hba : bx x eps ≤ aC x eps := by unfold aC; nlinarith
  have h1 : Real.exp (x ^ eps / 2) ≤ bpC x eps := by
    unfold bpC
    rw [le_div_iff₀ (by positivity), ← Real.exp_add]
    refine le_trans ?_ hba
    exact Real.exp_le_exp.2 (by linarith [N.third])
  have hk : (5 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k; have := R.two_le_m
    exact_mod_cast (by omega : 5 ≤ R.k)
  have hbp : 0 ≤ bpC x eps := le_trans (Real.exp_pos _).le h1
  refine ⟨h1, ?_, Real.exp_le_exp.2 (by linarith), hba, ?_, ?_, div_le_self hbp hx, hk, ?_⟩
  · unfold bpC; exact div_le_self (by linarith) hX
  · unfold aC; nlinarith [N.a_le]
  · rw [le_div_iff₀ (by linarith)]; linarith [N.kx]
  · nlinarith [N.kx]

theorem half_k (R : Ranks) : ∃ z : ℤ, ((R.k : ℚ) - 1) / 2 = z + 1 / 2 := by
  obtain ⟨c, hc⟩ := R.k_even
  exact ⟨c - 1, by rw [hc]; push_cast; ring⟩

variable {R : Ranks} {x eps : ℝ} {Del h : ℕ}

def hcTop (N : Num R x eps Del h) : HCParam R :=
  hcMk R Del h ((⌈aC x eps⌉ : ℚ) + ((R.k : ℚ) - 1) / 2) (-(⌈bpC x eps⌉ : ℚ) - ((R.k : ℚ) - 1) / 2)
    (⌈bpC x eps⌉ + ⌊bpC x eps / x⌋) N.Del_pos N.hh
    (by
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := N.facts
      have h1 := Int.le_ceil (aC x eps)
      have h2 := N.kDel
      have h3 : (0 : ℝ) ≤ Del := by positivity
      have : 4 * (Del : ℝ) * ((R.k : ℝ) - 2) < (⌈aC x eps⌉ : ℝ) + ((R.k : ℝ) - 1) / 2 := by nlinarith
      exact_mod_cast this)
    (by
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := N.facts
      have h1 := Int.le_ceil (bpC x eps)
      have : -(⌈bpC x eps⌉ : ℝ) - ((R.k : ℝ) - 1) / 2 < 0 := by linarith
      exact_mod_cast this)
    (by
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := N.facts
      have h1 := Int.lt_floor_add_one (bpC x eps / x)
      have : -((⌈bpC x eps⌉ + ⌊bpC x eps / x⌋ : ℤ) : ℝ) < -(⌈bpC x eps⌉ : ℝ) - ((R.k : ℝ) - 1) / 2 := by
        push_cast; linarith
      exact_mod_cast this)
    (by obtain ⟨z, hz⟩ := half_k R; exact ⟨⌈aC x eps⌉ + z, by rw [hz]; push_cast; ring⟩)
    (by obtain ⟨z, hz⟩ := half_k R; exact ⟨-⌈bpC x eps⌉ - z - 1, by rw [hz]; push_cast; ring⟩)

def hcOff (N : Num R x eps Del h) : HCParam R :=
  hcMk R Del h (4 * (Del : ℚ) * ((R.k : ℚ) - 2) + 4 * R.k * Del + 1 / 2) (-1 / 2) ⌈bx x eps⌉ N.Del_pos N.hh
    (by have : (0 : ℚ) ≤ 4 * R.k * Del := by positivity
        linarith)
    (by norm_num)
    (by
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := N.facts
      have h1 := Int.le_ceil (bx x eps)
      have : -((⌈bx x eps⌉ : ℤ) : ℝ) < -1 / 2 := by linarith
      exact_mod_cast this)
    ⟨4 * Del * (R.k - 2) + 4 * R.k * Del, by push_cast; ring⟩ ⟨-1, by norm_num⟩

theorem place_rows (D : D7) (N : Num D.R x eps Del h) (hDel : D.s.Del = Del)
    (hT : ∀ τ, Top D τ → D.hc τ = hcTop N) (hO : ∀ τ, ¬ Top D τ → D.hc τ = hcOff N) :
    OneScale D x eps (2 * (D.R.m : ℝ) * h) ∧ Nodes D x eps ∧
    (∀ τ (j : ℕ) (hj : j + 1 < D.R.m), (((D.hc τ).b ⟨j + 1, hj⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) = 2 * h) ∧
    (∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧
      (((D.hc τ).v i : ℚ) : ℝ) ≤ 4 * (D.R.k : ℝ) * (D.s.Del : ℝ)) ∧
    (∀ τ, ¬ Top D τ → 4 * (D.R.k : ℝ) * (D.s.Del : ℝ) ≤ uFirst D τ - vFirst D τ ∧
      uFirst D τ - vFirst D τ ≤ 8 * (D.R.k : ℝ) * (D.s.Del : ℝ) ∧ uLast D τ = vLast D τ - 1 / 2) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := N.facts
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have k0 : D.R.k - 1 ≠ 0 := by omega
  have k1 : D.R.k - 1 + 1 = D.R.k := by omega
  have k2 : ((D.R.k - 2 : ℕ) : ℝ) = (D.R.k : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have m1 : ((D.R.m - 1 : ℕ) : ℝ) = (D.R.m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hh : (1 : ℝ) ≤ h := by have := N.hh; exact_mod_cast (by omega : 1 ≤ h)
  have hD : (1 : ℝ) ≤ Del := by exact_mod_cast N.Del_pos
  have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have he := N.eta_le
  have c1 := Int.le_ceil (aC x eps)
  have c2 := Int.ceil_lt_add_one (aC x eps)
  have c3 := Int.le_ceil (bpC x eps)
  have c4 := Int.ceil_lt_add_one (bpC x eps)
  have c5 := Int.le_ceil (bx x eps)
  have c6 := Int.ceil_lt_add_one (bx x eps)
  have c7 := Int.floor_le (bpC x eps / x)
  have c8 := Int.lt_floor_add_one (bpC x eps / x)
  have hj : ∀ j : Fin D.R.m, 0 ≤ 2 * (h : ℝ) * (j.1 : ℝ) ∧ 2 * (h : ℝ) * (j.1 : ℝ) + 2 * h ≤ 2 * (D.R.m : ℝ) * h := by
    intro j
    have : (j.1 : ℝ) + 1 ≤ D.R.m := by exact_mod_cast j.2
    exact ⟨by positivity, by nlinarith⟩
  have tU : ∀ τ, Top D τ → uFirst D τ = (⌈aC x eps⌉ : ℝ) + ((D.R.k : ℝ) - 1) / 2 := fun τ ht => by
    simp [uFirst, hT τ ht, hcTop, hcMk]
  have tW : ∀ τ, Top D τ → uLast D τ = -(⌈bpC x eps⌉ : ℝ) - ((D.R.k : ℝ) - 1) / 2 := fun τ ht => by
    simp [uLast, hT τ ht, hcTop, hcMk, k0, k1]
  have tB : ∀ τ, Top D τ → bFirst D τ = (⌈bpC x eps⌉ : ℝ) + (⌊bpC x eps / x⌋ : ℝ) := fun τ ht => by
    simp [bFirst, hT τ ht, hcTop, hcMk]
  have tb : ∀ τ, Top D τ → ∀ j, (((D.hc τ).b j : ℚ) : ℝ) =
      (⌈bpC x eps⌉ : ℝ) + (⌊bpC x eps / x⌋ : ℝ) + 2 * (h : ℝ) * (j.1 : ℝ) := fun τ ht j => by
    simp [hT τ ht, hcTop, hcMk]
  have te : ∀ τ, Top D τ → ∀ j, (((D.hc τ).e j : ℚ) : ℝ) =
      (⌈bpC x eps⌉ : ℝ) + (⌊bpC x eps / x⌋ : ℝ) + 2 * (h : ℝ) * (j.1 : ℝ) + h := fun τ ht j => by
    simp [hT τ ht, hcTop, hcMk]
  have ob : ∀ τ, ¬ Top D τ → ∀ j, (((D.hc τ).b j : ℚ) : ℝ) =
      (⌈bx x eps⌉ : ℝ) + 2 * (h : ℝ) * (j.1 : ℝ) := fun τ ht j => by
    simp [hO τ ht, hcOff, hcMk]
  have oe : ∀ τ, ¬ Top D τ → ∀ j, (((D.hc τ).e j : ℚ) : ℝ) =
      (⌈bx x eps⌉ : ℝ) + 2 * (h : ℝ) * (j.1 : ℝ) + h := fun τ ht j => by
    simp [hO τ ht, hcOff, hcMk]
  have av : ∀ τ i, (((D.hc τ).v i : ℚ) : ℝ) = 4 * (Del : ℝ) * ((D.R.k : ℝ) - 2 - (i.1 : ℝ)) := fun τ i => by
    by_cases ht : Top D τ
    · simp [hT τ ht, hcTop, hcMk]
    · simp [hO τ ht, hcOff, hcMk]
  refine ⟨⟨by positivity, N.eta_log, fun τ ht => ⟨tU τ ht, tW τ ht, tB τ ht, fun j => ?_⟩, fun τ ht j => ⟨?_, ?_⟩⟩,
    ⟨fun τ j => ?_, fun τ => ?_, fun τ ht => ?_⟩, fun τ j hj' => ?_, fun τ i => ?_, fun τ ht => ?_⟩
  · rw [te τ ht]; linarith [(hj j).2]
  · rw [ob τ ht]; linarith [(hj j).1]
  · rw [oe τ ht]; linarith [(hj j).2]
  · rw [sqrt_bx]
    by_cases ht : Top D τ
    · rw [tb τ ht]; constructor <;> linarith [(hj j).1, (hj j).2]
    · rw [ob τ ht]; constructor <;> linarith [(hj j).1, (hj j).2]
  · unfold bLast bFirst
    have := (hj ⟨D.R.m - 1, by omega⟩).2
    by_cases ht : Top D τ
    · rw [tb τ ht, tb τ ht]; simp only [Nat.cast_zero, mul_zero] at this ⊢; linarith
    · rw [ob τ ht, ob τ ht]; simp only [Nat.cast_zero, mul_zero] at this ⊢; linarith
  · rw [sqrt_bx, tU τ ht, tW τ ht, tB τ ht]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · push_cast
    by_cases ht : Top D τ
    · rw [tb τ ht, tb τ ht]; push_cast; ring
    · rw [ob τ ht, ob τ ht]; push_cast; ring
  · rw [av, hDel]
    have : (i.1 : ℝ) + 2 ≤ D.R.k := by have := i.2; exact_mod_cast (by omega : i.1 + 2 ≤ D.R.k)
    have h0 : (0 : ℝ) ≤ i.1 := by positivity
    push_cast
    constructor <;> nlinarith
  · have oU : uFirst D τ = 4 * (Del : ℝ) * ((D.R.k : ℝ) - 2) + 4 * D.R.k * Del + 1 / 2 := by
      simp [uFirst, hO τ ht, hcOff, hcMk]
    have oW : uLast D τ = -1 / 2 := by simp [uLast, hO τ ht, hcOff, hcMk, k0, k1]
    unfold vFirst vLast
    rw [oU, oW, av, av, hDel]
    simp only [k2, Nat.cast_zero]
    push_cast
    refine ⟨by linarith, by nlinarith, by ring⟩

structure Arith (H : Host R) where
  T : ℕ
  T_prime : T.Prime
  hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E
  ht : THyp H
  hlev : T ∈ H.levelPrimes
  hpde : T ≠ H.pde ∧ T ≠ H.pde'
  pz : 𝓞 H.E
  hK : (pz : H.E) ∈ H.K
  hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E)
  hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)}

open Classical in

def hcAll (H : Host R) (N : Num R x eps Del h) (τ : Tau2 R) : HCParam R :=
  if ∃ t : H.TT, (τ : R.GG) = R.tau1 t then hcTop N else hcOff N

def rcd (H : Host R) (A : Arith H) (G : LocalGap H) (N : Num R x eps Del h) (Gam : ℝ) (hG : 1 < Gam) : D7 :=
  haveI : Fact A.T.Prime := ⟨A.T_prime⟩
  rankRecord H (hcAll H N) Del (by exact_mod_cast N.Del_pos)
    (fun τ l hl => by unfold hcAll; split_ifs <;> simp [hcTop, hcOff, hcMk] <;> ring)
    (fun τ l hl => by
      have h1 : l + 1 + 1 ≠ R.k := by omega
      unfold hcAll; split_ifs <;> simp [hcTop, hcOff, hcMk, h1] <;> (left; ring))
    (fun _ _ => 1) (fun _ _ => one_pos) (fun _ => 1) (fun _ => one_pos) 1 A.T A.T
    (by exact_mod_cast A.T_prime.pos) Gam hG le_rfl
    (by have : (0 : ℝ) ≤ 1 / ((R.f : ℝ) * R.k) * A.T := by positivity
        linarith)
    A.hg A.ht A.hlev A.hpde A.pz A.hK A.hpz A.hcong G

theorem rcd_rows (H : Host R) (A : Arith H) (G : LocalGap H) (N : Num R x eps Del h) (Gam : ℝ) (hG : 1 < Gam) :
    (∀ τ, Top (rcd H A G N Gam hG) τ → (rcd H A G N Gam hG).hc τ = hcTop (R := (rcd H A G N Gam hG).R) N) ∧
    (∀ τ, ¬ Top (rcd H A G N Gam hG) τ → (rcd H A G N Gam hG).hc τ = hcOff (R := (rcd H A G N Gam hG).R) N) :=
  ⟨fun τ ht => show hcAll H N τ = hcTop N from if_pos ht, fun τ ht => show hcAll H N τ = hcOff N from if_neg ht⟩

open Classical in

theorem card_top (D : D7) : (Finset.univ.filter (fun τ => Top D τ)).card = D.host.TT.card := by
  obtain ⟨h1, -, -, h4, -⟩ := factTopsThick D.R D.host
  rw [← h4]
  have hinj : Function.Injective (fun τ : D.what₂.Tau => (D.eTau τ : D.R.GG)) :=
    Subtype.val_injective.comp D.eTau.injective
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext g
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨τ, ⟨t, ht⟩, rfl⟩
    exact Finset.mem_image.2 ⟨t, t.2, ht.symm⟩
  · intro hg
    obtain ⟨t, ht, e⟩ := Finset.mem_image.1 hg
    refine ⟨D.eTau.symm ⟨g, h1 g hg⟩, ⟨⟨t, ht⟩, ?_⟩, ?_⟩ <;> simp [e]

theorem even_of_const (D : D7) (A B : HCParam D.R) (hT : ∀ τ, Top D τ → D.hc τ = A) (hO : ∀ τ, ¬ Top D τ → D.hc τ = B)
    (hev : Even D.host.TT.card) : EvenCentres D := by
  classical
  intro j
  obtain ⟨a, ha⟩ := A.e_int j
  obtain ⟨b, hb⟩ := B.e_int j
  obtain ⟨c, hc⟩ := hev
  have h1 := card_top D
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset D.what₂.Tau)) (fun τ => Top D τ)
  rw [Finset.card_univ, D.what₂.card_Tau, h1, hc] at h2
  have h3 : ((Finset.univ.filter (fun τ => ¬ Top D τ)).card : ℚ) = 2 * D.R.n - 2 * c := by
    have : ((c + c + (Finset.univ.filter (fun τ => ¬ Top D τ)).card : ℕ) : ℚ) = ((2 * D.R.n : ℕ) : ℚ) := by
      rw [h2]; rfl
    push_cast at this; linarith
  refine ⟨c * a + (D.R.n - c) * b, ?_⟩
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ => Top D τ),
    Finset.sum_congr rfl (fun τ hτ => show (D.hc τ).e j = (a : ℚ) by rw [hT τ (Finset.mem_filter.1 hτ).2, ha]),
    Finset.sum_congr rfl (fun τ hτ => show (D.hc τ).e j = (b : ℚ) by rw [hO τ (Finset.mem_filter.1 hτ).2, hb]),
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, h3, h1, hc]
  push_cast; ring

theorem even_card {H : Host R} {J : ℕ} (h : TopsCoset H J) (hm : 2 * R.m ≤ 2 ^ R.e) : Even H.TT.card :=
  h.card_even hm

theorem rcd_datum (H : Host R) (A : Arith H) (G : LocalGap H) (N : Num R x eps Del h) (Gam : ℝ) (hG : 1 < Gam) {J : ℕ}
    (hJ : TopsCoset H J) (hm : 2 * R.m ≤ 2 ^ R.e) :
    OneScale (rcd H A G N Gam hG) x eps (2 * (R.m : ℝ) * h) ∧ Nodes (rcd H A G N Gam hG) x eps ∧
      EvenCentres (rcd H A G N Gam hG) ∧ DelInt (rcd H A G N Gam hG) := by
  obtain ⟨r1, r2⟩ := rcd_rows H A G N Gam hG
  obtain ⟨o, n, -⟩ := place_rows (rcd H A G N Gam hG) N rfl r1 r2
  exact ⟨o, n, even_of_const _ _ _ r1 r2 (even_card hJ hm), Del, rfl⟩

@[irreducible] def P (n : ℕ) : ℝ := 2 ^ n

theorem charpoly_eq_of_isIso (n : ℕ) : P n = 2 ^ n := by unfold P; rfl

theorem natCast_two_pow (n : ℕ) : ((2 ^ n : ℕ) : ℝ) = P n := by rw [charpoly_eq_of_isIso]; push_cast; rfl

theorem twoPow_pos (n : ℕ) : 0 < P n := by rw [charpoly_eq_of_isIso]; positivity

theorem twoPow_mul_twoPow (a b : ℕ) : P a * P b = P (a + b) := by simp only [charpoly_eq_of_isIso, pow_add]

theorem twoPow_pow (a n : ℕ) : P a ^ n = P (a * n) := by simp only [charpoly_eq_of_isIso, pow_mul]

theorem P_le {a b : ℕ} (h : a ≤ b) : P a ≤ P b := by
  rw [charpoly_eq_of_isIso, charpoly_eq_of_isIso]; exact pow_le_pow_right₀ (by norm_num) h

theorem twoPow_rpow (N : ℕ) (c : ℝ) : P N ^ c = (2 : ℝ) ^ ((N : ℝ) * c) := by
  rw [charpoly_eq_of_isIso, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

theorem twoPow_rpow_of_mul_eq {N n : ℕ} {c : ℝ} (h : (N : ℝ) * c = n) : P N ^ c = P n := by
  rw [twoPow_rpow, h, Real.rpow_natCast, charpoly_eq_of_isIso]

theorem twoPow_rpow_le {N n : ℕ} {c : ℝ} (h : (N : ℝ) * c ≤ n) : P N ^ c ≤ P n := by
  rw [twoPow_rpow, charpoly_eq_of_isIso n, ← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

theorem twoPow_le_rpow {N n : ℕ} {c : ℝ} (h : (n : ℝ) ≤ (N : ℝ) * c) : P n ≤ P N ^ c := by
  rw [twoPow_rpow, charpoly_eq_of_isIso n, ← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

theorem twoPow_le_exp {n : ℕ} {y : ℝ} (h : (n : ℝ) ≤ y) : P n ≤ Real.exp y := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc P n = 2 ^ n := charpoly_eq_of_isIso n
    _ ≤ Real.exp 1 ^ n := pow_le_pow_left₀ (by norm_num) h2 n
    _ = Real.exp n := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ Real.exp y := Real.exp_le_exp.2 h

theorem log_le_of_le_P {n : ℕ} {y : ℝ} (hy : 0 < y) (h : y ≤ P n) : Real.log y ≤ n := by
  rw [Real.log_le_iff_le_exp hy]; exact h.trans (twoPow_le_exp le_rfl)

theorem one_le_P (n : ℕ) : 1 ≤ P n := by rw [charpoly_eq_of_isIso]; exact one_le_pow₀ (by norm_num)

theorem L_small : P 2800 ^ ((1 : ℝ) / 200) = 16384 := by
  rw [twoPow_rpow_of_mul_eq (n := 14) (by norm_num), charpoly_eq_of_isIso]; norm_num

theorem num_small : Num R0 (P 2800) (1 / 200) 1 9 where
  Del_pos := le_rfl
  hh := by decide
  x_ge := one_le_P _
  third := by
    rw [L_small]
    refine (twoPow_rpow_le (n := 5) (by norm_num)).trans ?_
    rw [charpoly_eq_of_isIso]; norm_num
  a_le := by
    have h4 : (4 : ℝ) = P 2 := by rw [charpoly_eq_of_isIso]; norm_num
    rw [bx, L_small, twoPow_rpow_of_mul_eq (n := 15400) (by norm_num), h4, twoPow_mul_twoPow]
    exact twoPow_le_exp (by norm_num)
  kx := by
    have h4 : 2 * (R0.k : ℝ) = P 4 := by rw [charpoly_eq_of_isIso]; show 2 * ((8 : ℕ) : ℝ) = _; norm_num
    rw [L_small, h4, twoPow_mul_twoPow]
    exact twoPow_le_exp (by norm_num)
  eta_le := by
    rw [L_small]
    refine le_trans ?_ (twoPow_le_exp (n := 6) (by norm_num))
    rw [charpoly_eq_of_isIso]; show 2 * ((2 : ℕ) : ℝ) * _ ≤ _; norm_num
  kDel := by
    rw [L_small]
    refine le_trans ?_ (twoPow_le_exp (n := 6) (by norm_num))
    rw [charpoly_eq_of_isIso]; show 4 * ((8 : ℕ) : ℝ) * _ ≤ _; norm_num
  eta_log := by
    have h1 : 2 * (R0.m : ℝ) * ((9 : ℕ) : ℝ) = 36 := by show 2 * ((2 : ℕ) : ℝ) * _ = _; norm_num
    rw [h1]
    refine (log_le_of_le_P (n := 6) (by norm_num) (by rw [charpoly_eq_of_isIso]; norm_num)).trans ?_
    refine le_trans ?_ (twoPow_le_rpow (n := 3) (by norm_num))
    rw [charpoly_eq_of_isIso]; norm_num

def H1 : Host R0 :=
  { H0 with
    TT := Finset.univ.image (fun s : R0.A => 0 + 2 ^ 1 • s)
    splitBound := 6
    split_small := fun p hp h2 hle => by
      have := hp.two_le
      interval_cases p
      · exact absurd rfl h2
      · show jacobiSym (-599) 3 = 1; norm_num
      · exact absurd hp (by norm_num)
      · show jacobiSym (-599) 5 = 1; norm_num
      · exact absurd hp (by norm_num)
    small_le := fun l hl h2 hd =>
      absurd ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp
        (hl.dvd_of_dvd_pow (show l ∣ 2 ^ (2 + 2) from hd))) h2 }

def A1 : Arith H1 :=
  ⟨T0, examplePrime_prime, exampleHost_type_primes_split, ⟨exampleHost_typeHypothesis.cond, exampleHost_typeHypothesis.bb, exampleHost_typeHypothesis.jac⟩, examplePrime_mem_levelPrimes, examplePrime_ne_split_primes, π0O, π0_mem_K, π0_norm, π0_cong⟩

theorem exists_not_top (D : D7) : ∃ τ, ¬ Top D τ := by
  obtain ⟨h1, h2⟩ := factPlaces D.R.toFrame
  refine ⟨D.eTau.symm ⟨D.R.tau2 0, (h1 _).2 (Or.inr ⟨0, rfl⟩)⟩, ?_⟩
  rintro ⟨t, ht⟩
  rw [Equiv.apply_symm_apply] at ht
  exact h2 _ _ ht.symm

theorem exists_top (D : D7) (h : D.host.TT.Nonempty) : ∃ τ, Top D τ := by
  obtain ⟨h1, -⟩ := factPlaces D.R.toFrame
  obtain ⟨t, ht⟩ := h
  exact ⟨D.eTau.symm ⟨D.R.tau1 t, (h1 _).2 (Or.inl ⟨t, rfl⟩)⟩, ⟨t, ht⟩, by rw [Equiv.apply_symm_apply]⟩

theorem gam_gt {CG y : ℝ} (R : Ranks) (hC : 0 < CG) (hy : 0 < y) : 1 < Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * y) := by
  have h2 : (0 : ℝ) < (R.m : ℝ) := by have := R.two_le_m; exact_mod_cast (by omega : 0 < R.m)
  have h3 : (0 : ℝ) < (R.f : ℝ) := by
    have : 0 < R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  exact Real.one_lt_exp_iff.2 (by positivity)

theorem small_host_tops_coset : TopsCoset H1 1 where
  lo := by decide
  hi := by decide
  coset := ⟨0, fun t => Finset.mem_image.trans
    ⟨fun ⟨s, _, h⟩ => ⟨s, congrArg R0.h h.symm⟩, fun ⟨s, h⟩ => ⟨s, Finset.mem_univ _, (exampleRanks_h_injective h).symm⟩⟩⟩

theorem small_host_dead_labels : DeadLabels H1 := ⟨⟨0, Finset.mem_singleton_self _⟩, 3, exampleRanks_jetIndex_bound, le_refl 50⟩

theorem floor_le_six {y : ℝ} (hy : 0 ≤ y) (h : y ^ 5 ≤ 16384) : ⌊y⌋₊ ≤ 6 := by
  apply Nat.le_of_lt_succ
  rw [Nat.floor_lt hy]
  by_contra hc
  have h7 : (7 : ℝ) ≤ y := by push_cast at hc; linarith [not_lt.1 hc]
  have h8 := pow_le_pow_left₀ (by norm_num) h7 5
  norm_num at h8
  linarith

private theorem small_host_split_clause {x eps : ℝ} (hx : 1 ≤ x) (he : 0 ≤ eps) (h : ⌊x ^ (eps / 5)⌋₊ ≤ 6) : SplitLab H1 x eps := by
  have h1 : 1 ≤ x ^ (eps / 100) := Real.one_le_rpow hx (by positivity)
  refine SplitLab.of_one h ?_ ?_
  · rw [exampleRanks_o]; exact_mod_cast h1
  · show ((2 ^ (2 + 2) : ℕ) : ℝ) ≤ 4 * ((4 : ℕ) : ℝ) * _
    push_cast; linarith

theorem small_witness (D0 : D7) (CG : ℝ) (hC : 0 < CG) : ∃ D : D7, D.host.TT.card = 2 ∧ D.R.f = 8 ∧
    OneScale D (P 2800) (1 / 200) 36 ∧ Nodes D (P 2800) (1 / 200) ∧ Labels D (P 2800) (1 / 200) CG ∧
    TopsCoset D.host 1 ∧ EvenCentres D ∧ DelInt D := by
  have hG := gam_gt R0 hC (Real.rpow_pos_of_pos (twoPow_pos 2800) (1 / 200))
  obtain ⟨o, n, e, d⟩ := rcd_datum H1 A1 (LocalGap.localGapOfRecord D0 H1) num_small _ hG small_host_tops_coset (by decide)
  have h1 : 2 * (R0.m : ℝ) * ((9 : ℕ) : ℝ) = 36 := by show 2 * ((2 : ℕ) : ℝ) * _ = _; norm_num
  rw [h1] at o
  refine ⟨_, small_host_tops_coset.card_eq (by decide), rfl, o, n, (labels_iff _ _ _ _).2 ⟨small_host_dead_labels, ?_, hC, fun u => Real.log_exp _⟩,
    small_host_tops_coset, e, d⟩
  refine small_host_split_clause (one_le_P _) (by norm_num) (floor_le_six (Real.rpow_pos_of_pos (twoPow_pos _) _).le ?_)
  rw [← Real.rpow_natCast (P 2800 ^ _), ← Real.rpow_mul (twoPow_pos _).le, twoPow_rpow_of_mul_eq (n := 14) (by norm_num), charpoly_eq_of_isIso]
  norm_num

theorem L_coarse : P 1 ^ (12 : ℝ) = 4096 := by
  rw [twoPow_rpow_of_mul_eq (n := 12) (by norm_num), charpoly_eq_of_isIso]; norm_num

theorem X_coarse : P 1 ^ ((12 : ℝ) / 3) = 16 := by
  rw [twoPow_rpow_of_mul_eq (n := 4) (by norm_num), charpoly_eq_of_isIso]; norm_num

theorem Y_coarse : P 1 ^ ((11 : ℝ) / 2) ≤ 64 :=
  (twoPow_rpow_le (n := 6) (by norm_num)).trans (by rw [charpoly_eq_of_isIso]; norm_num)

theorem le_exp_of_le {y z : ℝ} (n : ℕ) (h1 : y ≤ 2 ^ n) (h2 : (n : ℝ) ≤ z) : y ≤ Real.exp z :=
  (h1.trans (charpoly_eq_of_isIso n).ge).trans (twoPow_le_exp h2)

theorem num_coarse : Num R0 (P 1) 12 1 9 where
  Del_pos := le_rfl
  hh := by decide
  x_ge := one_le_P _
  third := by rw [L_coarse, X_coarse]; norm_num
  a_le := by
    rw [bx, L_coarse]
    exact le_exp_of_le 8 (by linarith [Y_coarse]) (by norm_num)
  kx := by
    rw [L_coarse, charpoly_eq_of_isIso]
    exact le_exp_of_le 5 (by show 2 * ((8 : ℕ) : ℝ) * _ ≤ _; norm_num) (by norm_num)
  eta_le := by
    rw [L_coarse]
    exact le_exp_of_le 6 (by show 2 * ((2 : ℕ) : ℝ) * _ ≤ _; norm_num) (by norm_num)
  kDel := by
    rw [L_coarse]
    exact le_exp_of_le 6 (by show 4 * ((8 : ℕ) : ℝ) * _ ≤ _; norm_num) (by norm_num)
  eta_log := by
    have h1 : 2 * (R0.m : ℝ) * ((9 : ℕ) : ℝ) = 36 := by show 2 * ((2 : ℕ) : ℝ) * _ = _; norm_num
    rw [h1, twoPow_rpow_of_mul_eq (n := 3) (by norm_num)]
    refine (log_le_of_le_P (n := 6) (by norm_num) (by rw [charpoly_eq_of_isIso]; norm_num)).trans ?_
    rw [charpoly_eq_of_isIso]; norm_num

theorem small_host_root_discriminant_le : H1.v ≤ 4096 := by
  have h := (factRd R0 H1).2.1
  have h1 : (H1.QS : ℝ) / 2 ≤ 8 := by show ((2 ^ (2 + 2) : ℕ) : ℝ) / 2 ≤ 8; norm_num
  have h2 : Real.sqrt ((H1.q : ℝ) * H1.d) ≤ 1024 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by show ((571 : ℕ) : ℝ) * ((599 : ℕ) : ℝ) ≤ _; norm_num⟩
  have h3 := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by norm_num)
  unfold Host.v
  linarith

theorem a_thresholds {x eps v : ℝ} (h1 : x ^ ((11 : ℝ) / 2) ≤ bx x eps) (h2 : x ^ ((11 : ℝ) / 2) * v ≤ bx x eps) :
    aC x eps ≤ bx x eps ^ 2 ∧ aC x eps * v ≤ bx x eps ^ 2 := by
  have hb : 0 < bx x eps := Real.exp_pos _
  unfold aC
  constructor <;> nlinarith

theorem thresh_coarse {v : ℝ} (hv : v ≤ 4096) : ThreshNums (P 1) 12 8 8 40 32 36 v 599 := by
  have hY := Y_coarse
  have hY0 : 0 < P 1 ^ ((11 : ℝ) / 2) := Real.rpow_pos_of_pos (twoPow_pos _) _
  obtain ⟨a1, a2⟩ := a_thresholds (x := P 1) (eps := 12) (v := v)
    (by rw [bx, L_coarse]; exact le_exp_of_le 6 (by linarith) (by norm_num))
    (by rw [bx, L_coarse]; exact le_exp_of_le 18 (by nlinarith) (by norm_num))
  refine ⟨by rw [charpoly_eq_of_isIso]; norm_num, a1, a2, ?_, ?_, by linarith, ?_⟩
  · rw [X_coarse]; exact le_exp_of_le 15 (by linarith) (by norm_num)
  · rw [bx, L_coarse]
    have := pow_le_pow_left₀ hY0.le hY 3
    exact le_exp_of_le 50 (by linarith) (by norm_num)
  · rw [bx, L_coarse, X_coarse, charpoly_eq_of_isIso, show (4096 : ℝ) = 4080 + 16 by norm_num, Real.exp_add]
    exact mul_le_mul_of_nonneg_right (le_exp_of_le 9 (by norm_num) (by norm_num)) (Real.exp_pos _).le

theorem coarse_witness (D0 : D7) (CG : ℝ) (hC : 0 < CG) : ∃ D : D7, D.host.TT.card = 2 ∧ D.R.f = 8 ∧
    OneScaleDatum D (P 1) 12 36 1 ∧ Nodes D (P 1) 12 ∧ Labels D (P 1) 12 CG := by
  have hG := gam_gt R0 hC (Real.rpow_pos_of_pos (twoPow_pos 1) 12)
  obtain ⟨o, n, e, d⟩ := rcd_datum H1 A1 (LocalGap.localGapOfRecord D0 H1) num_coarse _ hG small_host_tops_coset (by decide)
  have h1 : 2 * (R0.m : ℝ) * ((9 : ℕ) : ℝ) = 36 := by show 2 * ((2 : ℕ) : ℝ) * _ = _; norm_num
  rw [h1] at o
  refine ⟨_, small_host_tops_coset.card_eq (by decide), rfl, ⟨o, small_host_tops_coset, e, ?_, d⟩, n,
    (labels_iff _ _ _ _).2 ⟨small_host_dead_labels, ?_, hC, fun u => Real.log_exp _⟩⟩
  · show ThreshNums (P 1) 12 ((8 : ℕ) : ℝ) ((8 : ℕ) : ℝ) ((40 : ℕ) : ℝ) (4 * ((8 : ℕ) : ℝ) * ((((1 : ℕ) : ℚ)) : ℝ)) 36 H1.v
      ((599 : ℕ) : ℝ)
    convert thresh_coarse small_host_root_discriminant_le using 1 <;> norm_num
  · refine small_host_split_clause (one_le_P _) (by norm_num) (floor_le_six (Real.rpow_pos_of_pos (twoPow_pos _) _).le ?_)
    rw [← Real.rpow_natCast (P 1 ^ _), ← Real.rpow_mul (twoPow_pos _).le, twoPow_rpow_of_mul_eq (n := 12) (by norm_num), charpoly_eq_of_isIso]
    norm_num

def Rk (α e κ : ℕ) (h1 : 1 ≤ α) (h2 : α ≤ e + 1) (h3 : e + 1 ≤ κ) (h4 : α + 2 ≤ κ) : Ranks :=
  have a1 : 2 ^ 1 ≤ 2 ^ α := Nat.pow_le_pow_right (by norm_num) h1
  have a2 : 2 ^ α ≤ 2 * 2 ^ e := by rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) h2
  have a3 : 2 * 2 ^ e ≤ 2 ^ κ := by rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) h3
  have a4 : 2 ^ α * 4 ≤ 2 ^ κ := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h4
    rwa [pow_add] at this
  { toFrame := Formalism.HC.cyclicFrame e, k := 2 ^ κ, m := 2 ^ α, t := 4 * 2 ^ κ + 1
    k_even := (Nat.even_pow.2 ⟨even_two, by omega⟩)
    m_even := (Nat.even_pow.2 ⟨even_two, by omega⟩)
    t_odd := ⟨2 * 2 ^ κ, by ring⟩
    two_le_m := by omega
    m_add_three_le_k := by omega
    rank_add_five_le := by omega
    three_m_lt_t := by omega
    m_le_f := a2
    f_le_k := a3
    m_sq_le_N := by nlinarith }

theorem big_nums (R : Ranks) (Del h : ℕ) (hm : (R.m : ℝ) = P 119925) (hf : (R.f : ℝ) = P 489601) (hk : (R.k : ℝ) = P 1092000)
    (ht : R.t = 4 * R.k + 1) (hD : (Del : ℝ) = P 32000000) (hh : (h : ℝ) = P 24000000) :
    Num R (P 240000) (1 / 200) Del h ∧
    (∀ lrd, Real.log 2 ≤ lrd → lrd ≤ P 600 → RankNums (P 240000) (1 / 200) 20 R.m R.f R.k lrd Del) ∧
    P 240000 ^ ((1 : ℝ) / 200 / 100) * (R.r : ℝ) ^ 19 * (R.f : ℝ) ^ 5 * P 240000 ^ ((1 : ℝ) / 200) ≤ 2 * h := by
  have L : P 240000 ^ ((1 : ℝ) / 200) = P 1200 := twoPow_rpow_of_mul_eq (by norm_num)
  have L2 : P 240000 ^ ((1 : ℝ) / 200 / 2) = P 600 := twoPow_rpow_of_mul_eq (by norm_num)
  have L3 : P 240000 ^ ((1 : ℝ) / 200 / 3) = P 400 := twoPow_rpow_of_mul_eq (by norm_num)
  have L4 : P 240000 ^ ((1 : ℝ) / 200 / 4) = P 300 := twoPow_rpow_of_mul_eq (by norm_num)
  have locP_mono₂ : P 240000 ^ ((1 : ℝ) / 200 / 100) = P 12 := twoPow_rpow_of_mul_eq (by norm_num)
  have q1 : (2 : ℝ) = P 1 := by rw [charpoly_eq_of_isIso]; norm_num
  have q2 : (4 : ℝ) = P 2 := by rw [charpoly_eq_of_isIso]; norm_num
  have hh2 : P 1200 / 2 = P 1199 := by
    rw [div_eq_iff (by norm_num), q1, twoPow_mul_twoPow]
  have big : ∀ n, 27 ≤ n → (100000000 : ℝ) ≤ P n := fun n hn => le_trans (by rw [charpoly_eq_of_isIso]; norm_num) (P_le hn)
  have ex : ∀ a n : ℕ, 27 ≤ n → a ≤ 100000000 → P a ≤ Real.exp (P n) := fun a n hn ha =>
    twoPow_le_exp (le_trans (by exact_mod_cast ha) (big n hn))
  have lg : ∀ a n : ℕ, 27 ≤ n → a ≤ 100000000 → Real.log (P a) ≤ P n := fun a n hn ha =>
    (log_le_of_le_P (twoPow_pos a) le_rfl).trans (le_trans (by exact_mod_cast ha) (big n hn))
  refine ⟨⟨?_, ?_, one_le_P _, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun lrd l1 l2 => ⟨?_, ?_, ?_, ?_, ?_, l1, ?_, ?_, ?_⟩, ?_⟩
  · have := one_le_P 32000000
    rw [← hD] at this; exact_mod_cast this
  · have h1 : 4 * (R.k : ℝ) ≤ h := by rw [hk, hh, q2, twoPow_mul_twoPow]; exact P_le (by norm_num)
    have h2 : 4 * R.k ≤ h := by exact_mod_cast h1
    have := R.m_add_three_le_k
    omega
  · rw [L, L3, hh2]; exact P_le (by norm_num)
  · rw [bx, L, twoPow_rpow_of_mul_eq (n := 1320000) (by norm_num), q2, twoPow_mul_twoPow]; exact ex _ _ (by norm_num) (by norm_num)
  · rw [L, hh2, hk, q1, twoPow_mul_twoPow, twoPow_mul_twoPow]; exact ex _ _ (by norm_num) (by norm_num)
  · rw [L, hh2, hm, hh, q1, twoPow_mul_twoPow, twoPow_mul_twoPow]; exact ex _ _ (by norm_num) (by norm_num)
  · rw [L, hh2, hk, hD, q2, twoPow_mul_twoPow, twoPow_mul_twoPow]; exact ex _ _ (by norm_num) (by norm_num)
  · rw [L4, hm, hh, q1, twoPow_mul_twoPow, twoPow_mul_twoPow]; exact lg _ _ (by norm_num) (by norm_num)
  · rw [hm]; exact twoPow_rpow_le (by norm_num)
  · rw [hm, hf, twoPow_pow]; exact P_le (by norm_num)
  · rw [hk, hf]; exact P_le (by norm_num)
  · rw [L2, L, hm, hf, hk, twoPow_pow, twoPow_mul_twoPow, twoPow_mul_twoPow, twoPow_mul_twoPow]; exact P_le (by norm_num)
  · rw [hk]; exact twoPow_le_rpow (by norm_num)
  · rw [L2]; exact l2
  · rw [L, hk, hf, hD, twoPow_mul_twoPow, twoPow_mul_twoPow]; exact twoPow_rpow_le (by norm_num)
  · rw [L2, hD]; exact lg _ _ (by norm_num) (by norm_num)
  · have hr : (R.r : ℝ) ≤ P 1092001 := by
      have h1 : R.r ≤ 2 * R.k := by have := R.m_add_three_le_k; unfold Ranks.r; omega
      have h2 : (R.r : ℝ) ≤ 2 * R.k := by exact_mod_cast h1
      rwa [hk, q1, twoPow_mul_twoPow] at h2
    have hr19 : (R.r : ℝ) ^ 19 ≤ P 1092001 ^ 19 := pow_le_pow_left₀ (by positivity) hr 19
    rw [locP_mono₂, L, hf, hh]
    have := twoPow_pos 12; have := twoPow_pos 489601; have := twoPow_pos 1200
    calc _ ≤ P 12 * P 1092001 ^ 19 * P 489601 ^ 5 * P 1200 := by gcongr
      _ ≤ _ := by rw [twoPow_pow, twoPow_pow, twoPow_mul_twoPow, twoPow_mul_twoPow, twoPow_mul_twoPow, q1, twoPow_mul_twoPow]; exact P_le (by norm_num)

theorem big_ranks : ∃ (R : Ranks) (Del h : ℕ), (R.m : ℝ) = P 119925 ∧ (R.f : ℝ) = P 489601 ∧ (R.k : ℝ) = P 1092000 ∧
    R.t = 4 * R.k + 1 ∧ (Del : ℝ) = P 32000000 ∧ (h : ℝ) = P 24000000 := by
  have key : ∀ (α e κ a b : ℕ) (h1 : 1 ≤ α) (h2 : α ≤ e + 1) (h3 : e + 1 ≤ κ) (h4 : α + 2 ≤ κ),
      ∃ (R : Ranks) (Del h : ℕ), (R.m : ℝ) = P α ∧ (R.f : ℝ) = P (e + 1) ∧ (R.k : ℝ) = P κ ∧
        R.t = 4 * R.k + 1 ∧ (Del : ℝ) = P a ∧ (h : ℝ) = P b := fun α e κ a b h1 h2 h3 h4 =>
    ⟨Rk α e κ h1 h2 h3 h4, 2 ^ a, 2 ^ b, natCast_two_pow _, by rw [← natCast_two_pow, pow_succ']; rfl, natCast_two_pow _, rfl, natCast_two_pow _, natCast_two_pow _⟩
  exact key 119925 489600 1092000 32000000 24000000 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem big_thresh (R : Ranks) (Del h : ℕ) (hm : (R.m : ℝ) = P 119925) (hf : (R.f : ℝ) = P 489601) (hk : (R.k : ℝ) = P 1092000)
    (ht : R.t = 4 * R.k + 1) (hD : (Del : ℝ) = P 32000000) (hh : (h : ℝ) = P 24000000) {v d : ℝ}
    (hv : v ≤ Real.exp (P 600)) (hd : 2 * P 1320000 < d) :
    ThreshNums (P 240000) (1 / 200) R.f R.k (R.N R.m) (4 * (R.k : ℝ) * Del) (2 * (R.m : ℝ) * h) v d := by
  have L : P 240000 ^ ((1 : ℝ) / 200) = P 1200 := twoPow_rpow_of_mul_eq (by norm_num)
  have L3 : P 240000 ^ ((1 : ℝ) / 200 / 3) = P 400 := twoPow_rpow_of_mul_eq (by norm_num)
  have Y : P 240000 ^ ((11 : ℝ) / 2) = P 1320000 := twoPow_rpow_of_mul_eq (by norm_num)
  have q1 : (2 : ℝ) = P 1 := by rw [charpoly_eq_of_isIso]; norm_num
  have q2 : (4 : ℝ) = P 2 := by rw [charpoly_eq_of_isIso]; norm_num
  have big : ∀ n, 27 ≤ n → (100000000 : ℝ) ≤ P n := fun n hn => le_trans (by rw [charpoly_eq_of_isIso]; norm_num) (P_le hn)
  have ex : ∀ a n : ℕ, 27 ≤ n → a ≤ 100000000 → P a ≤ Real.exp (P n) := fun a n hn ha =>
    twoPow_le_exp (le_trans (by exact_mod_cast ha) (big n hn))
  have dbl : ∀ n, n < 1200 → Real.exp (P n) * Real.exp (P n) ≤ Real.exp (P 1200) := fun n hn => by
    rw [← Real.exp_add, ← two_mul, q1, twoPow_mul_twoPow]; exact Real.exp_le_exp.2 (P_le (by omega))
  have four : ∀ n, 4 * P n = P (n + 2) := fun n => by rw [q2, twoPow_mul_twoPow, add_comm]
  have hN : (R.N R.m : ℝ) ≤ P 1211928 := by
    have h1 : R.N R.m ≤ 8 * (R.m * R.k) := by
      have := R.two_le_m; have := R.m_add_three_le_k
      unfold Ranks.N; rw [ht]; nlinarith
    have h2 : (R.N R.m : ℝ) ≤ 8 * (R.m * R.k) := by exact_mod_cast h1
    rwa [hm, hk, show (8 : ℝ) = P 3 by rw [charpoly_eq_of_isIso]; norm_num, twoPow_mul_twoPow, twoPow_mul_twoPow] at h2
  have hN0 : (0 : ℝ) ≤ R.N R.m := by positivity
  have hS : 4 * (R.k : ℝ) * Del = P 33092002 := by rw [hk, hD, q2, twoPow_mul_twoPow, twoPow_mul_twoPow]
  have he : 2 * (R.m : ℝ) * h = P 24119926 := by rw [hm, hh, q1, twoPow_mul_twoPow, twoPow_mul_twoPow]
  have hfN : (R.f : ℝ) * (R.N R.m : ℝ) ^ 2 ≤ P 33092002 := by
    have := twoPow_pos 489601
    calc _ ≤ P 489601 * P 1211928 ^ 2 := by rw [hf]; gcongr
      _ ≤ _ := by rw [twoPow_pow, twoPow_mul_twoPow]; exact P_le (by norm_num)
  obtain ⟨a1, a2⟩ := a_thresholds (x := P 240000) (eps := 1 / 200) (v := v)
    (by rw [bx, L, Y]; exact ex _ _ (by norm_num) (by norm_num))
    (by
      rw [bx, L, Y]
      refine le_trans ?_ (dbl 600 (by norm_num))
      calc _ ≤ P 1320000 * Real.exp (P 600) := mul_le_mul_of_nonneg_left hv (twoPow_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_right (ex _ _ (by norm_num) (by norm_num)) (Real.exp_pos _).le)
  refine ⟨lt_of_lt_of_le (by rw [← q1]; norm_num) (P_le (show 1 ≤ 240000 by norm_num)), a1, a2, ?_, ?_, by rwa [Y], ?_⟩
  · rw [L3, Y, hk]
    have := twoPow_pos 1092000; have := twoPow_pos 1320000
    calc _ ≤ P 1092000 * P 1211928 * P 1320000 := by gcongr
      _ ≤ _ := by rw [twoPow_mul_twoPow, twoPow_mul_twoPow]; exact ex _ _ (by norm_num) (by norm_num)
  · rw [bx, L, Y, hS, he]
    have h1 : P 24119926 ≤ P 33092002 := P_le (by norm_num)
    have h2 : P 33092002 + P 24119926 + (R.f : ℝ) * (R.N R.m : ℝ) ^ 2 ≤ P (33092002 + 2) := by
      rw [← four 33092002]; linarith [twoPow_pos 33092002]
    have := twoPow_pos 33092002; have := twoPow_pos 24119926; have := twoPow_pos 1320000
    calc _ ≤ P (33092002 + 2) ^ 2 * P 1320000 ^ 3 := by gcongr
      _ ≤ _ := by rw [twoPow_pow, twoPow_pow, twoPow_mul_twoPow]; exact ex _ _ (by norm_num) (by norm_num)
  · rw [bx, L, L3, hS, four]
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le) (dbl 400 (by norm_num))
    have h1 : P 1211928 ≤ P (33092002 + 2) := P_le (by norm_num)
    have h2 : (R.N R.m : ℝ) + P (33092002 + 2) + 1 ≤ P (33092002 + 2 + 2) := by
      rw [← four (33092002 + 2)]; linarith [one_le_P (33092002 + 2)]
    calc _ ≤ P (33092002 + 2 + 2) * P 240000 := mul_le_mul_of_nonneg_right h2 (twoPow_pos _).le
      _ ≤ _ := by rw [twoPow_mul_twoPow]; exact ex _ _ (by norm_num) (by norm_num)

theorem big_witness (D0 : D7) (R : Ranks) (Del h : ℕ) (hm : (R.m : ℝ) = P 119925) (hf : (R.f : ℝ) = P 489601)
    (hk : (R.k : ℝ) = P 1092000) (ht : R.t = 4 * R.k + 1) (hD : (Del : ℝ) = P 32000000) (hh : (h : ℝ) = P 24000000)
    (H : Host R) (A : Arith H) (Cg CT CG : ℝ) (hC : 0 < CG) (J : ℕ) (hJ : TopsCoset H J)
    (r1 : 2 ≤ H.rdE) (r2 : Real.log H.rdE ≤ P 600) (hd : 2 * P 1320000 < H.d)
    (hs : SplitLab H (P 240000) (1 / 200))
    (hg : ∀ i, ((R.k : ℝ) * bx (P 240000) (1 / 200)) ^ 8 ≤ (H.g i : ℝ) ∧ (H.g i : ℝ) ≤ bx (P 240000) (1 / 200) ^ Cg)
    (hT : bx (P 240000) (1 / 200) ^ ((1 / 2 : ℝ) * (R.m : ℝ)) ≤ (A.T : ℝ) ∧
      (A.T : ℝ) ≤ bx (P 240000) (1 / 200) ^ (CT * (R.m : ℝ))) :
    ∃ D : D7, D.R = R ∧ HEq D.host H ∧ Glob D (P 240000) (1 / 200) 20 Cg CT ∧ Nodes D (P 240000) (1 / 200) ∧
      OneScaleDatum D (P 240000) (1 / 200) (2 * (R.m : ℝ) * h) J ∧ LiveLabels D (P 240000) (1 / 200) CG := by
  obtain ⟨N, n2, n3⟩ := big_nums R Del h hm hf hk ht hD hh
  have hG := gam_gt R hC (Real.rpow_pos_of_pos (twoPow_pos 240000) (1 / 200))
  have rn := n2 _ (Real.log_le_log (by norm_num) r1) r2
  let D := rcd H A (LocalGap.localGapOfRecord D0 H) N _ hG
  obtain ⟨s1, s2⟩ := rcd_rows H A (LocalGap.localGapOfRecord D0 H) N _ hG
  obtain ⟨-, -, g, c, f⟩ := place_rows D N rfl s1 s2
  obtain ⟨o, n, ev, di⟩ := rcd_datum H A (LocalGap.localGapOfRecord D0 H) N _ hG hJ (two_m_le_two_pow H rn.mf)
  have e : ((D.s.Del : ℚ) : ℝ) = (Del : ℝ) := by
    show (((Del : ℕ) : ℚ) : ℝ) = _
    push_cast; rfl
  refine ⟨D, rfl, HEq.rfl, ⟨?_, r1, hg, fun _ => hT, fun τ j hj => ?_, c, f⟩, n, ⟨o, hJ, ev, ?_, di⟩,
    ⟨hs, hC, fun u => Real.log_exp _⟩⟩
  · rw [e]; exact rn
  · rw [g τ j hj]; exact n3
  · unfold Thresholds
    rw [e]
    refine big_thresh R Del h hm hf hk ht hD hh ?_ hd
    have := (Real.log_le_iff_le_exp (by linarith)).1 r2
    show H.rdE / 2 ≤ _
    linarith

end GlobalTheory.Diag.PG.Wit

end
