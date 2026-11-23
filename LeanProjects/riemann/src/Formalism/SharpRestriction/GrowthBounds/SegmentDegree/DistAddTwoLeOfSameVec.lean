import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FourHundredSixteenLeA
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TypicalPathOrdersSmall

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.TE

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace Formalism.MainNotions.SelectionLemmas.Pf.T

section Asm

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

omit [NeZero r] in
theorem letters_eq_image (F : Frames n' r) (j : ℤ) : F.letters j = Finset.univ.image (segE F j) := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, ?_⟩
    simp [segE]
  · intro hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ((F.letters j).orderIsoOfFin rfl i).2

theorem dist_cast {F : Frames n' r} {j x : ℤ} (hx : x ∈ F.letters j) : (F.dist j x : ℤ) = F.fr j (r - 1) - x := by
  have hx' := (Finset.mem_filter.mp hx).1
  rw [Finset.mem_Icc] at hx'
  show (((F.fr j (r - 1) - x).toNat : ℕ) : ℤ) = F.fr j (r - 1) - x
  exact Int.toNat_of_nonneg (by omega)

theorem dist_lt {F : Frames n' r} {j : ℤ} {i i' : Fin (segN F j)} (h : i < i') :
    F.dist j (segE F j i') + 1 ≤ F.dist j (segE F j i) := by
  have hm : segE F j i < segE F j i' := by
    unfold segE
    exact_mod_cast ((F.letters j).orderIsoOfFin rfl).strictMono h
  have hmem : ∀ k : Fin (segN F j), segE F j k ∈ F.letters j := fun k => by
    unfold segE
    exact ((F.letters j).orderIsoOfFin rfl k).2
  have h1 := dist_cast (hmem i)
  have h2 := dist_cast (hmem i')
  omega

theorem dist_add_two_le_of_same_vec {F : Frames n' r} {j : ℤ} {i i' : Fin (segN F j)} (h : i < i')
    (hv : (segLL F j).vec i = (segLL F j).vec i') : F.dist j (segE F j i') + 2 ≤ F.dist j (segE F j i) := by
  have hm : segE F j i < segE F j i' := by
    unfold segE
    exact_mod_cast ((F.letters j).orderIsoOfFin rfl).strictMono h
  have hmem : ∀ k : Fin (segN F j), segE F j k ∈ F.letters j := fun k => by
    unfold segE
    exact ((F.letters j).orderIsoOfFin rfl k).2
  have h1 := dist_cast (hmem i)
  have h2 := dist_cast (hmem i')
  have hv' : decide (Even (segE F j i)) = decide (Even (segE F j i')) := hv
  rw [decide_eq_decide] at hv'
  have h3 : segE F j i + 1 ≠ segE F j i' := by
    intro he
    rw [← he, Int.even_add_one] at hv'
    tauto
  omega

theorem beS_eq (hV : X.F.Valid X.L₁ X.N₁) (j : ℤ) (b' : ℤ → ℕ) :
    X.beS p K j b' = beA (segN X.F j - r) (fun i => X.Bdeg p K j b' (segE X.F j i)) := by
  unfold Dat.beS beA
  rw [← Finset.sum_filter, letters_eq_image, Finset.filter_image, Finset.sum_image]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp [dict_early hV]
  · intro a _ b _ hab
    unfold segE at hab
    exact ((X.F.letters j).orderIsoOfFin rfl).injective (Subtype.ext hab)

omit [NeZero n'] [NeZero r] [NeZero K] in
theorem prod_fin_lt (N r : ℕ) (hr : r ≤ N) (h : ℕ → ℝ) :
    ∏ i : Fin N, (if i.val < r then h i.val else 1) = ∏ i : Fin r, h i.val := by
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < r then h i else 1) N,
    Fin.prod_univ_eq_prod_range h r, Finset.prod_ite, Finset.prod_const_one, mul_one]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem final_num (hX : X.Hyp p K) (hLa : 1088 ≤ X.CLa) (hk : 1088 ≤ X.Ck) (N : ℕ) (hN : N ≤ X.Ns) :
    Real.exp (11 * (N : ℝ) ^ 2 * ell0 N X.a - min X.La ((r + K : ℕ) : ℝ) / 32) ≤ 1 / X.a ^ (X.Ns ^ 2) := by
  have ha := four_hundred_sixteen_le_a hX
  have hab := a_big hX
  have hL := log_a_ge hX
  have hNs : (N : ℝ) ≤ X.Ns := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hapos : 0 < X.a := by linarith
  have h1 : 1 + 2 * X.a * (N : ℝ) ≤ X.a ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hNs hapos.le, mul_le_mul_of_nonneg_left hab hapos.le,
      mul_le_mul ha ha (by norm_num) hapos.le]
  have hpos1 : 0 < 1 + 2 * X.a * (N : ℝ) := by
    have := mul_nonneg hapos.le hN0
    linarith
  have hl0 : ell0 N X.a ≤ 2 * Real.log X.a := by
    unfold ell0
    have e : Real.log (X.a ^ 2) = 2 * Real.log X.a := by
      rw [Real.log_pow]
      norm_num
    rw [← e]
    exact Real.log_le_log hpos1 h1
  have hl0nn : 0 ≤ ell0 N X.a := by
    unfold ell0
    apply Real.log_nonneg
    have := mul_nonneg hapos.le hN0
    linarith
  have hS : 0 ≤ (X.Ns : ℝ) ^ 2 * Real.log X.a := mul_nonneg (sq_nonneg _) (by linarith)
  have hmin : 1088 * ((X.Ns : ℝ) ^ 2 * Real.log X.a) ≤ min X.La ((r + K : ℕ) : ℝ) := by
    apply le_min
    · show 1088 * ((X.Ns : ℝ) ^ 2 * Real.log X.a) ≤ X.CLa * (X.Ns : ℝ) ^ 2 * Real.log X.a
      nlinarith [mul_le_mul_of_nonneg_right hLa hS]
    · nlinarith [mul_le_mul_of_nonneg_right hk hS, hX.P1]
  have hN2 : (N : ℝ) ^ 2 ≤ (X.Ns : ℝ) ^ 2 := by gcongr
  have hexp : 11 * (N : ℝ) ^ 2 * ell0 N X.a - min X.La ((r + K : ℕ) : ℝ) / 32 ≤
      -((X.Ns : ℝ) ^ 2 * Real.log X.a) := by
    nlinarith [mul_le_mul hN2 hl0 hl0nn (sq_nonneg _)]
  have e2 : Real.log (X.a ^ (X.Ns ^ 2)) = (X.Ns : ℝ) ^ 2 * Real.log X.a := by
    rw [Real.log_pow]
    push_cast
    ring
  calc Real.exp (11 * (N : ℝ) ^ 2 * ell0 N X.a - min X.La ((r + K : ℕ) : ℝ) / 32)
      ≤ Real.exp (-((X.Ns : ℝ) ^ 2 * Real.log X.a)) := Real.exp_le_exp.mpr hexp
    _ = 1 / X.a ^ (X.Ns ^ 2) := by
      rw [Real.exp_neg, one_div, ← e2, Real.exp_log (pow_pos hapos _)]

theorem letter_dictionary_bounds (h41 : TopCountLowerBounds 1088) : LetterDictionaryBounds 1088 := by
  classical
  intro p n' r K _ _ _ X hX hLa hk j b hA
  have hV := hX.valid
  obtain ⟨h41a, -⟩ := h41 p n' r K X hX hLa hk
  obtain ⟨od, hod⟩ := exists_od hV j
  have hNr := r_le_segN hV j
  have h2r := two_r_le hV j
  have hNNs : segN X.F j ≤ X.Ns := hX.card j
  have Bs := basics hX
  have hN6 : (6 : ℝ) ≤ X.Ns := by exact_mod_cast six_le_Ns hX
  have ha := a_big hX
  have ha416 := four_hundred_sixteen_le_a hX
  have hlog := log_a_ge hX
  have hkb := k_big hX hk
  have hp0 : (0 : ℝ) < p := by linarith [Bs.p1]
  have ha0 : (0 : ℝ) < X.a := by linarith
  have hk5 := Bs.k5
  have hkdef : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  have hPpos : ∀ x : ℤ, (0 : ℝ) < (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := fun x => by positivity
  have hP1 : ∀ x : ℤ, (1 : ℝ) ≤ (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := fun x => one_le_pow₀ Bs.p1.le
  have Bb : ∀ i : Fin (segN X.F j), i.val < segN X.F j - r →
      (X.a' p K (posOf n' (segE X.F j i)) : ℝ) / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) -
          2 * Dat.k (r := r) K * (X.Ns : ℝ) ≤ (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ∧
        (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤
          (X.a' p K (posOf n' (segE X.F j i)) : ℝ) / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) :=
    fun i hi => Bdeg_bounds hX hk h41a j b hA _ (segE_mem X.F j i) ((dict_early hV i).2 hi)
  have cb := fun i : Fin (segN X.F j) => c_bounds hX h41a j _ (segE_mem X.F j i)

  have Bup : ∀ i : Fin (segN X.F j), i.val < segN X.F j - r →
      (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤
        2 * X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) := fun i hi =>
    le_trans (Bb i hi).2 (div_le_div_of_nonneg_right (cb i).2.2 (hPpos _).le)
  have hkN : Dat.k (r := r) K * 6 ≤ Dat.k (r := r) K * (X.Ns : ℝ) := mul_le_mul_of_nonneg_left hN6 (by linarith)
  have hk2 : Dat.k (r := r) K * (X.Ns : ℝ) * 5 ≤ Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
    have : 0 ≤ Dat.k (r := r) K * (X.Ns : ℝ) := by positivity
    nlinarith

  have cge : ∀ i : Fin (segN X.F j), 36 * (Dat.k (r := r) K * (X.Ns : ℝ)) ≤
      (X.a' p K (posOf n' (segE X.F j i)) : ℝ) / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) := by
    intro i
    rw [le_div_iff₀ (hPpos _)]
    refine le_trans ?_ (cb i).1
    refine mul_le_mul_of_nonneg_right ?_ (hPpos _).le
    have h1 : 0 ≤ Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by positivity
    nlinarith [Bs.Y1]
  have H : HypT (segN X.F j) (segN X.F j - r) r K (segLL X.F j)
      (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
      (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.a X.La p := by
    refine
      { hN := by omega
        r1 := by have := hX.r2; omega
        a3 := by linarith
        p13 := hX.p13
        H1 := ?_
        H2 := ?_
        vec_true_of_early := fun i hi => (comb_vec X.F j i).2 (comb_W_even X.F j hV _ (segE_mem X.F j i) ((dict_w hV i).2 hi))
        vec_true_of_late := fun i hi => (comb_vec X.F j i).2 (dict_lateV hV i hi)
        two_r_le_n0 := h2r
        N_add_r_le_K := by have := hX.NsK; omega
        H4 := ?_
        N_le_a := ?_
        od_lt := fun i hi => (hod i hi).2.1
        od_vec := fun i hi => (hod i hi).2.2.1
        od_card := fun i hi => (hod i hi).2.2.2
        bb_pos := fun i _ => div_pos ha0 (hPpos _)
        bb_le := ?_
        La_pos := ?_ }
    · intro i hi
      have h1 := Bb i hi
      have h2 := cge i
      refine ⟨?_, ?_⟩
      · show ((r + K : ℕ) : ℝ) ≤ (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ)
        rw [← hkdef]
        nlinarith
      · show (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ 2 * X.a
        refine le_trans h1.2 (le_trans (div_le_self (Nat.cast_nonneg _) (hP1 _)) (cb i).2.2)
    · intro i i' hii hi' hv
      show (p : ℝ) ^ 2 / 5 * (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤
        (X.Bdeg p K j (X.restr j b) (segE X.F j i') : ℝ)
      have hi : i.val < segN X.F j - r := lt_trans hii hi'
      have hd := dist_add_two_le_of_same_vec hii hv
      have hPP : (p : ℝ) ^ (X.F.dist j (segE X.F j i') + X.Rj p K j) * (p : ℝ) ^ 2 ≤
          (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) := by
        rw [← pow_add]
        exact pow_le_pow_right₀ Bs.p1.le (by omega)
      set P' := (p : ℝ) ^ (X.F.dist j (segE X.F j i') + X.Rj p K j) with hP'
      have hP'0 : 0 < P' := hPpos _
      have h1 : (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ 2 * X.a / (P' * (p : ℝ) ^ 2) :=
        le_trans (Bup i hi) (div_le_div_of_nonneg_left (by linarith) (by positivity) hPP)
      have h2 : (p : ℝ) ^ 2 / 5 * (2 * X.a / (P' * (p : ℝ) ^ 2)) = 2 / 5 * (X.a / P') := by
        field_simp
      have h3 : (p : ℝ) ^ 2 / 5 * (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ 2 / 5 * (X.a / P') := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 := (Bb i' hi').1
      have h5 := cge i'
      have h6 : 9 / 10 * (X.a / P') ≤ (X.a' p K (posOf n' (segE X.F j i')) : ℝ) / P' := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (cb i').2.1 hP'0.le
      have h7 : 0 < X.a / P' := div_pos ha0 hP'0
      linarith
    · have hr3 : (r : ℝ) ≤ X.Ns := by
        have : r ≤ X.Ns := by omega
        exact_mod_cast this
      have hNR : ((segN X.F j : ℕ) : ℝ) ≤ X.Ns := by exact_mod_cast hNNs
      have hsq : (X.Ns : ℝ) ≤ (X.Ns : ℝ) ^ 2 := by nlinarith
      push_cast at hkb ⊢
      linarith
    · have hNR : ((segN X.F j : ℕ) : ℝ) ≤ X.Ns := by exact_mod_cast hNNs
      linarith
    · intro i l _ hli hl
      show (X.Bdeg p K j (X.restr j b) (segE X.F j l) : ℝ) ≤
        4 * (X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) / (p : ℝ)
      have hd := dist_lt hli
      have hPP : (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) * (p : ℝ) ≤
          (p : ℝ) ^ (X.F.dist j (segE X.F j l) + X.Rj p K j) := by
        rw [← pow_succ]
        exact pow_le_pow_right₀ Bs.p1.le (by omega)
      set P' := (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) with hP'
      have hP'0 : 0 < P' := hPpos _
      have h1 : (X.Bdeg p K j (X.restr j b) (segE X.F j l) : ℝ) ≤ 2 * X.a / (P' * (p : ℝ)) :=
        le_trans (Bup l hl) (div_le_div_of_nonneg_left (by linarith) (by positivity) hPP)
      have h2 : 4 * (X.a / P') / (p : ℝ) = 2 * (2 * X.a / (P' * (p : ℝ))) := by field_simp; ring
      rw [h2]
      have h3 : 0 ≤ 2 * X.a / (P' * (p : ℝ)) := by positivity
      linarith
    · unfold Dat.La
      have : (0 : ℝ) < X.CLa := by linarith
      have h6 : (0 : ℝ) < X.Ns := by linarith
      have : (0 : ℝ) < Real.log X.a := by linarith
      positivity
  refine ⟨segN X.F j - r, od, H, ?_, ?_, ?_, final_num hX hLa hk _ hNNs⟩
  · intro μ dd
    constructor
    · intro h
      refine ⟨h.path, fun i hi => h.degs i ((dict_early hV i).2 hi), fun i m hi hm => ?_⟩
      have hlt : i.val - (segN X.F j - r) < r := by have := i.2; omega
      have := h.head i ⟨i.val - (segN X.F j - r), hlt⟩
        ((dict_tau hV i ⟨i.val - (segN X.F j - r), hlt⟩).2 (by simp only; omega)) m hm
      rw [this, beS_eq hV]
    · intro h
      refine ⟨h.path, fun i hi => h.degs i ((dict_early hV i).1 hi), fun i i' hi m hm => ?_⟩
      have hidx := (dict_tau hV i i').1 hi
      have := h.head i m (by omega) (by omega)
      rw [this, beS_eq hV]
  · intro μ hG i hnW
    have hi : r ≤ i.val := by rw [dict_w hV] at hnW; omega
    obtain ⟨g1, g2, g3⟩ := hG i hi
    have hodn := oldest_lt_n0 H i hi
    have hoe := (hod i hi).1
    have hXi : Xi r K (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p i =
        X.La * X.a / ((p : ℝ) * Dat.k (r := r) K * (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) := by
      unfold Xi
      rw [hkdef]
      have := (hPpos (segE X.F j i)).ne'
      have hk0 : ((r + K : ℕ) : ℝ) ≠ 0 := by rw [← hkdef]; linarith
      field_simp
    refine ⟨le_trans ?_ g1, ?_, ?_⟩
    · unfold Dat.thc
      rw [← hoe]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      show _ ≤ ((X.Bdeg p K j (X.restr j b) (segE X.F j (od i)) : ℕ) : ℝ)
      unfold Dat.Bdeg
      by_cases hW : X.F.IsW j (segE X.F j (od i))
      · rw [if_pos hW, if_pos hW]
        have := Int.self_le_toNat (X.Bw p K j (segE X.F j (od i)) - (X.m0 K : ℤ))
        exact_mod_cast this
      · rw [if_neg hW, if_neg hW]
    · intro hE
      refine le_trans (g2 ((comb_vec X.F j i).2 hE)) ?_
      unfold Dat.oc
      rw [if_pos hE, hXi, ← hoe]
      have h1 := Bup (od i) hodn
      have h2 : (p : ℝ) ^ (-((X.F.dist j (segE X.F j (od i)) : ℤ) + (X.Rj p K j : ℤ))) =
          1 / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j) := by
        rw [zpow_neg, ← Nat.cast_add, zpow_natCast, one_div]
      rw [h2]
      have h3 : 4 * X.a * (1 / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j)) =
          2 * (2 * X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j)) := by ring
      rw [h3]
      have h1' : ((X.Bdeg p K j (X.restr j b) (segE X.F j (od i)) : ℕ) : ℝ) ≤
          2 * X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j) := h1
      linarith
    · intro hE
      have hv : (segLL X.F j).vec i = false := by
        cases hvv : (segLL X.F j).vec i with
        | true => exact absurd ((comb_vec X.F j i).1 hvv) hE
        | false => rfl
      refine le_trans (g3 hv) ?_
      unfold Dat.oc
      rw [if_neg hE, hXi, add_zero]
  · unfold rkA
    push_cast
    have hpt : ∀ i : Fin (segN X.F j),
        ((if i.val < segN X.F j - r then
          (Nat.choose (X.Bdeg p K j (X.restr j b) (segE X.F j i) + (r + K) - 1) (r + K - 1) : ℕ) else 1 : ℕ) : ℝ) =
        (if r ≤ i.val ∧ i.val < segN X.F j - r then
          ((Nat.choose (b (segE X.F j i) + (r + K) - 1) (r + K - 1) : ℕ) : ℝ) else 1) *
        (if i.val < r then ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1)
          (r + K - 1) : ℕ) : ℝ) else 1) := by
      intro i
      by_cases h1 : i.val < r
      · have hW := (dict_w hV i).2 h1
        rw [if_pos (by omega), if_neg (by omega), if_pos h1, one_mul]
        unfold Dat.Bdeg
        rw [if_pos hW, dict_wE hV i h1]
      · by_cases h2 : i.val < segN X.F j - r
        · have hW : ¬ X.F.IsW j (segE X.F j i) := fun h => h1 ((dict_w hV i).1 h)
          have hlate : segE X.F j i ∈ X.toLate j := by
            unfold Dat.toLate; rw [Finset.mem_filter]; exact ⟨segE_mem X.F j i, hW⟩
          rw [if_pos h2, if_pos ⟨by omega, h2⟩, if_neg h1, mul_one]
          unfold Dat.Bdeg Dat.restr
          rw [if_neg hW, if_pos hlate]
        · rw [if_neg h2, if_neg (by omega), if_neg h1]; simp
    have hL : (∏ i : Fin (segN X.F j), ((if i.val < segN X.F j - r then
          (Nat.choose (X.Bdeg p K j (X.restr j b) (segE X.F j i) + (r + K) - 1) (r + K - 1) : ℕ) else 1 : ℕ) : ℝ)) =
        (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
        (∏ i : Fin r, ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1)
          (r + K - 1) : ℕ) : ℝ)) := by
      rw [Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib,
        prod_fin_lt (segN X.F j) r hNr (fun m => ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) m) - (X.m0 K : ℤ)).toNat +
          (r + K) - 1) (r + K - 1) : ℕ) : ℝ))]
      congr 1
      rw [LLset_eq_image hV, Finset.prod_image (fun a _ b _ h => (segE_strictMono X.F j).injective h),
        Finset.prod_filter]
    exact_mod_cast hL

end Asm

end Formalism.MainNotions.SelectionLemmas.Pf.TE
