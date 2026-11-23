import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptBlocksOfSLine
set_option maxHeartbeats 4000000

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

set_option maxHeartbeats 4000000 in
theorem pairS_at {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X) :
    PairSAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hI hc j rz ry hd A hA1 hA2 mu lam hP hK i hi
  have hs := hstd X hD hI hc
  have hk5 := hs.k5
  have hk : (0 : ℝ) < X.k := by linarith
  have hkk : X.k = (X.m : ℝ) + 1 := rfl
  have hLK := hs.LaK
  have hN1 : (1 : ℝ) ≤ X.N1 := by exact_mod_cast hs.N1pos
  have hLa1 := hs.La1
  have hLa0 : (0 : ℝ) ≤ X.La C0 := le_trans zero_le_one hLa1
  have hde6 := hs.de6
  have hp0 : (0 : ℝ) < X.p := by have := hs.p5; exact_mod_cast (show 0 < X.p by omega)
  have hp2pos : (0 : ℝ) < (X.p : ℝ) ^ 2 := by positivity
  have hp25 : (25 : ℝ) ≤ (X.p : ℝ) ^ 2 := by
    have : (5 : ℝ) ≤ X.p := by exact_mod_cast hs.p5
    nlinarith
  have hde0 : 0 ≤ X.de C0 Cde := le_trans (by positivity) hLK
  set A0 : ℝ := ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) with hA0
  set Aa : Fin (segS X.TT j) → ℝ := fun l => (clA C0 CE1 CE2 X j rz ry l : ℝ) with hAa

  have hAl : ∀ l : Fin (segS X.TT j), l.val ≤ i.val → Aa l ≤ A0 := by
    intro l hl
    have h := (coarse_degree_alternative le_rfl hs j (digitBlock rz ry) hd l).1 (lt_of_le_of_lt hl hi)
    have h0 : (0 : ℝ) ≤ (clA C0 CE1 CE2 X j rz ry l : ℝ) := Nat.cast_nonneg _
    show (clA C0 CE1 CE2 X j rz ry l : ℝ) ≤ _
    nlinarith
  have hAnn : ∀ l : Fin (segS X.TT j), (0 : ℝ) ≤ Aa l := fun l => by
    show (0 : ℝ) ≤ (clA C0 CE1 CE2 X j rz ry l : ℝ); exact Nat.cast_nonneg _
  have hA00 : (0 : ℝ) ≤ A0 := le_trans (hAnn i) (hAl i le_rfl)
  have h4p : 4 / (X.p : ℝ) ^ 2 ≤ 1 := by rw [div_le_one hp2pos]; linarith

  have hsum : ∀ l : Fin (segS X.TT j), (∑ x : Fin (segS X.TT j), if x.val < l.val then Aa x else 0) ≤ 4 * Aa l / (X.p : ℝ) ^ 2 :=
    fun l => coarse_degree_prefix_sum hs le_rfl j rz ry hd l

  have hkap : ∀ l : Fin (segS X.TT j), ((mu ⟨2 * l.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) ≤ 4 * Aa l / (X.p : ℝ) ^ 2 := by
    intro l
    have h1 := pf_prev_le hP.1 l.val (by omega)
    have h2 : ((∑ x : Fin (segS X.TT j), if x.val < l.val then pairW mu x.val else 0 : ℤ) : ℝ) ≤
        ∑ x : Fin (segS X.TT j), if x.val < l.val then Aa x else 0 := by
      push_cast
      refine Finset.sum_le_sum fun x _ => ?_
      split_ifs
      · obtain ⟨-, -, -, hw, -, -, -, -⟩ := pair_top hP.1 x
        show _ ≤ ((clA C0 CE1 CE2 X j rz ry x : ℕ) : ℝ)
        exact_mod_cast hw
      · exact le_rfl
    have h1' : ((mu ⟨2 * l.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) ≤
        ((∑ x : Fin (segS X.TT j), if x.val < l.val then pairW mu x.val else 0 : ℤ) : ℝ) := by exact_mod_cast h1
    linarith [hsum l]
  have hrho : ∀ l : Fin (segS X.TT j), ((pairRho mu l.val : ℤ) : ℝ) ≤ Aa l + 4 * Aa l / (X.p : ℝ) ^ 2 := by
    intro l
    have h1 := pf_rho_le hP.1 l
    obtain ⟨-, -, -, hw, -, -, -, -⟩ := pair_top hP.1 l
    have h1' : ((pairRho mu l.val : ℤ) : ℝ) ≤ ((mu ⟨2 * l.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) +
        ((pairW mu l.val : ℤ) : ℝ) := by exact_mod_cast h1
    have hw' : ((pairW mu l.val : ℤ) : ℝ) ≤ Aa l := by
      show _ ≤ ((clA C0 CE1 CE2 X j rz ry l : ℕ) : ℝ)
      exact_mod_cast hw
    linarith [hkap l]

  have hcup : ∀ l : Fin (segS X.TT j), l.val ≤ i.val → ((pairC mu l.val : ℤ) : ℝ) ≤ 2 * A0 := by
    intro l hl
    have h1 := pairC_le_sum hP.1 l
    have hA : (A : ℝ) ≤ A0 := hA2
    have h3 : 4 * Aa l / (X.p : ℝ) ^ 2 ≤ Aa l := by
      have e : 4 * Aa l / (X.p : ℝ) ^ 2 = Aa l * (4 / (X.p : ℝ) ^ 2) := by ring
      rw [e]; nlinarith [hAnn l]
    have := hsum l
    have := hAl l hl
    simp only [hAa] at *
    linarith

  have hkept : ∀ l : Fin (segS X.TT j), ((pairO mu (clA C0 CE1 CE2 X j rz ry) l : ℤ) : ℝ) - ((pairRho mu l.val : ℤ) : ℝ) +
      4 * (Aa l + X.m) / (X.p : ℝ) ^ 2 ≤ X.La C0 * max ((pairC mu l.val : ℤ) : ℝ) (Aa l) / X.k := by
    intro l
    have h := (hK l).1
    rw [hkk]
    push_cast at h ⊢
    exact h

  set δ : ℝ := 3 * A0 * (4 / (X.p : ℝ) ^ 2 + X.La C0 / X.k) with hδ
  have hlow : ∀ n : ℕ, ∀ hn : n ≤ i.val, (A : ℝ) - n * δ ≤ ((pairC mu n : ℤ) : ℝ) := by
    intro n
    induction n with
    | zero => intro _; rw [pairC_zero hP.1]; simp
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      set l : Fin (segS X.TT j) := ⟨n, by omega⟩ with hl
      have eC : pairC mu (n + 1) = pairC mu n + ((clA C0 CE1 CE2 X j rz ry l : ℕ) : ℤ) -
          pairO mu (clA C0 CE1 CE2 X j rz ry) l := by unfold pairO; ring
      have hk1 := hkept l
      have hr := hrho l
      have hcl := hcup l (by show n ≤ i.val; omega)
      have hal := hAl l (by show n ≤ i.val; omega)
      have hmax : max ((pairC mu n : ℤ) : ℝ) (Aa l) ≤ 2 * A0 := max_le hcl (by linarith)
      have hLk : 0 ≤ X.La C0 / X.k := div_nonneg hLa0 hk.le
      have hm0 : (0 : ℝ) ≤ 4 * (Aa l + X.m) / (X.p : ℝ) ^ 2 := by
        have := hAnn l; positivity
      have hOl : ((pairO mu (clA C0 CE1 CE2 X j rz ry) l : ℤ) : ℝ) ≤ Aa l + 4 * Aa l / (X.p : ℝ) ^ 2 +
          X.La C0 * (2 * A0) / X.k := by
        have : X.La C0 * max ((pairC mu n : ℤ) : ℝ) (Aa l) / X.k ≤ X.La C0 * (2 * A0) / X.k := by
          apply div_le_div_of_nonneg_right _ hk.le
          exact mul_le_mul_of_nonneg_left hmax hLa0
        simp only [hl] at hk1 hr ⊢
        linarith
      have hd1 : 4 * Aa l / (X.p : ℝ) ^ 2 + X.La C0 * (2 * A0) / X.k ≤ δ := by
        have e1 : 4 * Aa l / (X.p : ℝ) ^ 2 ≤ 3 * A0 * (4 / (X.p : ℝ) ^ 2) := by
          have e : 4 * Aa l / (X.p : ℝ) ^ 2 = Aa l * (4 / (X.p : ℝ) ^ 2) := by ring
          rw [e]
          have : (0 : ℝ) ≤ 4 / (X.p : ℝ) ^ 2 := by positivity
          nlinarith
        have e2 : X.La C0 * (2 * A0) / X.k ≤ 3 * A0 * (X.La C0 / X.k) := by
          have e : X.La C0 * (2 * A0) / X.k = 2 * A0 * (X.La C0 / X.k) := by ring
          rw [e]; nlinarith
        rw [hδ]; linarith
      rw [eC]
      push_cast
      simp only [hl] at hOl hd1
      linarith

  have hci_low := hlow i.val le_rfl
  have hsN : (i.val : ℝ) ≤ X.N1 := by
    have := (hs.segB j).2
    have : i.val ≤ X.N1 := by omega
    exact_mod_cast this
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hAlo : A0 * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) := hA1
  have hdich := (coarse_degree_alternative le_rfl hs j (digitBlock rz ry) hd i).1 hi

  have sq_level_le_degree : 2 * (X.N1 : ℝ) + 3 ≤ X.k := hs.N1k
  have hkp : X.k ^ 2 ≤ (X.p : ℝ) := by
    have hY2 : (1 : ℝ) ≤ X.Y ^ 2 := one_le_pow₀ hs.Y1
    nlinarith [hs.pk, mul_le_mul_of_nonneg_left hY2 (sq_nonneg X.k)]
  have hde40 : 40 * X.N1 * X.La C0 / X.k ≤ X.de C0 Cde := hLK
  have hq1 : 4 * X.N1 * X.La C0 / X.k ≤ X.de C0 Cde / 10 := by
    have e : 4 * X.N1 * X.La C0 / X.k = (40 * X.N1 * X.La C0 / X.k) / 10 := by ring
    rw [e]; linarith
  have hq2 : 12 * X.N1 / (X.p : ℝ) ^ 2 ≤ X.de C0 Cde / 80 := by
    have hk4 : X.k ^ 4 ≤ (X.p : ℝ) ^ 2 := by
      calc X.k ^ 4 = (X.k ^ 2) ^ 2 := by ring
        _ ≤ (X.p : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hkp 2
    have h40 : 40 / X.k ≤ X.de C0 Cde := by
      refine le_trans ?_ hde40
      rw [div_le_div_iff_of_pos_right hk]
      have h1 : 1 ≤ (X.N1 : ℝ) * X.La C0 := one_le_mul_of_one_le_of_one_le hN1 hLa1
      have e : 40 * (X.N1 : ℝ) * X.La C0 = 40 * ((X.N1 : ℝ) * X.La C0) := by ring
      rw [e]; linarith
    have hN1le : (X.N1 : ℝ) ≤ X.k := by linarith
    have h1 : 12 * X.N1 / (X.p : ℝ) ^ 2 ≤ 12 * X.k / X.k ^ 4 := by
      apply div_le_div₀ (by positivity) (by linarith) (by positivity) hk4
    have h2 : 12 * X.k / X.k ^ 4 ≤ (40 / X.k) / 80 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hk3 : (5 : ℝ) ^ 3 ≤ X.k ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hk5 3
        exact this
      nlinarith [mul_le_mul_of_nonneg_left hk3 (by positivity : (0:ℝ) ≤ X.k ^ 2)]
    have h3 : (40 / X.k) / 80 ≤ X.de C0 Cde / 80 := by linarith
    linarith
  have hci_ge : Aa i ≤ ((pairC mu i.val : ℤ) : ℝ) := by

    have h1 : (i.val : ℝ) * δ ≤ X.N1 * δ := mul_le_mul_of_nonneg_right hsN hδ0
    have hexp : X.N1 * δ = A0 * (12 * X.N1 / (X.p : ℝ) ^ 2 + 3 * X.N1 * X.La C0 / X.k) := by
      rw [hδ]; ring
    have hlow2 : A0 * (1 - (4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2)) ≤ ((pairC mu i.val : ℤ) : ℝ) := by
      have e : A0 * (1 - X.N1 * X.La C0 / X.k) = A0 - A0 * (X.N1 * X.La C0 / X.k) := by ring
      have e2 : A0 * (1 - (4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2)) =
          A0 - A0 * (X.N1 * X.La C0 / X.k) - A0 * (12 * X.N1 / (X.p : ℝ) ^ 2 + 3 * X.N1 * X.La C0 / X.k) := by ring
      rw [e2]
      linarith
    have hε : (4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2) * (1 + X.de C0 Cde) ≤ X.de C0 Cde := by
      have hsum' : 4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2 ≤ X.de C0 Cde * (9 / 80) := by linarith
      have hε0 : 0 ≤ 4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2 := by positivity
      nlinarith

    have key : Aa i * (1 + X.de C0 Cde) ≤ A0 := le_of_lt hdich
    set ε : ℝ := 4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2 with hεd
    have hε1 : 0 ≤ 1 - ε := by linarith
    have hprod : 1 ≤ (1 + X.de C0 Cde) * (1 - ε) := by nlinarith
    have g1 : Aa i ≤ Aa i * ((1 + X.de C0 Cde) * (1 - ε)) := le_mul_of_one_le_right (hAnn i) hprod
    have g2 : Aa i * ((1 + X.de C0 Cde) * (1 - ε)) ≤ A0 * (1 - ε) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right key hε1
    linarith
  have hmaxc : max ((pairC mu i.val : ℤ) : ℝ) (Aa i) = ((pairC mu i.val : ℤ) : ℝ) := max_eq_left hci_ge
  have hk1 := hkept i
  rw [hmaxc] at hk1
  have hm0 : (0 : ℝ) ≤ 4 * (Aa i + X.m) / (X.p : ℝ) ^ 2 := by have := hAnn i; positivity
  have hr := hrho i
  refine ⟨?_, ?_⟩
  · have e : Aa i * (1 + 4 / (X.p : ℝ) ^ 2) = Aa i + 4 * Aa i / (X.p : ℝ) ^ 2 := by ring
    show _ ≤ Aa i * (1 + 4 / (X.p : ℝ) ^ 2) + X.La C0 * ((pairC mu i.val : ℤ) : ℝ) / X.k
    rw [e]
    linarith
  ·
    have hu := pf_u_ge hP.1 i
    have hu' : ((pairSg mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) -
        ((mu ⟨2 * i.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) ≤
        ((pairO mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) - ((pairRho mu i.val : ℤ) : ℝ) := by exact_mod_cast hu
    have hkp' := hkap i
    have h4 : 4 * Aa i / (X.p : ℝ) ^ 2 ≤ 4 * (Aa i + X.m) / (X.p : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ hp2pos.le
      have : (0 : ℝ) ≤ X.m := Nat.cast_nonneg _
      linarith
    have hc2 := hcup i le_rfl
    have hfin : X.La C0 * ((pairC mu i.val : ℤ) : ℝ) / X.k ≤ 2 * X.La C0 * A0 / X.k := by
      apply div_le_div_of_nonneg_right _ hk.le
      nlinarith
    linarith

theorem restPairS : RestPairS :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      pairS_at fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc

theorem kept_blocks_holds : KeptBlocksBeyondThreshold := kept_blocks_of_S_line restPairS

end Formalism.MainNotions.ColumnSystems.Pf
