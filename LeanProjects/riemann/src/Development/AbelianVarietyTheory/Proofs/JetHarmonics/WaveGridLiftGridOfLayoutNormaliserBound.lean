import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume

namespace GlobalTheory.GridsFromLayout

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

noncomputable section

theorem cutWord_iff (P : M.Par) (l0 : ℕ) (w : List C.Letter) :
    KB.CutWord P l0 w ↔ (∀ l ∈ w, I.OnCut P.u P.u' l0 l.2) ∧ w.Pairwise (fun l l' => 2 < |l.2 - l'.2|) := by
  unfold KB.CutWord
  rw [List.pairwise_iff_get]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun l hl => ?_, fun i j hij => h2 i j hij.ne⟩
    obtain ⟨i, rfl⟩ := List.get_of_mem hl
    exact h1 i
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => h1 _ (List.get_mem _ _), fun i j hij => ?_⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact h2 i j h
    · rw [abs_sub_comm]; exact h2 j i h

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

open Finset in
private theorem two_lt_abs_sub_sub_of_five_le_of_abs_le_two {g b c : ℝ} (h : 5 ≤ |g - b|) (hc : |c| ≤ 2) :
    2 < |g - b - c| := by
  have := abs_sub_abs_le_abs_sub (g - b) c
  linarith

open Finset in
private theorem one_add_inv_pos_and_le_of_five_le_abs {x : ℝ} (hx : 5 ≤ |x|) : 0 < 1 + x⁻¹ ∧ 1 ≤ 5 / 4 * (1 + x⁻¹) := by
  have hx0 : x ≠ 0 := by intro h; rw [h, abs_zero] at hx; norm_num at hx
  have hinv : |x⁻¹| ≤ 1 / 5 := by
    rw [abs_inv, one_div]; exact inv_anti₀ (by norm_num) hx
  have := abs_le.1 hinv
  constructor <;> nlinarith [this.1, this.2]

open Finset in
private theorem exists_qw_eq_mul_pos_real_of_five_le_dist {S : Type} (q : ℂ → ℂ) (y : ℝ) :
    ∀ u : List (_root_.Formalism.FourierDecayAlt.Wd.Letter ℂ S), (∀ l ∈ u, ∃ t : ℝ, l.pt = t ∧ (l.plus = true → 5 ≤ |y - t|) ∧
      (l.plus = false → 5 ≤ |t - 1 - y|)) →
      ∃ ρ : ℝ, 0 < ρ ∧ 1 ≤ (5 / 4 : ℝ) ^ u.length * ρ ∧ _root_.Formalism.FourierDecayAlt.Wd.qw q u (y : ℂ) = q y * ρ
  | [], _ => ⟨1, one_pos, by simp, by simp [_root_.Formalism.FourierDecayAlt.Wd.qw]⟩
  | l :: w, h => by
    obtain ⟨ρ, hρ, hρ1, hρeq⟩ := exists_qw_eq_mul_pos_real_of_five_le_dist q y w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨t, ht, hplus, hminus⟩ := h l (List.mem_cons_self)
    cases hl : l.plus
    · obtain ⟨f0, f1⟩ := one_add_inv_pos_and_le_of_five_le_abs (hminus hl)
      refine ⟨ρ * (1 + (t - 1 - y)⁻¹), mul_pos hρ f0, ?_, ?_⟩
      · rw [List.length_cons, pow_succ]
        nlinarith [mul_le_mul hρ1 f1 zero_le_one (by positivity)]
      · have hz : (t : ℂ) - y - 1 ≠ 0 := by
          have : t - 1 - y ≠ 0 := by intro h0; have := hminus hl; rw [h0, abs_zero] at this; norm_num at this
          exact_mod_cast (show (t : ℝ) - y - 1 ≠ 0 by intro h1; apply this; linarith)
        have hz' : (t : ℂ) - 1 - y ≠ 0 := by
          intro h1; apply hz; linear_combination h1
        simp only [_root_.Formalism.FourierDecayAlt.Wd.qw, hl, Bool.false_eq_true, if_false, hρeq, ht]
        push_cast
        rw [show (t : ℂ) - 1 - y = (t : ℂ) - y - 1 by ring]
        field_simp
        ring
    · obtain ⟨f0, f1⟩ := one_add_inv_pos_and_le_of_five_le_abs (hplus hl)
      refine ⟨ρ * (1 + (y - t)⁻¹), mul_pos hρ f0, ?_, ?_⟩
      · rw [List.length_cons, pow_succ]
        nlinarith [mul_le_mul hρ1 f1 zero_le_one (by positivity)]
      · have hz : (y : ℂ) - t ≠ 0 := by
          have : y - t ≠ 0 := by intro h0; have := hplus hl; rw [h0, abs_zero] at this; norm_num at this
          exact_mod_cast this
        simp only [_root_.Formalism.FourierDecayAlt.Wd.qw, hl, if_true, hρeq, ht]
        push_cast
        field_simp

open Finset in
private theorem sum_abs_lagCo_le_one_of_five_separated {d : ℕ} (y : Fin (d + 1) → ℝ)
    (hy : ∀ i j, i ≠ j → 5 ≤ |y i - y j|) : ∑ j, |_root_.Formalism.FourierDecayAlt.F7.lagCo y j| ≤ 1 := by
  have key : ∀ n : ℕ, n + 1 ≤ 5 ^ n := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; omega
  have h1 : ∀ j, |_root_.Formalism.FourierDecayAlt.F7.lagCo y j| ≤ (1 / 5 : ℝ) ^ d := by
    intro j
    unfold _root_.Formalism.FourierDecayAlt.F7.lagCo
    rw [Finset.abs_prod]
    calc ∏ i ∈ Finset.univ.erase j, |(y j - y i)⁻¹| ≤ ∏ i ∈ Finset.univ.erase j, (1 / 5 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i hi => by
            rw [abs_inv, one_div]
            exact inv_anti₀ (by norm_num) (hy j i (Finset.ne_of_mem_erase hi).symm))
      _ = (1 / 5) ^ d := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, Nat.add_sub_cancel]
  have h2 : ((d : ℝ) + 1) ≤ 5 ^ d := by exact_mod_cast key d
  calc ∑ j, |_root_.Formalism.FourierDecayAlt.F7.lagCo y j| ≤ ∑ _j : Fin (d + 1), (1 / 5 : ℝ) ^ d := Finset.sum_le_sum fun j _ => h1 j
    _ = ((d : ℝ) + 1) / 5 ^ d := by simp [div_eq_mul_inv]
    _ ≤ 1 := by rw [div_le_one (by positivity)]; exact h2

open Finset in
private theorem exists_grid_of_layout_lemma {P : _root_.Formalism.FourierDecayAlt.M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (Λ Λ₀ : ℝ) (K N : ℕ)
    (hnn : ∀ y, 0 < nn y) (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|)
    (hcard : N * (2 * P.r + 1) ≤ Y.card)
    (hcut : ∀ y ∈ Y, _root_.Formalism.FourierDecayAlt.I.OnCut P.u P.u' p.l0 y ∧ _root_.Formalism.FourierDecayAlt.I.OnCut P.u P.u' p.l0 (y + 1))
    (hq : ∀ y ∈ Y, nn y * nn (y + 1) ≤ Λ₀ ^ 2 * (_root_.Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re) (hΛ : 0 ≤ Λ)
    (hΛ₀ : Λ₀ ^ 2 * (5 / 4 : ℝ) ^ N ≤ Λ ^ 2) (d : ℕ) (hd : d ≤ 2 * P.r) (w : List _root_.Formalism.FourierDecayAlt.C.Letter)
    (hw : _root_.Formalism.FourierDecayAlt.TBB.AdmW P p.l0 Y w) (hlen : w.length + K ≤ N) : ∃ grid, _root_.Formalism.FourierDecayAlt.P.TBBx5.GridOK p nn Y Λ K w d grid := by
  classical
  unfold _root_.Formalism.FourierDecayAlt.TBB.AdmW at hw
  obtain ⟨hwcut, hwY⟩ := hw
  rw [_root_.Formalism.FourierDecayAlt.P.PBD.cutWord_iff] at hwcut
  obtain ⟨hwon, hwpair⟩ := hwcut
  let base : _root_.Formalism.FourierDecayAlt.C.Letter → ℝ := fun l => if l.1 = true then l.2 else l.2 - 1
  have hbase : ∀ l ∈ w, base l ∈ Y ∧ (l.2 = base l ∨ l.2 = base l + 1) := by
    intro l hl
    obtain ⟨y', hy', h | h⟩ := hwY l hl
    · subst h; simp [base, hy']
    · subst h; simp [base, hy']
  set B := (w.map base).toFinset with hB
  set Y' := Y \ B with hY'
  have hBcard : B.card ≤ w.length := by
    rw [hB]; exact (List.toFinset_card_le _).trans (by simp)
  have hY'card : K * (d + 1) ≤ Y'.card := by
    have h1 : Y.card - B.card ≤ Y'.card := by rw [hY']; exact Finset.le_card_sdiff B Y
    have h2 : K * (d + 1) ≤ K * (2 * P.r + 1) := Nat.mul_le_mul_left _ (by omega)
    have h3 : K * (2 * P.r + 1) + (N - K) ≤ N * (2 * P.r + 1) := by
      obtain ⟨m, hm⟩ : ∃ m, N = K + m := ⟨N - K, by omega⟩
      rw [hm, Nat.add_sub_cancel_left, Nat.add_mul]
      have : m ≤ m * (2 * P.r + 1) := Nat.le_mul_of_pos_right m (by omega)
      omega
    omega
  obtain ⟨e⟩ : Nonempty (Fin K × Fin (d + 1) ↪ Y') := Function.Embedding.nonempty_of_card_le (by
    simpa [Fintype.card_prod, Fintype.card_fin] using hY'card)
  let grid : Fin K → Fin (d + 1) → ℝ := fun a i => (e (a, i) : ℝ)
  have hgY' : ∀ a i, grid a i ∈ Y' := fun a i => (e (a, i)).2
  have hgY : ∀ a i, grid a i ∈ Y := fun a i => (Finset.mem_sdiff.1 (hgY' a i)).1
  have hgB : ∀ a i, grid a i ∉ B := fun a i => (Finset.mem_sdiff.1 (hgY' a i)).2
  have hginj : ∀ a i b j, grid a i = grid b j → (a, i) = (b, j) := fun a i b j h =>
    e.injective (Subtype.ext h)
  have hfar : ∀ a i, ∀ l ∈ w, 5 ≤ |grid a i - base l| := by
    intro a i l hl
    refine hsep _ (hgY a i) _ (hbase l hl).1 ?_
    intro h
    apply hgB a i
    rw [hB, List.mem_toFinset, h]
    exact List.mem_map_of_mem hl
  unfold _root_.Formalism.FourierDecayAlt.P.TBBx5.GridOK
  refine ⟨grid, fun a i j h => (Prod.mk.inj (hginj a i a j h)).2, hgY, ?_, ?_⟩
  · intro n
    have hys : _root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n = List.ofFn fun a => grid a (n a) := rfl
    have hpair : List.Pairwise (fun y y' => 2 < |y - y'|) (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n) := by
      rw [hys, List.pairwise_ofFn]
      intro a b hab
      have hne : grid a (n a) ≠ grid b (n b) := fun h => (ne_of_lt hab) (Prod.mk.inj (hginj _ _ _ _ h)).1
      have := hsep _ (hgY _ _) _ (hgY _ _) hne
      linarith
    have hmem : ∀ y ∈ _root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n, ∃ a, y = grid a (n a) := by
      rw [hys]
      intro y hy
      obtain ⟨a, ha⟩ := List.mem_ofFn.1 hy
      exact ⟨a, ha.symm⟩
    refine ⟨?_, ?_, hpair⟩
    · rw [_root_.Formalism.FourierDecayAlt.P.PBD.cutWord_iff, _root_.Formalism.FourierDecayAlt.P.TBBx5.plusW_eq]
      constructor
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          obtain ⟨a, rfl⟩ := hmem y hy
          exact (hcut _ (hgY _ _)).1
        · exact hwon x hx
      · rw [List.pairwise_append]
        refine ⟨?_, hwpair, ?_⟩
        · rw [List.pairwise_map]; exact hpair
        · intro x hx l hl
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          obtain ⟨a, rfl⟩ := hmem y hy
          have h5 := hfar a (n a) l hl
          rcases (hbase l hl).2 with h | h
          · rw [h, show grid a (n a) - base l = grid a (n a) - base l - 0 by ring]
            exact two_lt_abs_sub_sub_of_five_le_of_abs_le_two h5 (by norm_num)
          · rw [h, show grid a (n a) - (base l + 1) = grid a (n a) - base l - 1 by ring]
            exact two_lt_abs_sub_sub_of_five_le_of_abs_le_two h5 (by norm_num)
    · rw [_root_.Formalism.FourierDecayAlt.P.PBD.cutWord_iff, _root_.Formalism.FourierDecayAlt.P.TBBx5.minusW_eq]
      constructor
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          obtain ⟨a, rfl⟩ := hmem y hy
          exact (hcut _ (hgY _ _)).2
        · exact hwon x hx
      · rw [List.pairwise_append]
        refine ⟨?_, hwpair, ?_⟩
        · rw [List.pairwise_map]
          exact hpair.imp fun {y y'} h => by simpa [show y + 1 - (y' + 1) = y - y' by ring] using h
        · intro x hx l hl
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          obtain ⟨a, rfl⟩ := hmem y hy
          have h5 := hfar a (n a) l hl
          rcases (hbase l hl).2 with h | h
          · rw [h, show grid a (n a) + 1 - base l = grid a (n a) - base l - (-1) by ring]
            exact two_lt_abs_sub_sub_of_five_le_of_abs_le_two h5 (by norm_num)
          · rw [h, show grid a (n a) + 1 - (base l + 1) = grid a (n a) - base l - 0 by ring]
            exact two_lt_abs_sub_sub_of_five_le_of_abs_le_two h5 (by norm_num)
  · have hposition_len : (_root_.Formalism.FourierDecayAlt.D.positionted w).length = w.length := by unfold _root_.Formalism.FourierDecayAlt.D.positionted; simp
    have hF : ∀ y ∈ Y, y ∉ B → 0 ≤ nn y * nn (y + 1) / (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re ∧
        nn y * nn (y + 1) / (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re ≤ Λ ^ 2 := by
      intro y hy hyB
      have hcond : ∀ l ∈ _root_.Formalism.FourierDecayAlt.D.positionted w, ∃ t : ℝ, l.pt = t ∧ (l.plus = true → 5 ≤ |y - t|) ∧
          (l.plus = false → 5 ≤ |t - 1 - y|) := by
        intro l hl
        unfold _root_.Formalism.FourierDecayAlt.D.positionted at hl
        obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hl
        have hla : w.get a ∈ w := List.get_mem w a
        have hfar' : 5 ≤ |y - base (w.get a)| := by
          refine hsep _ hy _ (hbase _ hla).1 ?_
          intro h
          apply hyB
          rw [hB, List.mem_toFinset, h]
          exact List.mem_map_of_mem hla
        refine ⟨(w.get a).2, rfl, fun hp => ?_, fun hm => ?_⟩
        · have hp' : (w.get a).1 = true := hp
          have : base (w.get a) = (w.get a).2 := if_pos hp'
          rw [this] at hfar'
          exact hfar'
        · have hm' : (w.get a).1 = false := hm
          have : base (w.get a) = (w.get a).2 - 1 := if_neg (by rw [hm']; decide)
          rw [this, abs_sub_comm] at hfar'
          exact hfar'
      obtain ⟨ρ, hρ, hρ1, hρeq⟩ := exists_qw_eq_mul_pos_real_of_five_le_dist (_root_.Formalism.FourierDecayAlt.M.qC P) y (_root_.Formalism.FourierDecayAlt.D.positionted w) hcond
      rw [hposition_len] at hρ1
      have hre : (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re = (_root_.Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re * ρ := by
        rw [hρeq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      have hnum : 0 < nn y * nn (y + 1) := mul_pos (hnn _) (hnn _)
      have hqy := hq y hy
      have hqpos : 0 < (_root_.Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re := by
        by_contra hle
        push_neg at hle
        nlinarith [sq_nonneg Λ₀]
      rw [hre]
      have hden : 0 < (_root_.Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re * ρ := mul_pos hqpos hρ
      refine ⟨div_nonneg hnum.le hden.le, ?_⟩
      rw [div_le_iff₀ hden]
      have hpow : (5 / 4 : ℝ) ^ w.length ≤ (5 / 4) ^ N :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h1 : Λ₀ ^ 2 ≤ Λ ^ 2 * ρ := by
        have : Λ₀ ^ 2 ≤ Λ₀ ^ 2 * ((5 / 4 : ℝ) ^ w.length * ρ) := le_mul_of_one_le_right (sq_nonneg _) hρ1
        nlinarith [sq_nonneg Λ₀, mul_le_mul_of_nonneg_right hpow hρ.le]
      nlinarith
    have hterm : ∀ n : Fin K → Fin (d + 1), √((List.map nn (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n)).prod *
        (List.map (fun y => nn (y + 1)) (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n)).prod /
        (List.map (fun y : ℝ => (_root_.Formalism.FourierDecayAlt.Wd.qw (_root_.Formalism.FourierDecayAlt.M.qC P) (_root_.Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re) (_root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n)).prod) ≤ Λ ^ K := by
      intro n
      have hys : _root_.Formalism.FourierDecayAlt.P.TBBx5.ysOf grid n = List.ofFn fun a => grid a (n a) := rfl
      rw [hys]
      simp only [List.map_ofFn, List.prod_ofFn, Function.comp_def]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
      calc _ ≤ √(∏ _a : Fin K, Λ ^ 2) := Real.sqrt_le_sqrt (Finset.prod_le_prod
              (fun a _ => (hF _ (hgY a (n a)) (hgB a (n a))).1)
              (fun a _ => (hF _ (hgY a (n a)) (hgB a (n a))).2))
        _ = Λ ^ K := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm, pow_mul]
          exact Real.sqrt_sq (pow_nonneg hΛ K)
    refine le_trans (Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hterm n) (abs_nonneg _)) ?_
    rw [← Finset.sum_mul]
    simp_rw [Finset.abs_prod]
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (t := fun _ => Finset.univ) (f := fun a j => |_root_.Formalism.FourierDecayAlt.F7.lagCo (grid a) j|)]
    calc (∏ a, ∑ j, |_root_.Formalism.FourierDecayAlt.F7.lagCo (grid a) j|) * Λ ^ K ≤ 1 * Λ ^ K :=
          mul_le_mul_of_nonneg_right (Finset.prod_le_one
            (fun a _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
            (fun a _ => sum_abs_lagCo_le_one_of_five_separated _ (fun i j hij =>
              hsep _ (hgY a i) _ (hgY a j) (fun h => hij (Prod.mk.inj (hginj a i a j h)).2))))
            (pow_nonneg hΛ K)
      _ = Λ ^ K := one_mul _

open Finset in

theorem _root_.GlobalTheory.GridsFromLayout.main : ∀ (P : _root_.Formalism.FourierDecayAlt.M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (Λ Λ₀ : ℝ) (K N : ℕ), (∀ y, 0 < nn y) → ((∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) ∧ N * (2 * P.r + 1) ≤ Y.card ∧ ∀ y ∈ Y, _root_.Formalism.FourierDecayAlt.I.OnCut P.u P.u' p.l0 y ∧ _root_.Formalism.FourierDecayAlt.I.OnCut P.u P.u' p.l0 (y + 1)) → (∀ y ∈ Y, nn y * nn (y + 1) ≤ Λ₀ ^ 2 * (_root_.Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re) → 0 ≤ Λ → Λ₀ ^ 2 * (5 / 4 : ℝ) ^ N ≤ Λ ^ 2 → _root_.Formalism.FourierDecayAlt.P.TBBx5.WaveGrid p nn Y Λ K N ∧ _root_.Formalism.FourierDecayAlt.P.TBBx5.LiftGrid p nn Y Λ K N := by
  intro P Wp Wq _ _ _ _ _ _ p nn Y Λ Λ₀ K N hnn ⟨hsep, hcard, hcut⟩ hq hΛ hΛ₀
  refine ⟨?_, ?_⟩
  · unfold _root_.Formalism.FourierDecayAlt.P.TBBx5.WaveGrid
    intro j hj w hw hlen
    exact exists_grid_of_layout_lemma p nn Y Λ Λ₀ K N hnn hsep hcard hcut hq hΛ hΛ₀ _ (by omega) w hw hlen
  · unfold _root_.Formalism.FourierDecayAlt.P.TBBx5.LiftGrid
    intro b s hb hs hbs w hw hlen
    exact exists_grid_of_layout_lemma p nn Y Λ Λ₀ K N hnn hsep hcard hcut hq hΛ hΛ₀ _ (by omega) w hw hlen

end

end GlobalTheory.GridsFromLayout
