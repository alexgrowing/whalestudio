import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace

namespace Formalism.FourierDecayAlt.P.Fr2

section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

lemma mem_inv (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) (Y : ℂ)
    (h0 : Y ∈ st.inv) (h : ∀ l ∈ w, Y - l.pt ≠ 0 ∧ Y - l.pt ≠ 1 ∧ Y - l.pt ≠ -1) :
    Y ∈ (ofWord L st w).inv := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    by_cases hp : l.plus
    · simp only [ofWord, hp, if_true, FrameData.plus]
      exact ⟨ih', hl.1, hl.2.1⟩
    · simp only [ofWord, hp, FrameData.minus]
      refine ⟨ih', ?_, ?_⟩
      · intro e; apply hl.1; linear_combination -e
      · intro e; apply hl.2.2; linear_combination -e

lemma qw_ne (q : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (h0 : q Y ≠ 0)
    (h : ∀ l ∈ w, Y - l.pt ≠ 0 ∧ Y - l.pt ≠ -1) : qw q w Y ≠ 0 := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    by_cases hp : l.plus
    · simp only [qw, hp, if_true]
      refine mul_ne_zero ih' (div_ne_zero ?_ hl.1)
      intro e; apply hl.2; linear_combination e
    · simp only [qw, hp]
      refine mul_ne_zero ih' (div_ne_zero ?_ ?_)
      · intro e; apply hl.1; linear_combination -e
      · intro e; apply hl.2; linear_combination -e
end

theorem frameAll (hS : StartFrame) (hM : StartModule) (hP : PlusStep) (hMi : MinusStep)
    (hF : FrameFree) (hW : WordJoint) : FrameAll := by
  intro A S _ _ _ _ _ _ r L st w hL hst hA
  induction w with
  | nil => exact hS hM A S r L st hst
  | cons l w ih =>
    obtain ⟨hnd, hre, hpt, hpw⟩ := hA
    have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup := List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    have hpw' := List.pairwise_cons.mp hpw
    have hAw : admitted st w :=
      ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
    have ihw := ih hAw
    have hfree := hF A S r L st w l.intersection_update_fsHerm_neg_one hnd'.1
    obtain ⟨p0, p1, pm1, q0, qm1⟩ := hpt l (by simp)
    have hd := hpw'.1
    have hq := (hW A S r L st w).2.2.1
    have m0 : l.pt ∈ (ofWord L st w).inv := mem_inv L st w _ p0 (fun l' hl' =>
      ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    have m1 : l.pt + 1 ∈ (ofWord L st w).inv := mem_inv L st w _ p1 (fun l' hl' =>
      ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)
    have mm1 : l.pt - 1 ∈ (ofWord L st w).inv := mem_inv L st w _ pm1 (fun l' hl' =>
      ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
    by_cases hp : l.plus
    · have e : ofWord L st (l :: w) = (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e]
      apply hP
      refine ⟨hL, ihw, hfree, hre l (by simp), m0, m1, ?_⟩
      rw [hq]
      exact qw_ne _ _ _ q0 (fun l' hl' =>
        ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    · have e : ofWord L st (l :: w) = (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      rw [e]
      apply hMi
      refine ⟨hL, ihw, hfree, hre l (by simp), m0, m1, mm1, ?_⟩
      rw [hq]
      exact qw_ne _ _ _ qm1 (fun l' hl' =>
        ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)

theorem frameAssemble : FrameAssemble := by
  intro hS hM hP hMi hF hW
  have hA := frameAll hS hM hP hMi hF hW
  refine ⟨hA, ?_⟩
  intro A S _ _ _ _ _ _ r L st w hL hst hAd
  have h := hA A S r L st w hL hst hAd
  obtain ⟨w1, w2, w3, w4, w5⟩ := hW A S r L st w
  refine ⟨h.F_Fi, h.Fi_F, ?_, ?_, ?_⟩
  · have := h.form
    rw [w1] at this
    rw [this]; simp only [FrameData.d, w4]
  · intro Y hY
    have := h.frame_τ Y (by rw [w5]; exact hY)
    rw [w2] at this; exact this
  · intro Y hY hY1
    have := h.frame_l Y hY hY1
    rw [w2] at this; exact this

section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

lemma q_eq (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) : (ofWord L st w).q = qw st.q w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    by_cases hp : l.plus
    · funext Y; simp [ofWord, qw, hp, FrameData.plus, ih]
    · funext Y; simp [ofWord, qw, hp, FrameData.minus, ih]

lemma mem_invB (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) (Y : ℂ)
    (h0 : Y ∈ st.inv) (h : ∀ l ∈ w, Y - ypt l ≠ 0 ∧ Y - ypt l ≠ 1) :
    Y ∈ (ofWord L st w).inv := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    by_cases hp : l.plus
    · simp only [ypt, hp, if_true] at hl
      simp only [ofWord, hp, if_true, FrameData.plus]
      exact ⟨ih', hl.1, hl.2⟩
    · simp only [ypt, hp] at hl
      simp only [ofWord, hp, FrameData.minus]
      refine ⟨ih', ?_, ?_⟩
      · intro e; apply hl.2; simp only [Bool.false_eq_true, if_false]; linear_combination -e
      · intro e; apply hl.1; simp only [Bool.false_eq_true, if_false]; linear_combination -e

lemma qw_neB (q : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (h0 : q Y ≠ 0)
    (h : ∀ l ∈ w, Y - ypt l ≠ 0 ∧ Y - ypt l ≠ 1 ∧ Y - ypt l ≠ -1) : qw q w Y ≠ 0 := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    by_cases hp : l.plus
    · simp only [ypt, hp, if_true] at hl
      simp only [qw, hp, if_true]
      refine mul_ne_zero ih' (div_ne_zero ?_ hl.1)
      intro e; apply hl.2.2; linear_combination e
    · simp only [ypt, hp] at hl
      simp only [qw, hp]
      refine mul_ne_zero ih' (div_ne_zero ?_ ?_)
      · intro e; apply hl.2.1; simp only [Bool.false_eq_true, if_false]; linear_combination -e
      · intro e; apply hl.1; simp only [Bool.false_eq_true, if_false]; linear_combination -e
end

theorem admissible_rec_of_admissible_word : AdmRecOfAdm := by
  intro A S _ _ _ _ _ _ r L st w hA
  induction w with
  | nil => trivial
  | cons l w ih =>
    obtain ⟨hnd, hre, hpt, hpw⟩ := hA
    have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
      List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    have hpw' := List.pairwise_cons.mp hpw
    have hAw : admitted st w :=
      ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
    obtain ⟨p0, p1, pm1, q0, qm1⟩ := hpt l (by simp)
    have hd := hpw'.1
    have m0 : l.pt ∈ (ofWord L st w).inv := mem_inv L st w _ p0 (fun l' hl' =>
      ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    have m1 : l.pt + 1 ∈ (ofWord L st w).inv := mem_inv L st w _ p1 (fun l' hl' =>
      ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)
    have mm1 : l.pt - 1 ∈ (ofWord L st w).inv := mem_inv L st w _ pm1 (fun l' hl' =>
      ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
    refine ⟨ih hAw, hnd'.1, hre l (by simp), m0, m1, ?_⟩
    by_cases hp : l.plus
    · simp only [hp, if_true]
      rw [q_eq]
      exact qw_ne _ _ _ q0 (fun l' hl' =>
        ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    · simp only [hp]
      refine ⟨mm1, ?_⟩
      rw [q_eq]
      exact qw_ne _ _ _ qm1 (fun l' hl' =>
        ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)

theorem admissible_rec_of_base : AdmRecOfBase := by
  intro A S _ _ _ _ _ _ r L st w hA
  induction w with
  | nil => trivial
  | cons l w ih =>
    obtain ⟨hnd, hre, hpt, hpw⟩ := hA
    have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
      List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    have hpw' := List.pairwise_cons.mp hpw
    have hAw : AdmBase st w :=
      ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
    obtain ⟨p0, p1, p2, q0⟩ := hpt l (by simp)
    have hd := hpw'.1
    have m0 : ypt l ∈ (ofWord L st w).inv := mem_invB L st w _ p0 (fun l' hl' =>
      ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e)⟩)
    have m1 : ypt l + 1 ∈ (ofWord L st w).inv := mem_invB L st w _ p1 (fun l' hl' =>
      ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
    have m2 : l.plus = false → ypt l + 2 ∈ (ofWord L st w).inv := fun hf => mem_invB L st w _ (p2 hf) (fun l' hl' =>
      ⟨fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    have qq : (ofWord L st w).q (ypt l) ≠ 0 := by
      rw [q_eq]
      exact qw_neB _ _ _ q0 (fun l' hl' =>
        ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
         fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    by_cases hp : l.plus
    · simp only [ypt, hp, if_true] at m0 m1 qq
      refine ⟨ih hAw, hnd'.1, hre l (by simp), m0, m1, ?_⟩
      simp only [hp, if_true]; exact qq
    · have hf : l.plus = false := by simpa using hp
      have m2' := m2 hf
      simp only [ypt, hf, Bool.false_eq_true, if_false] at m0 m1 m2' qq
      refine ⟨ih hAw, hnd'.1, hre l (by simp), ?_, ?_, ?_⟩
      · have : l.pt - 1 + 1 = l.pt := by ring
        rwa [this] at m1
      · have : l.pt - 1 + 2 = l.pt + 1 := by ring
        rwa [this] at m2'
      · simp only [hf, Bool.false_eq_true, if_false]; exact ⟨m0, qq⟩

theorem frameRecAssemble : FrameRecAssemble := by
  intro h0 hm hp hn hf A S _ _ _ _ _ _ r L st w hL hs
  induction w with
  | nil => intro _; exact h0 hm A S r L st hs
  | cons l w ih =>
    rintro ⟨h1, h2, h3, h4, h5, h6⟩
    have hw := ih h1
    have hfr := hf A S r L st w l.intersection_update_fsHerm_neg_one h2
    by_cases hl : l.plus
    · simp only [hl, if_true] at h6
      simp only [ofWord, hl, if_true]
      exact hp A S r L _ l.intersection_update_fsHerm_neg_one l.pt ⟨hL, hw, hfr, h3, h4, h5, h6⟩
    · simp only [hl] at h6
      simp only [ofWord, hl]
      exact hn A S r L _ l.intersection_update_fsHerm_neg_one l.pt ⟨hL, hw, hfr, h3, h4, h5, h6.1, h6.2⟩

section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

lemma eU_diag (a : S) (i : Fin 2) :
    (eU a i i : SlopeTestRemainingChoices S A) = Matrix.diagonal (fun e => if e a = i then 1 else 0) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy; simp [eU]
  · have : ¬ (x a = i ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b) := by
      rintro ⟨h1, h2, h3⟩
      apply hxy; funext b
      by_cases hb : b = a
      · subst hb; rw [h1, h2]
      · exact h3 b hb
    simp [eU, Matrix.diagonal_apply_ne _ hxy, this]

lemma ins_diag (a : S) (X Y : Ix S → A) :
    ins a !![Matrix.diagonal X, 0; 0, Matrix.diagonal Y] =
      Matrix.diagonal (fun e => if e a = 0 then X e else Y e) := by
  simp only [ins, Fin.sum_univ_two, eU_diag]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one,
    mul_zero, add_zero, zero_add, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
  congr 1; funext e
  by_cases h : e a = 0
  · simp [h]
  · have h1 : e a = 1 := Fin.eq_one_of_ne_zero _ h
    simp [h1]

lemma ins_sc (a : S) (φ : ℂ) :
    (ins a !![φ • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] : SlopeTestRemainingChoices S A) =
      Matrix.diagonal (fun e => if e a = 0 then algebraMap ℂ A φ else 1) := by
  have h1 : (φ • (1 : SlopeTestRemainingChoices S A)) = Matrix.diagonal (fun _ => algebraMap ℂ A φ) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul]; congr 1; funext _
    simp [Algebra.algebraMap_eq_smul_one]
  have h2 : (1 : SlopeTestRemainingChoices S A) = Matrix.diagonal (fun _ => (1 : A)) := Matrix.diagonal_one.symm
  rw [h1]; conv_lhs => rw [h2]
  exact ins_diag a _ _
end

theorem cDiag : CDiag := by
  intro A S _ _ _ _ _ _ r L st P κ x0 hx hxi w
  have km : ∀ f g : P → ℂ, κ f * κ g = κ (fun ρ => f ρ * g ρ) := fun f g => (map_mul κ f g).symm
  have kc : ∀ c : ℂ, algebraMap ℂ A c = κ (fun _ => c) := fun c => (AlgHom.commutes κ c).symm
  have ks : ∀ (c : ℂ) (f : P → ℂ), c • κ f = κ (fun ρ => c * f ρ) := fun c f => (map_smul κ c f).symm
  have k1 : (1 : A) = κ (fun _ => 1) := (map_one κ).symm
  induction w with
  | nil =>
    refine ⟨fun Y => ?_, fun Y => ?_, ?_⟩
    · simp [ofWord, Start.frame, io, xs, hx, Matrix.scalar_apply]
    · simp [ofWord, Start.frame, io, xs, hxi, Matrix.scalar_apply]
    · simp only [ofWord, Start.frame, cs, ← k1, Matrix.diagonal_one]
  | cons l w ih =>
    obtain ⟨ihx, ihxi, ihc⟩ := ih
    have hq : (ofWord L st w).q = qw st.q w := by
      clear ihx ihxi ihc
      induction w with
      | nil => rfl
      | cons l' w ih' =>
        by_cases hl : l'.plus
        · funext Y; simp [ofWord, hl, FrameData.plus, qw, ih']
        · funext Y; simp [ofWord, hl, FrameData.minus, qw, ih']
    by_cases hp : l.plus
    · refine ⟨fun Y => ?_, fun Y => ?_, ?_⟩
      · simp only [ofWord, hp, if_true, FrameData.plus, ihx, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]
        congr 1; funext e
        split_ifs <;> simp [kc, km]
      · simp only [ofWord, hp, if_true, FrameData.plus, ihxi, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]
        congr 1; funext e
        split_ifs <;> simp [kc, km, inv_div, mul_comm]
      · simp only [ofWord, hp, if_true, FrameData.plus, ihx, ihxi, ihc, hq, ← Matrix.diagonal_smul, ins_diag,
          Matrix.diagonal_mul_diagonal, cs]
        congr 1; funext e
        split_ifs <;> simp [ks, km, div_eq_mul_inv]
    · have hp' : l.plus = false := by simpa using hp
      refine ⟨fun Y => ?_, fun Y => ?_, ?_⟩
      · simp only [ofWord, hp', Bool.false_eq_true, if_false, FrameData.minus, ihx, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]
        congr 1; funext e
        split_ifs <;> simp [kc, km]
      · simp only [ofWord, hp', Bool.false_eq_true, if_false, FrameData.minus, ihxi, ins_sc, Matrix.diagonal_mul_diagonal, xs, phiL]
        congr 1; funext e
        split_ifs <;> simp [kc, km, inv_div, mul_comm]
      · simp only [ofWord, hp', Bool.false_eq_true, if_false, FrameData.minus, ihx, ihxi, ihc, hq, ← Matrix.diagonal_smul, ins_diag,
          Matrix.diagonal_mul_diagonal, cs]
        congr 1; funext e
        split_ifs <;> simp [ks, km, div_eq_mul_inv]

lemma pos_mul {a b : ℂ} (ha : Pos a) (hb : Pos b) : Pos (a * b) := by
  obtain ⟨a1, a2⟩ := ha; obtain ⟨b1, b2⟩ := hb
  refine ⟨?_, ?_⟩
  · simp [Complex.mul_re, a2, b2]; positivity
  · simp [Complex.mul_im, a2, b2]

lemma pos_ofReal {x : ℝ} (h : 0 < x) : Pos (x : ℂ) := ⟨by simpa using h, by simp⟩

lemma pos_eq {a : ℂ} (ha : Pos a) : a = (a.re : ℂ) := by
  apply Complex.ext <;> simp [ha.2]

lemma pos_div {a b : ℂ} (ha : Pos a) (hb : Pos b) : Pos (a / b) := by
  rw [pos_eq ha, pos_eq hb, ← Complex.ofReal_div]
  exact pos_ofReal (div_pos ha.1 hb.1)

lemma frac (z : ℂ) (hz : z.im = 0) (a b : ℝ) (h : 0 < (z.re + a) * (z.re + b)) :
    Pos ((z + a) / (z + b)) := by
  have e : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [e, ← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_div]
  apply pos_ofReal
  have hb : z.re + b ≠ 0 := by intro h0; simp [h0] at h
  have : (z.re + a) / (z.re + b) = (z.re + a) * (z.re + b) / (z.re + b) ^ 2 := by
    field_simp
  rw [this]; positivity

section
variable {S : Type} [Fintype S] [DecidableEq S]

lemma gt1 {t : ℝ} (h : 1 < |t|) : 0 < t * (t - 1) ∧ 0 < t * (t + 1) := by
  rcases lt_abs.mp h with h | h
  · constructor <;> nlinarith
  · constructor <;> nlinarith

lemma phi_pos (l : Letter ℂ S) (Y : ℂ) (hY : Y.im = 0) (hl : l.pt.im = 0) (h : 1 < |Y.re - l.pt.re|) :
    Pos (phiL l Y) := by
  obtain ⟨g1, g2⟩ := gt1 h
  unfold phiL
  split_ifs
  · have := frac (Y - l.pt) (by simp [hY, hl]) 0 (-1) (by simp; nlinarith)
    simpa [sub_eq_add_neg] using this
  · have := frac (l.pt - Y) (by simp [hY, hl]) 0 (-1) (by simp; nlinarith)
    simpa [sub_eq_add_neg] using this

lemma xs_pos (x0 : ℂ → ℂ) (w : List (Letter ℂ S)) (e : Ix S) (Y : ℂ) (hY : Y.im = 0) (h0 : Pos (x0 Y))
    (h : ∀ l ∈ w, l.pt.im = 0 ∧ 1 < |Y.re - l.pt.re|) : Pos (xs x0 w e Y) := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    simp only [xs]
    apply pos_mul ih'
    split_ifs
    · exact phi_pos l Y hY hl.1 hl.2
    · exact ⟨by simp, by simp⟩

lemma qw_pos (q0 : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (hY : Y.im = 0) (h0 : Pos (q0 Y))
    (h : ∀ l ∈ w, l.pt.im = 0 ∧ 1 < |Y.re - l.pt.re|) : Pos (qw q0 w Y) := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    obtain ⟨g1, g2⟩ := gt1 hl.2
    simp only [qw]
    split_ifs
    · apply pos_mul ih'
      have := frac (Y - l.pt) (by simp [hY, hl.1]) 1 0 (by simp; nlinarith)
      simpa [sub_eq_add_neg] using this
    · apply pos_mul ih'
      have := frac (l.pt - Y) (by simp [hY, hl.1]) 0 (-1) (by simp; nlinarith)
      simpa [sub_eq_add_neg] using this
end

theorem cPos : CPos := by
  intro S _ _ x0 q0 w him hpw hpos e
  induction w with
  | nil => exact ⟨by simp [cs], by simp [cs]⟩
  | cons l w ih =>
    have hpw' := List.pairwise_cons.mp hpw
    have ih' := ih (fun l' h => him l' (by simp [h])) hpw'.2 (fun l' h => hpos l' (by simp [h]))
    obtain ⟨x1, x2, x3, q1, q2⟩ := hpos l (by simp)
    have hl := him l (by simp)
    have d0 : ∀ l' ∈ w, l'.pt.im = 0 ∧ 1 < |(l.pt).re - l'.pt.re| := fun l' h =>
      ⟨him l' (by simp [h]), by have := hpw'.1 l' h; linarith⟩
    have d1 : ∀ l' ∈ w, l'.pt.im = 0 ∧ 1 < |(l.pt + 1).re - l'.pt.re| := fun l' h =>
      ⟨him l' (by simp [h]), by
        have := hpw'.1 l' h
        simp only [Complex.add_re, Complex.one_re]
        rcases lt_abs.mp this with g | g
        · exact lt_abs.mpr (Or.inl (by linarith))
        · exact lt_abs.mpr (Or.inr (by linarith))⟩
    have dm : ∀ l' ∈ w, l'.pt.im = 0 ∧ 1 < |(l.pt - 1).re - l'.pt.re| := fun l' h =>
      ⟨him l' (by simp [h]), by
        have := hpw'.1 l' h
        simp only [Complex.sub_re, Complex.one_re]
        rcases lt_abs.mp this with g | g
        · exact lt_abs.mpr (Or.inl (by linarith))
        · exact lt_abs.mpr (Or.inr (by linarith))⟩
    simp only [cs]
    apply pos_mul ih'
    split_ifs
    · exact pos_div (qw_pos q0 w _ hl q1 d0) (xs_pos x0 w e _ (by simp [hl]) x2 d1)
    · exact xs_pos x0 w e _ hl x1 d0
    · exact pos_div (qw_pos q0 w _ (by simp [hl]) q2 dm) (xs_pos x0 w e _ (by simp [hl]) x3 dm)
    · exact xs_pos x0 w e _ hl x1 d0

section
variable {S : Type} [Fintype S] [DecidableEq S]

lemma phi_posB (l : Letter ℂ S) (Y : ℂ) (hY : Y.im = 0) (hl : l.pt.im = 0)
    (h : 0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re - 1)) : Pos (phiL l Y) := by
  unfold phiL
  unfold ypt at h
  split_ifs at h ⊢
  · have := frac (Y - l.pt) (by simp [hY, hl]) 0 (-1) (by simp; nlinarith)
    simpa [sub_eq_add_neg] using this
  · have := frac (l.pt - Y) (by simp [hY, hl]) 0 (-1) (by simp at h ⊢; nlinarith)
    simpa [sub_eq_add_neg] using this

lemma xs_posB (x0 : ℂ → ℂ) (w : List (Letter ℂ S)) (e : Ix S) (Y : ℂ) (hY : Y.im = 0) (h0 : Pos (x0 Y))
    (h : ∀ l ∈ w, l.pt.im = 0 ∧ 0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re - 1)) : Pos (xs x0 w e Y) := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    simp only [xs]
    apply pos_mul ih'
    split_ifs
    · exact phi_posB l Y hY hl.1 hl.2
    · exact ⟨by simp, by simp⟩

lemma qw_posB (q0 : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (hY : Y.im = 0) (h0 : Pos (q0 Y))
    (h : ∀ l ∈ w, l.pt.im = 0 ∧ 0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re - 1) ∧
      0 < (Y.re - (ypt l).re) * (Y.re - (ypt l).re + 1)) : Pos (qw q0 w Y) := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    obtain ⟨hl, g1, g2⟩ := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    simp only [qw]
    unfold ypt at g1 g2
    split_ifs at g1 g2 ⊢
    · apply pos_mul ih'
      have := frac (Y - l.pt) (by simp [hY, hl]) 1 0 (by simp; nlinarith)
      simpa [sub_eq_add_neg] using this
    · apply pos_mul ih'
      have := frac (l.pt - Y) (by simp [hY, hl]) 0 (-1) (by simp at g1 g2 ⊢; nlinarith)
      simpa [sub_eq_add_neg] using this
end

theorem cPosBase : CPosBase := by
  intro S _ _ x0 q0 w him hpw hpos e
  induction w with
  | nil => exact ⟨by simp [cs], by simp [cs]⟩
  | cons l w ih =>
    have hpw' := List.pairwise_cons.mp hpw
    have ih' := ih (fun l' h => him l' (by simp [h])) hpw'.2 (fun l' h => hpos l' (by simp [h]))
    obtain ⟨x1, x2, q1⟩ := hpos l (by simp)
    have hl := him l (by simp)
    have hy : (ypt l).im = 0 := by unfold ypt; split_ifs <;> simp [hl]
    have d0 : ∀ l' ∈ w, l'.pt.im = 0 ∧ 0 < ((ypt l).re - (ypt l').re) * ((ypt l).re - (ypt l').re - 1) ∧
        0 < ((ypt l).re - (ypt l').re) * ((ypt l).re - (ypt l').re + 1) := fun l' h =>
      ⟨him l' (by simp [h]), by
        rcases lt_abs.mp (hpw'.1 l' h) with g | g <;> constructor <;> nlinarith⟩
    have d1 : ∀ l' ∈ w, l'.pt.im = 0 ∧
        0 < ((ypt l + 1).re - (ypt l').re) * ((ypt l + 1).re - (ypt l').re - 1) := fun l' h =>
      ⟨him l' (by simp [h]), by
        simp only [Complex.add_re, Complex.one_re]
        rcases lt_abs.mp (hpw'.1 l' h) with g | g <;> nlinarith⟩
    have X0 := xs_posB x0 w e _ hy x1 (fun l' h => ⟨(d0 l' h).1, (d0 l' h).2.1⟩)
    have X1 := xs_posB x0 w e _ (by simp [hy]) x2 d1
    have Q0 := qw_posB q0 w _ hy q1 d0
    simp only [cs]
    apply pos_mul ih'
    unfold ypt at X0 X1 Q0
    split_ifs at X0 X1 Q0 ⊢
    · exact pos_div Q0 X1
    · exact X0
    · exact pos_div Q0 X0
    · simpa using X1

lemma q_core' (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    ∏ i ∈ Icc 1 k, ((Y - 1 + 1/2 + u i) * (Y - 1 + 1/2 + u' i)) < 0 := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  have hl : l ∈ Icc 1 k := mem_Icc.2 ⟨hl1, hlk⟩
  rw [← mul_prod_erase _ _ hl]
  apply mul_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos <;> linarith
  · apply prod_pos
    intro i hi
    have hne := ne_of_mem_erase hi
    have hi' := mem_Icc.1 (mem_of_mem_erase hi)
    rcases lt_or_gt_of_ne hne with hil | hil
    · obtain ⟨a, b, c, d⟩ := h i (mem_Icc.2 ⟨hi'.1, by omega⟩)
      have h1 := hu' (i + 1) l (by omega) (by omega) hlk
      have h2 := hu' i l hi'.1 (by omega) hlk
      apply mul_pos <;> linarith
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      obtain ⟨a, b, c, d⟩ := h j (mem_Icc.2 ⟨by omega, by omega⟩)
      have h1 := hu l (j + 1) hl1 (by omega) hi'.2
      have h2 := hu l j hl1 (by omega) (by omega)
      apply mul_pos_of_neg_of_neg <;> linarith

lemma q_core'' (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u' l + 2 ≤ -Y ∧ -Y ≤ u l - 2) :
    ∏ i ∈ Icc 1 k, ((Y - 1 + 1/2 + u i) * (Y - 1 + 1/2 + u' i)) < 0 := by
  have := q_core' k u' u ρ l Y hl1 hlk (interlaces_swap h) hA
  rwa [prod_congr rfl (fun i _ => mul_comm (Y - 1 + 1/2 + u' i) (Y - 1 + 1/2 + u i))] at this

theorem qPositiveShift : QPositiveShift := by
  intro k u u' ρ l Y T T' hl1 hlk h hc hT hT'
  have hTT : 0 < T * T' := mul_pos hT hT'
  have hP : ∏ i ∈ Icc 1 k, ((Y - 1 + 1/2 + u i) * (Y - 1 + 1/2 + u' i)) < 0 := by
    rcases hc with hA | hB
    · exact q_core' k u u' ρ l Y hl1 hlk h hA
    · exact q_core'' k u u' ρ l Y hl1 hlk h hB
  unfold qpoly
  nlinarith

theorem cPosCut : CPosCut := by
  intro hI hQ hQs hC S _ _ k u u' ρ l T T' w hl1 hlk hint hT hT' hpts hpw e
  apply hC S _ _ w (fun a ha => (hpts a ha).1) hpw
  intro a ha
  obtain ⟨him, hcut⟩ := hpts a ha
  obtain ⟨y, hy⟩ : ∃ y : ℝ, a.pt = (y : ℂ) := ⟨a.pt.re, by apply Complex.ext <;> simp [him]⟩
  have hcut' : OnCut u u' l y := by simpa [hy] using hcut
  have hx : ∀ e : ℝ, e ∈ ({-1, 0, 1} : Finset ℝ) →
      Pos ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((y + e : ℝ) : ℂ) + (ρ i : ℂ))) := by
    intro e he
    have := hI k u u' ρ l y hl1 hlk hint hcut' e he
    have c : ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((y + e : ℝ) : ℂ) + (ρ i : ℂ))) =
        (((-1 : ℝ) ^ (k - l) * xpoly k ρ (y + e) : ℝ) : ℂ) := by
      unfold xpoly; push_cast; ring
    rw [c]; exact pos_ofReal this
  have hq : ∀ z : ℝ, 0 < qpoly k T T' u u' z →
      Pos (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ))) := by
    intro z hz
    have c : (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ))) =
        ((qpoly k T T' u u' z : ℝ) : ℂ) := by
      unfold qpoly; push_cast; ring
    rw [c]; exact pos_ofReal hz
  rw [hy]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := hx 0 (by simp); simpa using this
  · have := hx 1 (by simp); simpa using this
  · have := hx (-1) (by simp); simpa [sub_eq_add_neg] using this
  · exact hq y (hQ k u u' ρ l y T T' hl1 hlk hint hcut' hT hT')
  · have := hq (y - 1) (hQs k u u' ρ l y T T' hl1 hlk hint hcut' hT hT'); simpa using this

theorem cPosCutBase : CPosCutBase := by
  intro hI hQ hQs hC S _ _ k u u' ρ l T T' w hl1 hlk hint hT hT' hpts hpw e
  apply hC S _ _ w (fun a ha => (hpts a ha).1) hpw
  intro a ha
  obtain ⟨him, hcut⟩ := hpts a ha
  have himy : (ypt a).im = 0 := by unfold ypt; split_ifs <;> simp [him]
  obtain ⟨y, hy⟩ : ∃ y : ℝ, ypt a = (y : ℂ) := ⟨(ypt a).re, by apply Complex.ext <;> simp [himy]⟩
  have hcut' : OnCut u u' l y ∨ OnCut u u' l (y + 1) := by simpa [hy] using hcut
  have hx : ∀ z : ℝ, 0 < (-1 : ℝ) ^ (k - l) * xpoly k ρ z →
      Pos ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((z : ℝ) : ℂ) + (ρ i : ℂ))) := by
    intro z hz
    have c : ((-1 : ℂ) ^ (k - l) * ∏ i ∈ Finset.Icc 1 (k - 1), (((z : ℝ) : ℂ) + (ρ i : ℂ))) =
        (((-1 : ℝ) ^ (k - l) * xpoly k ρ z : ℝ) : ℂ) := by
      unfold xpoly; push_cast; ring
    rw [c]; exact pos_ofReal hz
  have hq : ∀ z : ℝ, 0 < qpoly k T T' u u' z →
      Pos (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ))) := by
    intro z hz
    have c : (-((T : ℂ) * T') * ∏ i ∈ Finset.Icc 1 k, (((z : ℝ) : ℂ) + 1 / 2 + (u i : ℂ)) * (((z : ℝ) : ℂ) + 1 / 2 + (u' i : ℂ))) =
        ((qpoly k T T' u u' z : ℝ) : ℂ) := by
      unfold qpoly; push_cast; ring
    rw [c]; exact pos_ofReal hz
  rw [hy]
  rcases hcut' with hc | hc
  · have a0 := hI k u u' ρ l y hl1 hlk hint hc 0 (by simp)
    have a1 := hI k u u' ρ l y hl1 hlk hint hc 1 (by simp)
    rw [add_zero] at a0
    refine ⟨hx y a0, ?_, hq y (hQ k u u' ρ l y T T' hl1 hlk hint hc hT hT')⟩
    have := hx (y + 1) a1; simpa using this
  · have a0 := hI k u u' ρ l (y + 1) hl1 hlk hint hc 0 (by simp)
    have a1 := hI k u u' ρ l (y + 1) hl1 hlk hint hc (-1) (by simp)
    have b := hQs k u u' ρ l (y + 1) T T' hl1 hlk hint hc hT hT'
    rw [add_zero] at a0
    have e1 : y + 1 + -1 = y := by ring
    have e2 : y + 1 - 1 = y := by ring
    rw [e1] at a1; rw [e2] at b
    refine ⟨hx y a1, ?_, hq y b⟩
    have := hx (y + 1) a0; simpa using this

end Formalism.FourierDecayAlt.P.Fr2

namespace Formalism.FourierDecayAlt.P

theorem frame_of_steps : Formalism.FourierDecayAlt.Fr.FrameAssemble := Fr2.frameAssemble

theorem c_diagonal : Formalism.FourierDecayAlt.Fr.CDiag := Fr2.cDiag

theorem cPos_true : Formalism.FourierDecayAlt.Fr.CPos := Fr2.cPos

theorem q_positive_shift : Formalism.FourierDecayAlt.Fr.QPositiveShift := Fr2.qPositiveShift

theorem c_pos_truncated : Formalism.FourierDecayAlt.Fr.CPosCut := Fr2.cPosCut

theorem c_pos_base : Formalism.FourierDecayAlt.Fr.CPosBase := Fr2.cPosBase

theorem admissible_rec_of_admissible : Formalism.FourierDecayAlt.Fr.AdmRecOfAdm := Fr2.admissible_rec_of_admissible_word

theorem admissible_rec_of_base_case : Formalism.FourierDecayAlt.Fr.AdmRecOfBase := Fr2.admissible_rec_of_base

theorem frame_rec_of_steps : Formalism.FourierDecayAlt.Fr.FrameRecAssemble := Fr2.frameRecAssemble

theorem c_pos_truncated_base : Formalism.FourierDecayAlt.Fr.CPosCutBase := Fr2.cPosCutBase

end Formalism.FourierDecayAlt.P
