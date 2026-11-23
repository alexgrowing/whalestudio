import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommuteInvLeft

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

namespace Formalism.FourierDecayAlt.P.Fr10

open Formalism.FourierDecayAlt.P.Wd1

section Gen

variable {B : Type} [Ring B]

lemma comm_inv {x xi y : B} (h1 : x * xi = 1) (h2 : xi * x = 1) (h : Commute x y) : Commute xi y := by
  first | exact GlobalTheory.CommuteInvLeft.commute_inv_left .. | (apply GlobalTheory.CommuteInvLeft.commute_inv_left <;> assumption) | (intros; apply GlobalTheory.CommuteInvLeft.commute_inv_left <;> assumption) | (apply @GlobalTheory.CommuteInvLeft.commute_inv_left <;> assumption) | (intros; apply @GlobalTheory.CommuteInvLeft.commute_inv_left <;> assumption) | (apply @GlobalTheory.CommuteInvLeft.commute_inv_left <;> first | assumption | infer_instance) | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B ‹_› x xi y h1 h2 h | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B ‹_› x xi y h1 h2 | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B ‹_› x xi y h1 | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B ‹_› x xi y | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B ‹_› x xi | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B ‹_› x | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B ‹_› | exact @GlobalTheory.CommuteInvLeft.commute_inv_left B

lemma star_inv [StarRing B] {x xi : B} (h1 : x * xi = 1) (h : star x = x) : star xi = xi := by
  have h3 : star xi * x = 1 := by
    have := congrArg star h1
    rwa [star_mul, star_one, h] at this
  calc star xi = star xi * (x * xi) := by rw [h1, mul_one]
    _ = (star xi * x) * xi := by rw [mul_assoc]
    _ = xi := by rw [h3, one_mul]

lemma t21_commutator_identity [Algebra ℂ B] (a c a' c' : B) (Y Y' Yb : ℂ) (hne : Y ≠ Y')
    (h1 : (Y - Y') • (a * c' - c' * a) = c * a' - c' * a)
    (h2 : (Y' - Y) • (a' * c - c * a') = c' * a - c * a') :
    -a * ((Yb - Y') • c') + ((Yb - Y - 1) • c) * (-a') = -a' * ((Yb - Y) • c) + ((Yb - Y' - 1) • c') * (-a) := by
  have hXZ : a * c' - c' * a + (c * a' - a' * c) = 0 := by
    have h : (Y - Y') • (a * c' - c' * a + (c * a' - a' * c)) = 0 := by
      linear_combination (norm := module) h1 + h2
    exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne)
  simp only [neg_mul, mul_neg, mul_smul_comm, smul_mul_assoc]
  linear_combination (norm := module) (-(Yb - Y)) • hXZ - h1

end Gen

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]

lemma io_mul (x y : A) : (io (x * y) : SlopeTestRemainingChoices S A) = io x * io y := (Matrix.scalar (Ix S)).map_mul x y

lemma io_one : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := (Matrix.scalar (Ix S)).map_one

lemma io_comm {x y : A} (h : x * y = y * x) : Commute (io x : SlopeTestRemainingChoices S A) (io y) := by
  show (io x : SlopeTestRemainingChoices S A) * io y = io y * io x
  rw [← io_mul, ← io_mul, h]

lemma free_io (c : S) (x : A) : FreeOf c (io x : SlopeTestRemainingChoices S A) := by
  intro i j
  show (eU c i j : SlopeTestRemainingChoices S A) * io x = io x * eU c i j
  ext u v
  simp only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, eU, Matrix.of_apply]
  split_ifs <;> simp

lemma free_one (c : S) : FreeOf c (1 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.one_right _

lemma free_zero (c : S) : FreeOf c (0 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.zero_right _

lemma free_mul {c : S} {b b' : SlopeTestRemainingChoices S A} (h : FreeOf c b) (h' : FreeOf c b') : FreeOf c (b * b') :=
  fun i j => (h i j).mul_right (h' i j)

lemma free_add {c : S} {b b' : SlopeTestRemainingChoices S A} (h : FreeOf c b) (h' : FreeOf c b') : FreeOf c (b + b') :=
  fun i j => (h i j).add_right (h' i j)

lemma free_neg {c : S} {b : SlopeTestRemainingChoices S A} (h : FreeOf c b) : FreeOf c (-b) :=
  fun i j => (h i j).neg_right

lemma free_smul {c : S} {b : SlopeTestRemainingChoices S A} (k : ℂ) (h : FreeOf c b) : FreeOf c (k • b) :=
  fun i j => (h i j).smul_right k

lemma free_pow {c : S} {b : SlopeTestRemainingChoices S A} (h : FreeOf c b) (n : ℕ) : FreeOf c (b ^ n) :=
  fun i j => (h i j).pow_right n

lemma free_star {c : S} {b : SlopeTestRemainingChoices S A} (h : FreeOf c b) : FreeOf c (star b) := by
  intro i j
  have := (h j i).star_star
  rwa [star_eU] at this

lemma freeOf2_of_entries {c : S} {p q r s : SlopeTestRemainingChoices S A} (hp : FreeOf c p) (hq : FreeOf c q) (hr : FreeOf c r)
    (hs : FreeOf c s) : FreeOf2 c !![p, q; r, s] := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [hp, hq, hr, hs]

lemma comm_lit {w p q r s : SlopeTestRemainingChoices S A} (hp : Commute w p) (hq : Commute w q) (hr : Commute w r)
    (hs : Commute w s) : ∀ i j, Commute w ((!![p, q; r, s] : M2 (SlopeTestRemainingChoices S A)) i j) := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [hp, hq, hr, hs]

lemma freeOf2_mul {c : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) (hN : FreeOf2 c N) :
    FreeOf2 c (M * N) := by
  intro i j k l
  rw [Matrix.mul_apply]
  exact Commute.sum_right _ _ _ fun m _ => (hM i m k l).mul_right (hN m j k l)

lemma ins_comm_ins {a : S} {M N : M2 (SlopeTestRemainingChoices S A)} (fM : FreeOf2 a M) (fN : FreeOf2 a N) (h : M * N = N * M) :
    Commute (ins a M) (ins a N) := by
  show ins a M * ins a N = ins a N * ins a M
  rw [← ins_mul a M N fM, ← ins_mul a N M fN, h]

lemma comm_mul_ins {a : S} {u v : SlopeTestRemainingChoices S A} {M N : M2 (SlopeTestRemainingChoices S A)} (fu : FreeOf a u) (fv : FreeOf a v)
    (fM : FreeOf2 a M) (fN : FreeOf2 a N) (huv : Commute u v) (huN : ∀ i j, Commute u (N i j))
    (hvM : ∀ i j, Commute v (M i j)) (hMN : M * N = N * M) : Commute (u * ins a M) (v * ins a N) :=
  Commute.mul_left (huv.mul_right (ins_comm a N u fu huN))
    ((ins_comm a M v fv hvM).symm.mul_right (ins_comm_ins fM fN hMN))

lemma comm_mul_ins_one {a : S} {u w : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)} (fw : FreeOf a w) (huw : Commute u w)
    (hwM : ∀ i j, Commute w (M i j)) : Commute (u * ins a M) w :=
  Commute.mul_left huw (ins_comm a M w fw hwM).symm

lemma inv_mul_ins {a : S} {u ui : SlopeTestRemainingChoices S A} {M Mi : M2 (SlopeTestRemainingChoices S A)} (fui : FreeOf a ui) (fM : FreeOf2 a M)
    (h : u * ui = 1) (hc : ∀ i j, Commute ui (M i j)) (hM : M * Mi = 1) :
    u * ins a M * (ui * ins a Mi) = 1 := by
  calc u * ins a M * (ui * ins a Mi) = u * (ins a M * ui) * ins a Mi := by simp only [mul_assoc]
    _ = u * (ui * ins a M) * ins a Mi := by rw [(ins_comm a M ui fui hc).eq]
    _ = (u * ui) * (ins a M * ins a Mi) := by simp only [mul_assoc]
    _ = 1 := by rw [h, one_mul, ← ins_mul a M Mi fM, hM, ins_one]

lemma star_mul_ins {a : S} {u : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)} (fu : FreeOf a u) (fM : FreeOf2 a M)
    (hu : star u = u) (hc : ∀ i j, Commute u (M i j)) (hM : Mᴴ = M) : star (u * ins a M) = u * ins a M := by
  rw [star_mul, ins_star a M fM, hM, hu, (ins_comm a M u fu hc).eq]

lemma diag_mul (p s p' s' : SlopeTestRemainingChoices S A) :
    (!![p, 0; 0, s] * !![p', 0; 0, s'] : M2 (SlopeTestRemainingChoices S A)) = !![p * p', 0; 0, s * s'] := by
  simp

lemma diag_star (p s : SlopeTestRemainingChoices S A) : (!![p, 0; 0, s] : M2 (SlopeTestRemainingChoices S A))ᴴ = !![star p, 0; 0, star s] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

lemma diag_one : (!![1, 0; 0, 1] : M2 (SlopeTestRemainingChoices S A)) = 1 := Matrix.one_fin_two.symm

lemma Rht0_mul_10 (b : S) (d : ℂ) (M : M2 (SlopeTestRemainingChoices S A)) :
    (Rht0 b d * M : M2 (SlopeTestRemainingChoices S A)) 1 0 = (d - 1)⁻¹ • ins b !![d • M 1 0, 0; -M 0 0, (d - 1) • M 1 0] := by
  have h := sum_eU_diag (A := A) b
  rw [Fin.sum_univ_two] at h
  have h0 : (eU b 0 0 : SlopeTestRemainingChoices S A) = 1 - eU b 1 1 := eq_sub_of_add_eq h
  unfold Rht0 ins Q0
  rw [Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply]
  congr 1
  simp only [Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply_eq]
  simp [h0, sub_mul, mul_sub, sub_smul]
  module

section Frame

variable {r : ℕ} (L : LevelData A r) (f : FrameData S A)

lemma free_l {b : S} (h : f.Free b) (Y : ℂ) : FreeOf b (f.l L Y) :=
  free_add (free_io b _) (free_mul (free_io b _) (h.2.2.2.2.2.2.2.2 Y))

lemma free_m {b : S} (h : f.Free b) (Y : ℂ) : FreeOf b (f.m L Y) :=
  free_mul (free_mul (free_mul h.2.2.2.2.2.2.2.1 (free_pow (free_io b _) _)) (free_star (free_l L f h _)))
    (free_mul (free_pow (free_io b _) _) h.2.2.2.2.2.2.1)

lemma tri_mul (m : SlopeTestRemainingChoices S A) :
    (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * m, io L.GG]) *
      (!![1, 0; -m, io L.GGi] * !![io L.ζb, 0; 0, io L.ζ]) = (1 : M2 (SlopeTestRemainingChoices S A)) := by
  have h1 : (!![1, 0; io L.GG * m, io L.GG] * !![1, 0; -m, io L.GGi] : M2 (SlopeTestRemainingChoices S A)) = 1 := by
    rw [Matrix.mul_fin_two, ← diag_one]
    simp [← io_mul, L.GG_GGi, io_one]
  calc _ = !![io L.ζbi, 0; 0, io L.ζi] * ((!![1, 0; io L.GG * m, io L.GG] * !![1, 0; -m, io L.GGi]) *
        !![io L.ζb, 0; 0, io L.ζ]) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.one_mul, diag_mul, ← io_mul, ← io_mul, L.ζbi_ζb, L.ζi_ζ, io_one, diag_one]

lemma tri_mul' (m : SlopeTestRemainingChoices S A) :
    (!![1, 0; -m, io L.GGi] * !![io L.ζb, 0; 0, io L.ζ]) *
      (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * m, io L.GG]) = (1 : M2 (SlopeTestRemainingChoices S A)) := by
  have h1 : (!![1, 0; -m, io L.GGi] * !![1, 0; io L.GG * m, io L.GG] : M2 (SlopeTestRemainingChoices S A)) = 1 := by
    rw [Matrix.mul_fin_two, ← diag_one]
    simp [← mul_assoc, ← io_mul, L.GGi_GG, io_one]
  calc _ = !![1, 0; -m, io L.GGi] * ((!![io L.ζb, 0; 0, io L.ζ] * !![io L.ζbi, 0; 0, io L.ζi]) *
        !![1, 0; io L.GG * m, io L.GG]) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [diag_mul, ← io_mul, ← io_mul, L.ζb_ζbi, L.ζ_ζi, io_one, diag_one, Matrix.one_mul, h1]

end Frame

lemma freeOf2_diag_scalar (b : S) (α : ℂ) : FreeOf2 b (!![α • 1, 0; 0, 1] : M2 (SlopeTestRemainingChoices S A)) :=
  freeOf2_of_entries (free_smul _ (free_one b)) (free_zero b) (free_zero b) (free_one b)

lemma comm_sc (w : SlopeTestRemainingChoices S A) (α : ℂ) : ∀ i j, Commute w ((!![α • 1, 0; 0, 1] : M2 (SlopeTestRemainingChoices S A)) i j) :=
  comm_lit ((Commute.one_right w).smul_right α) (Commute.zero_right w) (Commute.zero_right w)
    (Commute.one_right w)

lemma sc_comm_diag (α : ℂ) (p s : SlopeTestRemainingChoices S A) :
    (!![α • 1, 0; 0, 1] * !![p, 0; 0, s] : M2 (SlopeTestRemainingChoices S A)) = !![p, 0; 0, s] * !![α • 1, 0; 0, 1] := by
  rw [diag_mul, diag_mul]
  simp

lemma lit_congr {p q r s p' q' r' s' : SlopeTestRemainingChoices S A} (hp : p = p') (hq : q = q') (hr : r = r') (hs : s = s') :
    (!![p, q; r, s] : M2 (SlopeTestRemainingChoices S A)) = !![p', q'; r', s'] := by
  rw [hp, hq, hr, hs]

lemma sc_inv {α β : ℂ} (h : α * β = 1) :
    (!![α • 1, 0; 0, 1] * !![β • 1, 0; 0, 1] : M2 (SlopeTestRemainingChoices S A)) = 1 := by
  rw [diag_mul, ← diag_one]
  simp [smul_smul, mul_comm β α, h]

theorem minusStep_of (hLM : LetterMinus) (hRTT : RTTEntries) (hForm : MinusForm) (hTau : MinusTau)
    (hL : MinusL) : MinusStep := by
  intro A S _ _ _ _ _ _ r L f b Yb h
  obtain ⟨hSL, hF, hFree, hYb, hb, hb1, hbm, hq⟩ := h
  have hFree' := hFree
  obtain ⟨fRR, fTT, fF, fFi, fx, fxi, fc, fci, fee⟩ := hFree
  obtain ⟨xb1, xb2⟩ := hF.x_xi Yb hb
  obtain ⟨xm1, xm2⟩ := hF.x_xi (Yb - 1) hbm
  have hYm : star (Yb - 1) = Yb - 1 := by rw [star_sub, hYb, star_one]

  have fC : FreeOf2 b (!![f.q (Yb - 1) • f.xi (Yb - 1), 0; 0, f.x Yb] : M2 (SlopeTestRemainingChoices S A)) :=
    freeOf2_of_entries (free_smul _ (fxi _)) (free_zero b) (free_zero b) (fx _)
  have fCi : FreeOf2 b (!![(f.q (Yb - 1))⁻¹ • f.x (Yb - 1), 0; 0, f.xi Yb] : M2 (SlopeTestRemainingChoices S A)) :=
    freeOf2_of_entries (free_smul _ (fx _)) (free_zero b) (free_zero b) (fxi _)
  have cC : ∀ w : SlopeTestRemainingChoices S A, (∀ Y, Commute (f.x Y) w) →
      ∀ i j, Commute w ((!![f.q (Yb - 1) • f.xi (Yb - 1), 0; 0, f.x Yb] : M2 (SlopeTestRemainingChoices S A)) i j) := fun w hw =>
    comm_lit ((comm_inv xm1 xm2 (hw _)).symm.smul_right _) (Commute.zero_right w) (Commute.zero_right w)
      (hw _).symm
  have cCi : ∀ w : SlopeTestRemainingChoices S A, (∀ Y, Commute (f.x Y) w) →
      ∀ i j, Commute w ((!![(f.q (Yb - 1))⁻¹ • f.x (Yb - 1), 0; 0, f.xi Yb] : M2 (SlopeTestRemainingChoices S A)) i j) := fun w hw =>
    comm_lit ((hw _).symm.smul_right _) (Commute.zero_right w) (Commute.zero_right w)
      (comm_inv xb1 xb2 (hw _)).symm
  have x_ci : ∀ Y, Commute (f.x Y) f.ci := fun Y => (comm_inv hF.c_ci.1 hF.c_ci.2 (hF.x_c Y).symm).symm
  have fE : FreeOf2 b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG] : M2 (SlopeTestRemainingChoices S A)) :=
    freeOf2_mul (freeOf2_of_entries (free_io b _) (free_zero b) (free_zero b) (free_io b _))
      (freeOf2_of_entries (free_one b) (free_zero b) (free_mul (free_io b _) (free_m L f hFree' _)) (free_io b _))
  have fEi : FreeOf2 b (!![1, 0; -f.m L Yb, io L.GGi] * !![io L.ζb, 0; 0, io L.ζ] : M2 (SlopeTestRemainingChoices S A)) :=
    freeOf2_mul (freeOf2_of_entries (free_one b) (free_zero b) (free_neg (free_m L f hFree' _)) (free_io b _))
      (freeOf2_of_entries (free_io b _) (free_zero b) (free_zero b) (free_io b _))
  refine
    { module := hLM ℂ A S f.reg f.RR f.TT f.q b Yb hF.module fRR fTT (hF.inv_reg hb) hYb
      lowerLeftEntry_commute := ?_
      inv_reg := fun Y hY => ⟨hF.inv_reg hY.1, hY.2.2⟩
      F_Fi := ?_
      Fi_F := ?_
      x_xi := ?_
      c_ci := ⟨?_, ?_⟩
      x_commute := ?_
      x_c := ?_
      x_fn := ?_
      x_nab := ?_
      c_fn := ?_
      x_star := ?_
      c_star := ?_
      ee_fn := ?_
      form := hForm A S r L f b Yb ⟨hSL, hF, hFree', hYb, hb, hb1, hbm, hq⟩
      frame_τ := hTau A S r L f b Yb ⟨hSL, hF, hFree', hYb, hb, hb1, hbm, hq⟩
      frame_l := hL A S r L f b Yb ⟨hSL, hF, hFree', hYb, hb, hb1, hbm, hq⟩ }
  ·
    intro Y hY Y' hY'
    show Commute ((Rht0 b (Yb - Y) * f.TT Y : M2 (SlopeTestRemainingChoices S A)) 1 0) ((Rht0 b (Yb - Y') * f.TT Y' : M2 (SlopeTestRemainingChoices S A)) 1 0)
    by_cases hne : Y = Y'
    · subst hne; exact Commute.refl _
    rw [Rht0_mul_10, Rht0_mul_10]
    refine (Commute.smul_right ?_ _).smul_left _
    have ht := hF.lowerLeftEntry_commute Y hY.1 Y' hY'.1
    have r1 := hRTT ℂ (SlopeTestRemainingChoices S A) f.TT Y' Y (hF.module.rtt Y' hY'.1 Y hY.1) 0 0 1 0
    have r2 := hRTT ℂ (SlopeTestRemainingChoices S A) f.TT Y Y' (hF.module.rtt Y hY.1 Y' hY'.1) 0 0 1 0
    refine ins_comm_ins
      (freeOf2_of_entries (free_smul _ (fTT _ _ _)) (free_zero b) (free_neg (fTT _ _ _)) (free_smul _ (fTT _ _ _)))
      (freeOf2_of_entries (free_smul _ (fTT _ _ _)) (free_zero b) (free_neg (fTT _ _ _)) (free_smul _ (fTT _ _ _))) ?_
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    have e10 := t21_commutator_identity (f.TT Y 0 0) (f.TT Y 1 0) (f.TT Y' 0 0) (f.TT Y' 1 0) Y Y' Yb hne r1 r2
    refine lit_congr ?_ (by simp) e10 ?_
    · simp only [zero_mul, add_zero]
      exact ((ht.smul_left _).smul_right _).eq
    · simp only [mul_zero, zero_add]
      exact ((ht.smul_left _).smul_right _).eq
  · show ins b _ * f.F * (f.Fi * ins b _) = 1
    calc _ = ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * (f.F * f.Fi) *
          ins b (!![1, 0; -f.m L Yb, io L.GGi] * !![io L.ζb, 0; 0, io L.ζ]) := by simp only [mul_assoc]
      _ = 1 := by rw [hF.F_Fi, mul_one, ← ins_mul b _ _ fE, tri_mul, ins_one]
  · show f.Fi * ins b _ * (ins b _ * f.F) = 1
    calc _ = f.Fi * (ins b (!![1, 0; -f.m L Yb, io L.GGi] * !![io L.ζb, 0; 0, io L.ζ]) *
          ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG])) * f.F := by
            simp only [mul_assoc]
      _ = 1 := by rw [← ins_mul b _ _ fEi, tri_mul', ins_one, mul_one, hF.Fi_F]
  · rintro Y ⟨hYi, h0, h1⟩
    obtain ⟨a1, a2⟩ := hF.x_xi Y hYi
    have h0' : Yb - Y ≠ 0 := h0
    have h1' : Yb - Y - 1 ≠ 0 := sub_ne_zero.mpr h1
    exact ⟨inv_mul_ins (fxi Y) (freeOf2_diag_scalar b _) a1 (comm_sc _ _) (sc_inv (by field_simp)),
      inv_mul_ins (fx Y) (freeOf2_diag_scalar b _) a2 (comm_sc _ _) (sc_inv (by field_simp))⟩
  · refine inv_mul_ins fci fC hF.c_ci.1 (cC f.ci x_ci) ?_
    rw [diag_mul, ← diag_one, xb1, smul_mul_smul_comm, xm2, mul_inv_cancel₀ hq, one_smul]
  · refine inv_mul_ins fc fCi hF.c_ci.2 (cCi f.c hF.x_c) ?_
    rw [diag_mul, ← diag_one, xb2, smul_mul_smul_comm, xm1, inv_mul_cancel₀ hq, one_smul]
  · intro Y Y'
    exact comm_mul_ins (fx Y) (fx Y') (freeOf2_diag_scalar b _) (freeOf2_diag_scalar b _) (hF.x_commute Y Y') (comm_sc _ _) (comm_sc _ _)
      (sc_comm_diag _ _ _)
  · intro Y
    exact comm_mul_ins (fx Y) fc (freeOf2_diag_scalar b _) fC (hF.x_c Y) (cC (f.x Y) (fun Y' => hF.x_commute Y' Y)) (comm_sc _ _)
      (sc_comm_diag _ _ _)
  · intro Y g hg
    exact comm_mul_ins_one (free_io b g) (hF.x_fn Y g hg) (comm_sc _ _)
  · intro Y
    exact comm_mul_ins_one (free_io b _) (hF.x_nab Y) (comm_sc _ _)
  · intro g hg
    exact comm_mul_ins_one (free_io b g) (hF.c_fn g hg) (cC (io g) (fun Y => hF.x_fn Y g hg))
  · intro Y hY
    refine star_mul_ins (fx Y) (freeOf2_diag_scalar b _) (hF.x_star Y hY) (comm_sc _ _) ?_
    rw [diag_star, star_smul, star_one, star_div₀, star_sub, star_sub, star_sub, hY, hYb, star_one]
  · refine star_mul_ins fc fC hF.c_star (cC f.c hF.x_c) ?_
    rw [diag_star, star_smul, hF.module.q_real _ hYm, star_inv xm1 (hF.x_star _ hYm), hF.x_star _ hYb]
  · intro Y g hg
    have gx : ∀ Y, Commute (io g) (f.x Y) := fun Y => (hF.x_fn Y g hg).symm
    have gb : Commute (io g) (f.xi Yb) := (comm_inv xb1 xb2 (hF.x_fn Yb g hg)).symm
    have gm : Commute (io g) (f.xi (Yb - 1)) := (comm_inv xm1 xm2 (hF.x_fn (Yb - 1) g hg)).symm
    have ge : ∀ Y, Commute (io g) (f.ee Y) := fun Y => (hF.ee_fn Y g hg).symm
    have gD : Commute (io g) (f.DD Y Yb) := ((ge Y).sub_right (ge Yb)).smul_right _
    have gt : Commute (io g : SlopeTestRemainingChoices S A) (tz L) := by
      have hz : L.ζbi ∈ zfns L := by simp [zfns]
      refine io_comm ?_
      rw [mul_smul_comm, smul_mul_assoc, L.fns_comm g (Or.inr hg) L.ζbi (Or.inr hz)]
    exact (ins_comm b _ (io g) (free_io b g) (comm_lit (ge Y) (Commute.zero_right _)
      ((gb.mul_right gm).smul_right _).neg_right
      ((((gb.mul_right (ge Y)).mul_right (gx Yb)).sub_right gD).add_right gt))).symm

end Formalism.FourierDecayAlt.P.Fr10

namespace Formalism.FourierDecayAlt.P

theorem minus_letter_frame_of_data : Formalism.FourierDecayAlt.Fr.MinusAssemble :=
  fun _ _ _ _ hLM hRTT hForm hTau hL => Fr10.minusStep_of hLM hRTT hForm hTau hL

end Formalism.FourierDecayAlt.P
