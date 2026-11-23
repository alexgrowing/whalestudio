import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
import Formalism.HermitianCurvature.StatementTL

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.PBF

section slots

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {n r : ℕ}

theorem liftM_star (M : SlopeTestRemainingChoices (Fin n) A) : liftM (star M) = star (liftM M) := by
  ext z z'
  simp only [Matrix.star_apply, liftM_apply]
  by_cases h : z 0 = z' 0
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem liftM_neg (M : SlopeTestRemainingChoices (Fin n) A) : liftM (-M) = -liftM M := by
  rw [← liftRingHom_apply_eq_liftM, map_neg, liftRingHom_apply_eq_liftM]

theorem liftM_sub (M N : SlopeTestRemainingChoices (Fin n) A) : liftM (M - N) = liftM M - liftM N := by
  rw [← liftRingHom_apply_eq_liftM, map_sub, liftRingHom_apply_eq_liftM, liftRingHom_apply_eq_liftM]

theorem liftM_pow (M : SlopeTestRemainingChoices (Fin n) A) (m : ℕ) : liftM (M ^ m) = liftM M ^ m := by
  rw [← liftRingHom_apply_eq_liftM, map_pow, liftRingHom_apply_eq_liftM]

theorem matrix_two_map_lift (a b c d : SlopeTestRemainingChoices (Fin n) A) :
    (!![a, b; c, d] : M2 (SlopeTestRemainingChoices (Fin n) A)).map liftM = !![liftM a, liftM b; liftM c, liftM d] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

structure Lifted (f : FrameData (Fin n) A) (f' : FrameData (Fin (n + 1)) A) : Prop where
  F : f'.F = liftM f.F
  ee : ∀ Y, f'.ee Y = liftM (f.ee Y)
  x : ∀ Y, f'.x Y = liftM (f.x Y)
  xi : ∀ Y, f'.xi Y = liftM (f.xi Y)
  c : f'.c = liftM f.c
  ci : f'.ci = liftM f.ci
  q : f'.q = f.q
  N : f'.N = f.N

variable (L : LevelData A r)

theorem io_lift (x : A) : (io x : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (io x) := io_succ x

theorem lifted_l {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y : ℂ) :
    f'.l L Y = liftM (f.l L Y) := by
  simp only [FrameData.l, kapL, liftM_add, liftM_mul, hf.ee Y, io_lift]

theorem lifted_m {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y : ℂ) :
    f'.m L Y = liftM (f.m L Y) := by
  simp only [FrameData.m, FrameData.d, FrameData.di, wt, wti, liftM_mul, liftM_pow, hf.N, hf.c, hf.ci,
    lifted_l L hf, liftM_star, io_lift]

theorem lifted_DD {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y Ya : ℂ) :
    f'.DD Y Ya = liftM (f.DD Y Ya) := by
  simp only [FrameData.DD, liftM_smul, liftM_sub, hf.ee]

theorem tz_lift : (tz L : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (tz L) := io_succ _

theorem lifted_plus {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (a : Fin n)
    (Ya : ℂ) : Lifted (f.plus L a Ya) (f'.plus L a.succ Ya) := by
  refine ⟨?_, fun Y => ?_, fun Y => ?_, fun Y => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [FrameData.plus]
    rw [hf.F, liftM_mul, ← ins_succ, map_mul_liftM, matrix_two_map_lift, matrix_two_map_lift, lifted_l L hf]
    simp only [liftM_mul, liftM_zero, liftM_one, io_lift]
  · simp only [FrameData.plus]
    rw [← ins_succ, matrix_two_map_lift]
    simp only [liftM_add, liftM_sub, liftM_mul, liftM_neg, liftM_smul, liftM_zero, liftM_one, hf.ee, hf.x, hf.xi,
      lifted_DD hf, tz_lift]
  · simp only [FrameData.plus]
    rw [hf.x, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.plus]
    rw [hf.xi, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.plus]
    rw [hf.c, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.plus]
    rw [hf.ci, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.plus, hf.q]
  · simp only [FrameData.plus, hf.N]

theorem lifted_minus {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (b : Fin n)
    (Yb : ℂ) : Lifted (f.minus L b Yb) (f'.minus L b.succ Yb) := by
  refine ⟨?_, fun Y => ?_, fun Y => ?_, fun Y => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [FrameData.minus]
    rw [hf.F, liftM_mul, ← ins_succ, map_mul_liftM, matrix_two_map_lift, matrix_two_map_lift, lifted_m L hf]
    simp only [liftM_mul, liftM_zero, liftM_one, io_lift]
  · simp only [FrameData.minus]
    rw [← ins_succ, matrix_two_map_lift]
    simp only [liftM_add, liftM_sub, liftM_mul, liftM_neg, liftM_smul, liftM_zero, liftM_one, hf.ee, hf.x, hf.xi,
      hf.q, lifted_DD hf, tz_lift]
  · simp only [FrameData.minus]
    rw [hf.x, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.minus]
    rw [hf.xi, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.minus]
    rw [hf.c, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.minus]
    rw [hf.ci, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.minus, hf.q]
  · simp only [FrameData.minus, hf.N]

theorem lifted_ofWord (st : Start A) :
    ∀ u : List (Letter ℂ (Fin n)), Lifted (ofWord L st u) (ofWord L st (u.map upL))
  | [] => ⟨by simp [ofWord, Start.frame, liftM_one], fun Y => io_succ _, fun Y => io_succ _, fun Y => io_succ _,
      by simp [ofWord, Start.frame, liftM_one], by simp [ofWord, Start.frame, liftM_one], rfl, rfl⟩
  | l :: u => by
    have ih := lifted_ofWord st u
    rw [List.map_cons]
    by_cases hp : l.plus
    · have e1 : ofWord L st (l :: u) = (ofWord L st u).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      have e2 : ofWord L st (upL l :: u.map upL) = (ofWord L st (u.map upL)).plus L l.intersection_update_fsHerm_neg_one.succ l.pt := by
        simp [ofWord, upL, hp]
      rw [e1, e2]
      exact lifted_plus L ih l.intersection_update_fsHerm_neg_one l.pt
    · have e1 : ofWord L st (l :: u) = (ofWord L st u).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      have e2 : ofWord L st (upL l :: u.map upL) = (ofWord L st (u.map upL)).minus L l.intersection_update_fsHerm_neg_one.succ l.pt := by
        simp [ofWord, upL, hp]
      rw [e1, e2]
      exact lifted_minus L ih l.intersection_update_fsHerm_neg_one l.pt

theorem bT_lift (σ : Site A) : ∀ u : List (Letter ℂ (Fin n)), bT σ (u.map upL) = liftM (bT σ u)
  | [] => by simp [bT, liftM_one]
  | l :: u => by
    rw [List.map_cons, bT, bT, bT_lift σ u, liftM_mul]
    congr 1
    show ins l.intersection_update_fsHerm_neg_one.succ (lift0 (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star)) =
      liftM (ins l.intersection_update_fsHerm_neg_one (lift0 (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star)))
    rw [liftZero_succ_eq_map, ins_succ]

theorem bTA_lift (u : List (Letter ℂ (Fin n))) : TL.bTA L (u.map upL) = liftM (TL.bTA L u) := by
  simp only [TL.bTA, bT_lift]
  rw [← liftRingHom_apply_eq_liftM, map_list_prod, List.map_map]
  rfl

end slots

end Formalism.FourierDecayAlt.P.PBN
