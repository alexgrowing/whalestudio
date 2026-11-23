import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QEFirstMulSecondEqSwap

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

namespace Formalism.FourierDecayAlt.P.Fr5

section Core

variable {B : Type} [Ring B] [StarRing B] [Algebra ℂ B]

lemma comm_inv {x xi g : B} (h1 : x * xi = 1) (h2 : xi * x = 1) (h : Commute x g) : Commute xi g := by
  show xi * g = g * xi
  calc xi * g = xi * g * (x * xi) := by rw [h1, mul_one]
    _ = xi * (x * g) * xi := by rw [h.eq]; simp only [mul_assoc]
    _ = g * xi := by rw [← mul_assoc xi x g, h2, one_mul]

lemma core (F Fi d τ τi τ' τi' l RR T00 T01 T10 T11 U10 U11 : B) (q : ℂ)
    (hRR : RR = star F * d * F) (hF : F * Fi = 1) (hF' : Fi * F = 1)
    (hdτ : star (d * τ) = d * τ) (hτ : τi * τ = 1) (hτ1 : τ' * τi' = 1) (hτ2 : τi' * τ' = 1)
    (h11 : F * T11 = τ * F) (h10 : F * T10 = τ * l * F) (hU : F * U11 = τ' * F)
    (herm : star (RR * T10) = RR * T01)
    (quantum_determinant_shifted : T00 * U11 - T01 * U10 = q • (1 : B)) (upper_block_det_one : T10 * U11 = T11 * U10) :
    RR * T11 = star F * (d * τ) * F ∧ RR * T10 = star F * (d * τ * l) * F ∧
      RR * T01 = star F * (star l * (d * τ)) * F ∧
      RR * T00 = star F * (q • (d * τi') + star l * (d * τ) * l) * F := by
  have hFl : ∀ X : B, X * F * Fi = X := fun X => by rw [mul_assoc, hF, mul_one]
  have h3l : ∀ X : B, X * τ' * τi' = X := fun X => by rw [mul_assoc, hτ1, mul_one]
  have hT11 : RR * T11 = star F * (d * τ) * F := by
    rw [hRR, mul_assoc (star F * d) F T11, h11]
    simp only [mul_assoc]
  have hT10 : RR * T10 = star F * (d * τ * l) * F := by
    rw [hRR, mul_assoc (star F * d) F T10, h10]
    simp only [mul_assoc]
  have hT01 : RR * T01 = star F * (star l * (d * τ)) * F := by
    rw [← herm, hT10, star_mul, star_mul, star_star, star_mul, hdτ]
    simp only [mul_assoc]
  have hU11 : U11 = Fi * τ' * F := by
    calc U11 = Fi * F * U11 := by rw [hF', one_mul]
      _ = Fi * τ' * F := by rw [mul_assoc Fi F U11, hU, ← mul_assoc]
  have hUi : U11 * (Fi * τi' * F) = 1 := by
    rw [hU11]
    simp only [← mul_assoc, hFl, h3l, hF']
  have hFU10 : F * U10 = l * F * U11 := by
    have e : τ * (F * U10) = τ * (l * F * U11) := by
      calc τ * (F * U10) = F * T11 * U10 := by rw [h11, mul_assoc]
        _ = F * T10 * U11 := by rw [mul_assoc F T11 U10, ← upper_block_det_one, ← mul_assoc]
        _ = τ * (l * F * U11) := by rw [h10]; simp only [mul_assoc]
    calc F * U10 = τi * τ * (F * U10) := by rw [hτ, one_mul]
      _ = τi * (τ * (l * F * U11)) := by rw [mul_assoc τi τ (F * U10), e]
      _ = l * F * U11 := by rw [← mul_assoc τi τ, hτ, one_mul]
  have e2 : T00 * U11 = q • (1 : B) + T01 * U10 := by rw [← quantum_determinant_shifted, sub_add_cancel]
  have hT00 : T00 = (q • (1 : B) + T01 * U10) * (Fi * τi' * F) := by
    calc T00 = T00 * (U11 * (Fi * τi' * F)) := by rw [hUi, mul_one]
      _ = (q • (1 : B) + T01 * U10) * (Fi * τi' * F) := by rw [← mul_assoc T00, e2]
  have hA : RR * (q • (1 : B)) * (Fi * τi' * F) = star F * (q • (d * τi')) * F := by
    rw [mul_smul_comm, mul_one, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, hRR]
    congr 1
    simp only [← mul_assoc, hFl]
  have hB : RR * (T01 * U10) * (Fi * τi' * F) = star F * (star l * (d * τ) * l) * F := by
    rw [← mul_assoc RR T01 U10, hT01, mul_assoc (star F * (star l * (d * τ))) F U10, hFU10,
      mul_assoc (star F * (star l * (d * τ))) (l * F * U11), mul_assoc (l * F) U11, hUi, mul_one]
    simp only [mul_assoc]
  refine ⟨hT11, hT10, hT01, ?_⟩
  rw [hT00, ← mul_assoc RR, mul_add, add_mul, hA, hB, mul_add, add_mul]

end Core

section Slots

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]

lemma io_mul (x y : A) : (io (x * y) : SlopeTestRemainingChoices S A) = io x * io y := by
  first
  | exact map_mul (Matrix.scalar (Ix S)) x y
  | simp [io]

lemma io_one : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := by
  first
  | exact map_one (Matrix.scalar (Ix S))
  | simp [io]

lemma io_star (x : A) : star (io x : SlopeTestRemainingChoices S A) = io (star x) := by
  first
  | exact Matrix.diagonal_conjTranspose (fun _ : Ix S => x)
  | (show star (Matrix.scalar (Ix S) x) = Matrix.scalar (Ix S) (star x)
     simp [Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]; rfl)

lemma io_comm {x y : A} (h : x * y = y * x) : Commute (io x : SlopeTestRemainingChoices S A) (io y) := by
  show (io x : SlopeTestRemainingChoices S A) * io y = io y * io x
  rw [← io_mul, ← io_mul, h]

private lemma mul_scalar_comm_of_entries_zero_or_one {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n A) (x : A)
    (hM : ∀ k l, M k l = 0 ∨ M k l = 1) : M * Matrix.scalar n x = Matrix.scalar n x * M := by
  ext k l
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases hM k l with h | h <;> rw [h] <;> simp

lemma free_io (a : S) (x : A) : FreeOf a (io x : SlopeTestRemainingChoices S A) := by
  intro i j
  exact mul_scalar_comm_of_entries_zero_or_one (eU a i j) x (fun k l => by
    first
    | (simp only [eU, Matrix.of_apply]; split_ifs <;> simp)
    | (rw [eU]; simp only [Matrix.of_apply]; split_ifs <;> simp))

lemma free_mul {a : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x * y) := fun i j => (hx i j).mul_right (hy i j)

lemma free_add {a : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x + y) := fun i j => (hx i j).add_right (hy i j)

lemma free_smul {a : S} (c : ℂ) {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) : FreeOf a (c • x) := fun i j => (hx i j).smul_right c

lemma free_zero (a : S) : FreeOf a (0 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.zero_right _

lemma free_one (a : S) : FreeOf a (1 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.one_right _

lemma free_pow {a : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (n : ℕ) : FreeOf a (x ^ n) := fun i j => (hx i j).pow_right n

private lemma star_eU_eq_eU_swap (a : S) (i j : Fin 2) : star (eU a i j : SlopeTestRemainingChoices S A) = eU a j i := by
  have key : ∀ k l : Ix S, star ((eU a i j : SlopeTestRemainingChoices S A) l k) = (eU a j i : SlopeTestRemainingChoices S A) k l := by
    intro k l
    simp only [eU, Matrix.of_apply]
    by_cases h1 : l a = i ∧ k a = j ∧ ∀ b, b ≠ a → l b = k b
    · have h2 : k a = j ∧ l a = i ∧ ∀ b, b ≠ a → k b = l b :=
        ⟨h1.2.1, h1.1, fun b hb => (h1.2.2 b hb).symm⟩
      rw [if_pos h1, if_pos h2, star_one]
    · have h2 : ¬ (k a = j ∧ l a = i ∧ ∀ b, b ≠ a → k b = l b) :=
        fun h => h1 ⟨h.2.1, h.1, fun b hb => (h.2.2 b hb).symm⟩
      rw [if_neg h1, if_neg h2, star_zero]
  exact Matrix.ext key

lemma free_star {a : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) : FreeOf a (star x) := by
  intro i j
  have e1 : star (eU a j i : SlopeTestRemainingChoices S A) = eU a i j := star_eU_eq_eU_swap a j i
  first
  | (have h3 := (hx j i).star_star
     rw [e1] at h3
     exact h3)
  | (show eU a i j * star x = star x * eU a i j
     rw [← e1, ← star_mul, ← star_mul, (hx j i).eq])

lemma freeOf2_of_four_entries {a : S} {x y z w : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) (hz : FreeOf a z)
    (hw : FreeOf a w) : FreeOf2 a !![x, y; z, w] := by
  intro i j
  fin_cases i <;> fin_cases j <;> first | exact hx | exact hy | exact hz | exact hw | simp [hx, hy, hz, hw]

private lemma d0_eq_diagonal (b : SlopeTestRemainingChoices S A) : d0 b = !![b, 0; 0, b] := by
  first
  | (refine Matrix.ext fun i j => ?_
     fin_cases i <;> fin_cases j <;> rfl)
  | (refine Matrix.ext fun i j => ?_
     fin_cases i <;> fin_cases j <;> simp [d0])

lemma gauss_entries (Fs dd ls l p t F : SlopeTestRemainingChoices S A) :
    d0 Fs * !![1, ls; 0, 1] * d0 dd * !![p, 0; 0, t] * !![1, 0; l, 1] * d0 F =
      !![Fs * (dd * p + ls * (dd * t) * l) * F, Fs * (ls * (dd * t)) * F;
        Fs * (dd * t * l) * F, Fs * (dd * t) * F] := by
  first
  | (simp only [d0_eq_diagonal, Matrix.mul_fin_two, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add,
      mul_add, add_mul, mul_assoc]; done)
  | (refine Matrix.ext fun i j => ?_
     fin_cases i <;> fin_cases j <;>
       simp [d0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, mul_add, add_mul, mul_assoc])

lemma lam_conj (l : SlopeTestRemainingChoices S A) : (!![1, 0; l, 1] : M2 (SlopeTestRemainingChoices S A))ᴴ = !![1, star l; 0, 1] := by
  first
  | (refine Matrix.ext fun i j => ?_
     fin_cases i <;> fin_cases j <;> simp)
  | (ext i j; fin_cases i <;> fin_cases j <;> simp)

lemma diag_conj (x y : SlopeTestRemainingChoices S A) : (!![x, 0; 0, y] : M2 (SlopeTestRemainingChoices S A))ᴴ = !![star x, 0; 0, star y] := by
  first
  | (refine Matrix.ext fun i j => ?_
     fin_cases i <;> fin_cases j <;> simp)
  | (ext i j; fin_cases i <;> fin_cases j <;> simp)

end Slots

section Level

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

lemma fn_comm (L : LevelData A r) {g h : A} (hg : g ∈ zfns L) (hh : h ∈ zfns L) : g * h = h * g := by
  first
  | exact L.16 g (Set.mem_union_right _ hg) h (Set.mem_union_right _ hh)
  | exact L.16 g (Or.inr hg) h (Or.inr hh)

lemma mem_ζ (L : LevelData A r) : L.ζ ∈ zfns L := by
  simp [zfns]
lemma mem_ζi (L : LevelData A r) : L.ζi ∈ zfns L := by
  simp [zfns]
lemma mem_ζb (L : LevelData A r) : L.ζb ∈ zfns L := by
  simp [zfns]
lemma mem_ζbi (L : LevelData A r) : L.ζbi ∈ zfns L := by
  simp [zfns]
lemma mem_GG (L : LevelData A r) : L.GG ∈ zfns L := by
  simp [zfns]
lemma mem_GGi (L : LevelData A r) : L.GGi ∈ zfns L := by
  simp [zfns]

lemma star_ζb {L : LevelData A r} (h : IsStarLevel L) : star L.ζb = L.ζ := by
  have h' : star L.ζ = L.ζb ∧ star L.nab = L.nabs ∧ star L.TT = L.TT := h
  rw [← h'.1, star_star]

lemma star_ζi {L : LevelData A r} (h : IsStarLevel L) : star L.ζi = L.ζbi := by
  have h' : star L.ζ = L.ζb ∧ star L.nab = L.nabs ∧ star L.TT = L.TT := h
  calc star L.ζi = star L.ζi * (L.ζb * L.ζbi) := by rw [L.ζb_ζbi, mul_one]
    _ = star (L.ζ * L.ζi) * L.ζbi := by rw [star_mul, h'.1, mul_assoc]
    _ = L.ζbi := by rw [L.ζ_ζi, star_one, one_mul]

lemma star_ζbi {L : LevelData A r} (h : IsStarLevel L) : star L.ζbi = L.ζi := by
  rw [← star_ζi h, star_star]

lemma star_GG {L : LevelData A r} (h : IsStarLevel L) : star L.GG = L.GG := by
  have h' : star L.ζ = L.ζb ∧ star L.nab = L.nabs ∧ star L.TT = L.TT := h
  have e : star (L.ζ * L.ζb) = L.ζ * L.ζb := by rw [star_mul, star_ζb h, h'.1]
  rw [L.GG_def, star_sub, e]
  first
  | rw [← algebraMap_star_comm, h'.2.2]
  | rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one, h'.2.2]

lemma star_GGi {L : LevelData A r} (h : IsStarLevel L) : star L.GGi = L.GGi := by
  calc star L.GGi = star L.GGi * (L.GG * L.GGi) := by rw [L.GG_GGi, mul_one]
    _ = star (L.GG * L.GGi) * L.GGi := by rw [star_mul, star_GG h, mul_assoc]
    _ = L.GGi := by rw [L.GG_GGi, star_one, one_mul]

lemma star_wt {L : LevelData A r} (h : IsStarLevel L) : star (wt L : SlopeTestRemainingChoices S A) = wt L := by
  have h' : star L.ζ = L.ζb ∧ star L.nab = L.nabs ∧ star L.TT = L.TT := h
  have k1 : Commute L.GGi L.ζ := fn_comm L (mem_GGi L) (mem_ζ L)
  have k2 : Commute L.GGi L.ζb := fn_comm L (mem_GGi L) (mem_ζb L)
  show star (io (L.ζ * L.ζb * L.GGi) : SlopeTestRemainingChoices S A) = io (L.ζ * L.ζb * L.GGi)
  rw [io_star, star_mul, star_mul, star_GGi h, star_ζb h, h'.1]
  congr 1
  exact (k1.mul_right k2).eq

lemma wt_eq (L : LevelData A r) : (wt L : SlopeTestRemainingChoices S A) = io L.ζ * io L.ζb * io L.GGi := by
  show (io (L.ζ * L.ζb * L.GGi) : SlopeTestRemainingChoices S A) = _
  rw [io_mul, io_mul]

lemma comm_wt (L : LevelData A r) {b : SlopeTestRemainingChoices S A} (h : ∀ g ∈ zfns L, Commute b (io g)) : Commute b (wt L) := by
  rw [wt_eq]
  exact ((h _ (mem_ζ L)).mul_right (h _ (mem_ζb L))).mul_right (h _ (mem_GGi L))

lemma io_fn_comm (L : LevelData A r) {g : A} (hg : g ∈ zfns L) :
    ∀ h ∈ zfns L, Commute (io g : SlopeTestRemainingChoices S A) (io h) := fun _ hh => io_comm (fn_comm L hg hh)

lemma free_wt (L : LevelData A r) (a : S) : FreeOf a (wt L : SlopeTestRemainingChoices S A) := free_io a _

lemma free_l (L : LevelData A r) (f : FrameData S A) {a : S} (h : f.Free a) (Y : ℂ) : FreeOf a (f.l L Y) := by
  obtain ⟨-, -, -, -, -, -, -, -, hee⟩ := h
  exact free_add (free_io a _) (free_mul (free_io a _) (hee Y))

lemma free_d (L : LevelData A r) (f : FrameData S A) {a : S} (h : f.Free a) : FreeOf a (f.d L) := by
  obtain ⟨-, -, -, -, -, -, hc, -, -⟩ := h
  exact free_mul (free_pow (free_wt L a) _) hc

lemma star_d {L : LevelData A r} {f : FrameData S A} (hs : IsStarLevel L) (h : IsFrame L f) :
    star (f.d L) = f.d L := by
  have e : f.d L = wt L ^ f.N * f.c := rfl
  rw [e, star_mul, star_pow, star_wt hs, h.c_star]
  exact ((comm_wt L h.c_fn).pow_right f.N).eq

lemma comm_d (L : LevelData A r) (f : FrameData S A) {b : SlopeTestRemainingChoices S A} (h1 : ∀ g ∈ zfns L, Commute b (io g))
    (h2 : Commute b f.c) : Commute b (f.d L) := by
  have e : f.d L = wt L ^ f.N * f.c := rfl
  rw [e]
  exact ((comm_wt L h1).pow_right f.N).mul_right h2

end Level

section Main

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem gaussFormPlus (L : LevelData A r) (f : FrameData S A) (a : S) (Ya : ℂ) (H : PlusHyp L f a Ya) :
    f.RR * ins a (f.TT Ya) = star (ins a !![1, 0; f.l L Ya, 1] * f.F) *
      (f.d L * ins a !![f.q Ya • (io L.GGi * f.xi (Ya + 1)), 0; 0, io L.GG * f.x Ya]) *
      (ins a !![1, 0; f.l L Ya, 1] * f.F) := by
  obtain ⟨hs, h, hfree, hreal, hYa, hYa1, hq⟩ := H
  obtain ⟨fRR, fTT, fF, fFi, fx, fxi, fc, fci, fee⟩ := hfree
  have hfree : f.Free a := ⟨fRR, fTT, fF, fFi, fx, fxi, fc, fci, fee⟩
  have rYa := h.inv_reg hYa
  have rYa1 := h.inv_reg hYa1

  have hGx : ∀ Y, Commute (io L.GG) (f.x Y) := fun Y => (h.x_fn Y _ (mem_GG L)).symm
  have hτs : star (io L.GG * f.x Ya) = io L.GG * f.x Ya := by
    rw [star_mul, io_star, star_GG hs, h.x_star Ya hreal]; exact (hGx Ya).eq.symm
  have hτd : Commute (io L.GG * f.x Ya) (f.d L) :=
    (comm_d L f (io_fn_comm L (mem_GG L)) (h.c_fn _ (mem_GG L)).symm).mul_left
      (comm_d L f (h.x_fn Ya) (h.x_c Ya))
  have hdτ : star (f.d L * (io L.GG * f.x Ya)) = f.d L * (io L.GG * f.x Ya) := by
    rw [star_mul, hτs, star_d hs h]; exact hτd.eq
  have hGG1 : (io L.GG : SlopeTestRemainingChoices S A) * io L.GGi = 1 := by rw [← io_mul, L.GG_GGi, io_one]
  have hGG2 : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by rw [← io_mul, L.GGi_GG, io_one]
  have hinv1 : ∀ Y ∈ f.inv, (io L.GGi * f.xi Y) * (io L.GG * f.x Y) = 1 := by
    intro Y hY
    calc (io L.GGi * f.xi Y) * (io L.GG * f.x Y) = io L.GGi * f.xi Y * (f.x Y * io L.GG) := by rw [(hGx Y).eq]
      _ = io L.GGi * (f.xi Y * f.x Y) * io L.GG := by simp only [mul_assoc]
      _ = 1 := by rw [(h.x_xi Y hY).2, mul_one, hGG2]
  have hinv2 : ∀ Y ∈ f.inv, (io L.GG * f.x Y) * (io L.GGi * f.xi Y) = 1 := by
    intro Y hY
    calc (io L.GG * f.x Y) * (io L.GGi * f.xi Y) = f.x Y * (io L.GG * io L.GGi) * f.xi Y := by
          rw [(hGx Y).eq]; simp only [mul_assoc]
      _ = 1 := by rw [hGG1, mul_one, (h.x_xi Y hY).1]

  have herm : star (f.RR * f.TT Ya 1 0) = f.RR * f.TT Ya 0 1 := by
    have e := congrFun (congrFun (h.module.herm Ya rYa hreal) 0) 1
    unfold d0 at e
    rwa [Matrix.conjTranspose_apply, Matrix.diagonal_mul, Matrix.diagonal_mul] at e
  have hdet := (h.module.det Ya rYa rYa1).2
  have quantum_determinant_shifted : f.TT Ya 0 0 * f.TT (Ya + 1) 1 1 - f.TT Ya 0 1 * f.TT (Ya + 1) 1 0 = f.q Ya • (1 : SlopeTestRemainingChoices S A) := by
    have e := congrFun (congrFun hdet 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J, Matrix.transpose_apply, Matrix.smul_apply] at e
    simp at e
    rw [Algebra.smul_def, mul_one, ← e]; abel
  have upper_block_det_one : f.TT Ya 1 0 * f.TT (Ya + 1) 1 1 = f.TT Ya 1 1 * f.TT (Ya + 1) 1 0 := by
    have e := congrFun (congrFun hdet 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J, Matrix.transpose_apply, Matrix.smul_apply] at e
    simp at e
    rw [← sub_eq_zero, ← e]; abel
  obtain ⟨e11, e10, e01, e00⟩ := core f.F f.Fi (f.d L) (io L.GG * f.x Ya) (io L.GGi * f.xi Ya)
    (io L.GG * f.x (Ya + 1)) (io L.GGi * f.xi (Ya + 1)) (f.l L Ya) f.RR (f.TT Ya 0 0) (f.TT Ya 0 1) (f.TT Ya 1 0)
    (f.TT Ya 1 1) (f.TT (Ya + 1) 1 0) (f.TT (Ya + 1) 1 1) (f.q Ya) h.form h.F_Fi h.Fi_F hdτ (hinv1 Ya hYa)
    (hinv2 _ hYa1) (hinv1 _ hYa1) (h.frame_τ Ya rYa) (h.frame_l Ya hYa hYa1) (h.frame_τ _ rYa1) herm quantum_determinant_shifted upper_block_det_one

  have fl := free_l L f hfree Ya
  have fd := free_d L f hfree
  have fΛ : FreeOf2 a !![1, 0; f.l L Ya, 1] := freeOf2_of_four_entries (free_one a) (free_zero a) fl (free_one a)
  have fΛs : FreeOf2 a !![1, star (f.l L Ya); 0, 1] :=
    freeOf2_of_four_entries (free_one a) (free_star fl) (free_zero a) (free_one a)
  have fD : FreeOf2 a !![f.q Ya • (io L.GGi * f.xi (Ya + 1)), 0; 0, io L.GG * f.x Ya] :=
    freeOf2_of_four_entries (free_smul _ (free_mul (free_io a _) (fxi _))) (free_zero a) (free_zero a)
      (free_mul (free_io a _) (fx _))
  have f1 := Wd4.freeOf_diagScalar (free_star fF)
  have f2 := Wd4.freeOf2_mul f1 fΛs
  have f3 := Wd4.freeOf2_mul f2 (Wd4.freeOf_diagScalar fd)
  have f4 := Wd4.freeOf2_mul f3 fD
  have f5 := Wd4.freeOf2_mul f4 fΛ
  have R : star (ins a !![1, 0; f.l L Ya, 1] * f.F) *
      (f.d L * ins a !![f.q Ya • (io L.GGi * f.xi (Ya + 1)), 0; 0, io L.GG * f.x Ya]) *
      (ins a !![1, 0; f.l L Ya, 1] * f.F) =
      ins a (d0 (star f.F) * !![1, star (f.l L Ya); 0, 1] * d0 (f.d L) *
        !![f.q Ya • (io L.GGi * f.xi (Ya + 1)), 0; 0, io L.GG * f.x Ya] * !![1, 0; f.l L Ya, 1] * d0 f.F) := by
    rw [Wd1.ins_mul a _ _ f5, Wd1.ins_mul a _ _ f4, Wd1.ins_mul a _ _ f3, Wd1.ins_mul a _ _ f2,
      Wd1.ins_mul a _ _ f1, Wd1.insert_diagonal_extract, Wd1.insert_diagonal_extract, Wd1.insert_diagonal_extract, star_mul, Wd1.ins_star a _ fΛ, lam_conj]
    simp only [mul_assoc]
  have Lh : f.RR * ins a (f.TT Ya) = ins a (d0 f.RR * f.TT Ya) := by
    rw [Wd1.ins_mul a _ _ (Wd4.freeOf_diagScalar fRR), Wd1.insert_diagonal_extract]
  rw [R, Lh, gauss_entries]
  congr 1
  refine Matrix.ext fun i j => ?_
  unfold d0
  rw [Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j
  · simpa [mul_smul_comm] using e00
  · simpa using e01
  · simpa using e10
  · simpa using e11

lemma w1 (L : LevelData A r) : L.ζbi * (L.ζ * L.ζb * L.GGi) * L.ζi = L.GGi := by
  have c1 : L.ζbi * L.ζ = L.ζ * L.ζbi := fn_comm L (mem_ζbi L) (mem_ζ L)
  have c2 : L.GGi * L.ζi = L.ζi * L.GGi := fn_comm L (mem_GGi L) (mem_ζi L)
  calc L.ζbi * (L.ζ * L.ζb * L.GGi) * L.ζi = L.ζ * (L.ζbi * L.ζb) * (L.GGi * L.ζi) := by
        rw [← mul_assoc L.ζbi, ← mul_assoc L.ζbi, c1]; simp only [mul_assoc]
    _ = L.GGi := by rw [L.ζbi_ζb, mul_one, c2, ← mul_assoc, L.ζ_ζi, one_mul]

lemma w2 (L : LevelData A r) : L.GG * L.ζi * (L.ζ * L.ζb * L.GGi) * (L.ζbi * L.GG) = L.GG := by
  have c3 : L.ζb * L.GGi = L.GGi * L.ζb := fn_comm L (mem_ζb L) (mem_GGi L)
  calc L.GG * L.ζi * (L.ζ * L.ζb * L.GGi) * (L.ζbi * L.GG)
        = L.GG * (L.ζi * L.ζ) * (L.ζb * L.GGi) * (L.ζbi * L.GG) := by simp only [mul_assoc]
    _ = L.GG * L.GGi * (L.ζb * L.ζbi) * L.GG := by rw [L.ζi_ζ, mul_one, c3]; simp only [mul_assoc]
    _ = L.GG := by rw [L.GG_GGi, L.ζb_ζbi, one_mul, one_mul]

lemma diag_entries (p1 p2 w c1 c2 e1 e2 : SlopeTestRemainingChoices S A) :
    !![p1, 0; 0, p2] * d0 w * !![c1, 0; 0, c2] * !![e1, 0; 0, e2] =
      !![p1 * w * c1 * e1, 0; 0, p2 * w * c2 * e2] := by
  first
  | (simp only [d0_eq_diagonal, Matrix.mul_fin_two, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add,
      mul_assoc]; done)
  | (refine Matrix.ext fun i j => ?_
     fin_cases i <;> fin_cases j <;>
       simp [d0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, mul_assoc])

theorem plusForm (L : LevelData A r) (f : FrameData S A) (a : S) (Ya : ℂ) (H : PlusHyp L f a Ya) :
    (f.plus L a Ya).RR = star (f.plus L a Ya).F * (f.plus L a Ya).d L * (f.plus L a Ya).F := by
  have hG := gaussFormPlus L f a Ya H
  have hfree0 := H.2.2.1
  obtain ⟨hs, hf, hfree, hY, hYi, hY1i, -⟩ := H
  obtain ⟨-, -, -, -, fx, fxi, fc, -, -⟩ := hfree0
  obtain ⟨hx1, hx1'⟩ := hf.x_xi (Ya + 1) hY1i
  have hd : f.d L = (wt L : SlopeTestRemainingChoices S A) ^ f.N * f.c := rfl
  have gW : ∀ g ∈ zfns L, Commute (io g : SlopeTestRemainingChoices S A) (wt L) := fun g hg => comm_wt L (io_fn_comm L hg)
  have gc : ∀ g ∈ zfns L, Commute (io g : SlopeTestRemainingChoices S A) f.c := fun g hg => (hf.c_fn g hg).symm
  have cW : Commute f.c (wt L : SlopeTestRemainingChoices S A) := comm_wt L hf.c_fn
  have xiζi : Commute (f.xi (Ya + 1)) (io L.ζi) := comm_inv hx1 hx1' (hf.x_fn (Ya + 1) _ (mem_ζi L))
  have xζbi : Commute (f.x Ya) (io L.ζbi) := hf.x_fn Ya _ (mem_ζbi L)
  have xG : Commute (f.x Ya) (io L.GG) := hf.x_fn Ya _ (mem_GG L)
  have cb1 : Commute L.ζbi L.ζ := fn_comm L (mem_ζbi L) (mem_ζ L)
  have cb2 : Commute L.ζbi L.ζb := fn_comm L (mem_ζbi L) (mem_ζb L)
  have cb3 : Commute L.ζbi L.GGi := fn_comm L (mem_ζbi L) (mem_GGi L)
  have k1 : L.ζ * L.ζb * L.GGi * L.ζbi * L.ζi = L.GGi := by
    rw [← ((cb1.mul_right cb2).mul_right cb3).eq]
    exact w1 L
  have hw : (wt L : SlopeTestRemainingChoices S A) * io L.ζbi * io L.ζi = io L.GGi := by
    show (io (L.ζ * L.ζb * L.GGi) : SlopeTestRemainingChoices S A) * io L.ζbi * io L.ζi = io L.GGi
    rw [← io_mul, ← io_mul, k1]
  have hw2 : (io L.GG : SlopeTestRemainingChoices S A) * (io L.ζi * (wt L * (io L.ζbi * io L.GG))) = io L.GG := by
    show (io L.GG : SlopeTestRemainingChoices S A) * (io L.ζi * (io (L.ζ * L.ζb * L.GGi) * (io L.ζbi * io L.GG))) = io L.GG
    rw [← io_mul, ← io_mul, ← io_mul, ← io_mul]
    congr 1
    rw [← mul_assoc L.GG L.ζi, ← mul_assoc (L.GG * L.ζi)]
    exact w2 L
  have E1 : io L.ζbi * (wt L ^ (f.N + 1) * f.c) * (f.q Ya • f.xi (Ya + 1)) * io L.ζi =
      f.d L * (f.q Ya • (io L.GGi * f.xi (Ya + 1))) := by
    rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [hd, pow_succ]
    simp only [mul_assoc]
    rw [((gW _ (mem_ζbi L)).pow_right f.N).left_comm, (gW _ (mem_ζbi L)).left_comm,
      (gc _ (mem_ζbi L)).left_comm, cW.symm.left_comm, xiζi.eq]
    rw [← mul_assoc (io L.ζbi) (io L.ζi) (f.xi (Ya + 1)),
      ← mul_assoc (wt L) (io L.ζbi * io L.ζi) (f.xi (Ya + 1)), ← mul_assoc (wt L) (io L.ζbi) (io L.ζi), hw]
  have E2 : io L.GG * io L.ζi * (wt L ^ (f.N + 1) * f.c) * f.x Ya * (io L.ζbi * io L.GG) =
      f.d L * (io L.GG * f.x Ya) := by
    rw [hd, pow_succ]
    simp only [mul_assoc]
    rw [xζbi.left_comm, xG.eq]
    rw [((gW _ (mem_ζi L)).pow_right f.N).left_comm, ((gW _ (mem_GG L)).pow_right f.N).left_comm]
    rw [cW.symm.left_comm, (gc _ (mem_ζi L)).left_comm, (gc _ (mem_GG L)).left_comm]
    rw [← mul_assoc (io L.ζbi) (io L.GG) (f.x Ya), ← mul_assoc (wt L) (io L.ζbi * io L.GG) (f.x Ya),
      ← mul_assoc (io L.ζi) (wt L * (io L.ζbi * io L.GG)) (f.x Ya),
      ← mul_assoc (io L.GG) (io L.ζi * (wt L * (io L.ζbi * io L.GG))) (f.x Ya), hw2]
  have fd : FreeOf a (f.d L) := free_d L f hfree
  have fX : FreeOf a ((wt L : SlopeTestRemainingChoices S A) ^ (f.N + 1) * f.c) := free_mul (free_pow (free_wt L a) _) fc
  have fd0 : ∀ X : SlopeTestRemainingChoices S A, FreeOf a X → FreeOf2 a (d0 X) := fun X hX => by
    rw [d0_eq_diagonal]; exact freeOf2_of_four_entries hX (free_zero a) (free_zero a) hX
  have fZ2 : FreeOf2 a !![(io L.ζi : SlopeTestRemainingChoices S A), 0; 0, io L.ζbi * io L.GG] :=
    freeOf2_of_four_entries (free_io a _) (free_zero a) (free_zero a) (free_mul (free_io a _) (free_io a _))
  have fZh : FreeOf2 a !![(io L.ζbi : SlopeTestRemainingChoices S A), 0; 0, io L.GG * io L.ζi] :=
    freeOf2_of_four_entries (free_io a _) (free_zero a) (free_zero a) (free_mul (free_io a _) (free_io a _))
  have fC : FreeOf2 a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya] :=
    freeOf2_of_four_entries (free_smul _ (fxi _)) (free_zero a) (free_zero a) (fx _)
  have key : ins a !![(io L.ζbi : SlopeTestRemainingChoices S A), 0; 0, io L.GG * io L.ζi] *
      (wt L ^ (f.N + 1) * (f.c * ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya])) *
      ins a !![io L.ζi, 0; 0, io L.ζbi * io L.GG] =
      f.d L * ins a !![f.q Ya • (io L.GGi * f.xi (Ya + 1)), 0; 0, io L.GG * f.x Ya] := by
    rw [← mul_assoc ((wt L : SlopeTestRemainingChoices S A) ^ (f.N + 1)) f.c, ← Wd1.insert_diagonal_extract a ((wt L : SlopeTestRemainingChoices S A) ^ (f.N + 1) * f.c),
      ← Wd1.insert_diagonal_extract a (f.d L)]
    simp only [mul_assoc]
    rw [← Wd1.ins_mul a _ _ fC, ← Wd1.ins_mul a _ _ (fd0 _ fX), ← Wd1.ins_mul a _ _ fZh,
      ← Wd1.ins_mul a _ _ (fd0 _ fd)]
    congr 1
    simp only [← mul_assoc]
    rw [diag_entries, d0_eq_diagonal, Matrix.mul_fin_two]
    simp only [mul_zero, zero_mul, add_zero, zero_add]
    rw [E1, E2]
  have key' : ∀ Y : SlopeTestRemainingChoices S A, ins a !![(io L.ζbi : SlopeTestRemainingChoices S A), 0; 0, io L.GG * io L.ζi] *
      (wt L ^ (f.N + 1) * (f.c * (ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya] *
      (ins a !![io L.ζi, 0; 0, io L.ζbi * io L.GG] * Y)))) =
      f.d L * (ins a !![f.q Ya • (io L.GGi * f.xi (Ya + 1)), 0; 0, io L.GG * f.x Ya] * Y) := by
    intro Y
    have e := congrArg (· * Y) key
    simp only [mul_assoc] at e
    exact e
  have hZ : (!![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * f.l L Ya, io L.GG] : M2 (SlopeTestRemainingChoices S A)) =
      !![io L.ζi, 0; 0, io L.ζbi * io L.GG] * !![1, 0; f.l L Ya, 1] := by
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp only [mul_one, mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_assoc]
  show f.RR * ins a (f.TT Ya) =
    star (ins a (!![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * f.l L Ya, io L.GG]) * f.F) *
      ((wt L : SlopeTestRemainingChoices S A) ^ (f.N + 1) * (f.c * ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya])) *
      (ins a (!![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * f.l L Ya, io L.GG]) * f.F)
  rw [hG, hZ, Wd1.ins_mul a _ _ fZ2, star_mul, star_mul, star_mul, Wd1.ins_star a _ fZ2, diag_conj,
    io_star, star_mul, io_star, io_star, star_ζi hs, star_GG hs, star_ζbi hs]
  simp only [mul_assoc]
  rw [key']

end Main

end Formalism.FourierDecayAlt.P.Fr5

namespace Formalism.FourierDecayAlt.P

theorem gauss_form_plus_letter : Formalism.FourierDecayAlt.Fr.GaussFormPlus := by
  intro A S _ _ _ _ _ _ r L f a Ya H
  exact Fr5.gaussFormPlus L f a Ya H

theorem plus_letter_form : Formalism.FourierDecayAlt.Fr.PlusForm := by
  intro A S _ _ _ _ _ _ r L f a Ya H
  exact Fr5.plusForm L f a Ya H

end Formalism.FourierDecayAlt.P
