import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockTwist

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

namespace TwistedTransfer

section Frame

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

private theorem eU_zero_zero_add_eU_one_one (a : S) : (eU a 0 0 : SlopeTestRemainingChoices S A) + eU a 1 1 = 1 := by
  refine Matrix.ext fun x y => ?_
  simp only [eU, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    generalize x a = v
    fin_cases v <;> simp
  · rw [if_neg hxy]
    have h : ∀ i : Fin 2, ¬ (x a = i ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b) := by
      rintro i ⟨h1, h2, h3⟩
      apply hxy
      funext b
      by_cases hb : b = a
      · subst hb; rw [h1, h2]
      · exact h3 b hb
    rw [if_neg (h 0), if_neg (h 1), add_zero]

private theorem commute_io_eU (g : A) (a : S) (i j : Fin 2) : Commute (io g : SlopeTestRemainingChoices S A) (eU a i j) := by
  show (io g : SlopeTestRemainingChoices S A) * eU a i j = eU a i j * io g
  refine Matrix.ext fun x y => ?_
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, eU, Matrix.of_apply]
  split_ifs <;> simp

private theorem commute_io_ins_of_commute_entries (g : A) (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (h : ∀ i j, Commute (io g : SlopeTestRemainingChoices S A) (M i j)) :
    Commute (io g : SlopeTestRemainingChoices S A) (ins a M) := by
  unfold ins
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => (commute_io_eU g a i j).mul_right (h i j)

private theorem cj_mul_of_mul_inv_eq_one {f fi : A} (h1 : f * fi = 1) (x y : SlopeTestRemainingChoices S A) :
    cj f fi (x * y) = cj f fi x * cj f fi y := by
  have hff : (io f : SlopeTestRemainingChoices S A) * io fi = 1 := by
    unfold io; rw [← map_mul (Matrix.scalar (Ix S)), h1, map_one]
  unfold cj
  calc io fi * (x * y) * io f = io fi * x * (io f * io fi) * y * io f := by
        rw [hff, mul_one]; simp only [mul_assoc]
    _ = io fi * x * io f * (io fi * y * io f) := by simp only [mul_assoc]

private theorem cj_eq_self_of_commute {f fi : A} (h2 : fi * f = 1) (x : SlopeTestRemainingChoices S A) (hx : Commute (io f : SlopeTestRemainingChoices S A) x) :
    cj f fi x = x := by
  have hfi : (io fi : SlopeTestRemainingChoices S A) * io f = 1 := by
    unfold io; rw [← map_mul (Matrix.scalar (Ix S)), h2, map_one]
  unfold cj
  rw [mul_assoc, ← hx.eq, ← mul_assoc, hfi, one_mul]

private theorem cj_smul' (f fi : A) (c : ℂ) (x : SlopeTestRemainingChoices S A) : cj f fi (c • x) = c • cj f fi x := by
  unfold cj; rw [mul_smul_comm, smul_mul_assoc]

private theorem cj_sub' (f fi : A) (x y : SlopeTestRemainingChoices S A) : cj f fi (x - y) = cj f fi x - cj f fi y := by
  unfold cj; rw [mul_sub, sub_mul]

private theorem cj_add' (f fi : A) (x y : SlopeTestRemainingChoices S A) : cj f fi (x + y) = cj f fi x + cj f fi y := by
  unfold cj; rw [mul_add, add_mul]

private theorem star_eU_apply_swap (a : S) (i j : Fin 2) : star (eU a i j : SlopeTestRemainingChoices S A) = eU a j i := by
  refine Matrix.ext fun x y => ?_
  rw [Matrix.star_apply]
  simp only [eU, Matrix.of_apply]
  have hiff : (y a = i ∧ x a = j ∧ ∀ b, b ≠ a → y b = x b) ↔ (x a = j ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b) := by
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, fun b hb => (h3 b hb).symm⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, fun b hb => (h3 b hb).symm⟩
  by_cases h : x a = j ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b
  · rw [if_pos (hiff.2 h), if_pos h, star_one]
  · rw [if_neg (mt hiff.1 h), if_neg h, star_zero]

theorem ins_combine (a : S) (p k : SlopeTestRemainingChoices S A) (hk : FreeOf a k) (M : M2 (SlopeTestRemainingChoices S A)) :
    p + k * ins a M = ins a !![p + k * M 0 0, k * M 0 1; k * M 1 0, p + k * M 1 1] := by
  have hc : ∀ i j, eU a i j * k = k * eU a i j := fun i j => (hk i j).eq
  have hp : p = eU a 0 0 * p + eU a 1 1 * p := by rw [← add_mul, eU_zero_zero_add_eU_one_one, one_mul]
  unfold ins
  simp [Fin.sum_univ_two, mul_add, ← mul_assoc, hc]
  conv_lhs => rw [hp]
  abel

theorem ins_combine_mk (a : S) (p k : SlopeTestRemainingChoices S A) (hk : FreeOf a k) (x y z w : SlopeTestRemainingChoices S A) :
    p + k * ins a !![x, y; z, w] = ins a !![p + k * x, k * y; k * z, p + k * w] := by
  exact ins_combine a p k hk !![x, y; z, w]

variable {L : R.LevelData A r} {st : Fr.Start A} {f fi : A} {s : ℂ}

theorem tw_ins_mk (a : S) (t : ℂ) (x y z w : SlopeTestRemainingChoices S A) (hx : Tw f fi t x) (hw : Tw f fi t w)
    (hy : cj f fi y = y) (hz : cj f fi z = z) : Tw f fi t (ins a !![x, y; z, w]) := by
  have hx' : cj f fi x = x - t • (1 : SlopeTestRemainingChoices S A) := hx
  have hw' : cj f fi w = w - t • (1 : SlopeTestRemainingChoices S A) := hw
  have key : cj f fi (ins a !![x, y; z, w]) = ins a !![cj f fi x, cj f fi y; cj f fi z, cj f fi w] := by
    unfold ins cj
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, (commute_io_eU fi a i j).eq, mul_assoc (eU a i j), mul_assoc (eU a i j)]
    fin_cases i <;> fin_cases j <;> rfl
  show cj f fi (ins a !![x, y; z, w]) = ins a !![x, y; z, w] - t • (1 : SlopeTestRemainingChoices S A)
  rw [key, hx', hw', hy, hz]
  conv_rhs => rw [← eU_zero_zero_add_eU_one_one (A := A) a]
  unfold ins
  simp [Fin.sum_univ_two, mul_sub, smul_add, mul_smul_comm] <;> abel

section Older

variable (hW : WaveHyp L st f fi s) (fw : Fr.FrameData S A) (hF : Fr.IsFrame L fw)
  (ihx : ∀ Y, Commute (io f : SlopeTestRemainingChoices S A) (fw.x Y)) (ihl : ∀ Y ∈ fw.inv, Tw f fi s (fw.l L Y))
include hW hF ihx ihl

theorem io_commute_xi : ∀ Y ∈ fw.inv, Commute (io f : SlopeTestRemainingChoices S A) (fw.xi Y) := by
  intro Y hY
  obtain ⟨h1, h2⟩ := hF.x_xi Y hY
  have hx := ihx Y
  show (io f : SlopeTestRemainingChoices S A) * fw.xi Y = fw.xi Y * io f
  calc (io f : SlopeTestRemainingChoices S A) * fw.xi Y = fw.xi Y * fw.x Y * io f * fw.xi Y := by rw [h2, one_mul]
    _ = fw.xi Y * (io f * fw.x Y) * fw.xi Y := by rw [hx.eq]; simp only [mul_assoc]
    _ = fw.xi Y * io f := by rw [mul_assoc, mul_assoc, h1, mul_one]

theorem cj_kapL_DD : ∀ Y ∈ fw.inv, ∀ Y' ∈ fw.inv,
    cj f fi (Fr.kapL L * fw.DD Y Y') = Fr.kapL L * fw.DD Y Y' := by
  intro Y hY Y' hY'
  have hl : cj f fi (fw.l L Y) = fw.l L Y - s • (1 : SlopeTestRemainingChoices S A) := ihl Y hY
  have hl' : cj f fi (fw.l L Y') = fw.l L Y' - s • (1 : SlopeTestRemainingChoices S A) := ihl Y' hY'
  have hio : (io (L.l0 Y - L.l0 Y') : SlopeTestRemainingChoices S A) = io (L.l0 Y) - io (L.l0 Y') := map_sub (Matrix.scalar (Ix S)) _ _
  have e : Fr.kapL L * fw.DD Y Y' = (Y - Y')⁻¹ • (fw.l L Y - fw.l L Y' - io (L.l0 Y - L.l0 Y')) := by
    unfold Formalism.FourierDecayAlt.Fr.FrameData.DD Formalism.FourierDecayAlt.Fr.FrameData.l
    rw [mul_smul_comm, mul_sub, hio]
    congr 1
    abel
  have hc : Commute (io f : SlopeTestRemainingChoices S A) (io (L.l0 Y - L.l0 Y')) := (hW.lowering_constant_sub Y Y').map (Matrix.scalar (Ix S))
  rw [e, cj_smul', cj_sub', cj_sub', hl, hl', cj_eq_self_of_commute hW.fi_f _ hc]
  congr 1
  abel

theorem tw_xi_l_x : ∀ Y ∈ fw.inv, ∀ Ya ∈ fw.inv, Tw f fi s (fw.xi Ya * fw.l L Y * fw.x Ya) := by
  intro Y hY Ya hYa
  have hxi := io_commute_xi hW fw hF ihx ihl Ya hYa
  obtain ⟨h1, h2⟩ := hF.x_xi Ya hYa
  have hl : cj f fi (fw.l L Y) = fw.l L Y - s • (1 : SlopeTestRemainingChoices S A) := ihl Y hY
  show cj f fi (fw.xi Ya * fw.l L Y * fw.x Ya) = fw.xi Ya * fw.l L Y * fw.x Ya - s • (1 : SlopeTestRemainingChoices S A)
  rw [cj_mul_of_mul_inv_eq_one hW.f_fi, cj_mul_of_mul_inv_eq_one hW.f_fi, cj_eq_self_of_commute hW.fi_f _ hxi, cj_eq_self_of_commute hW.fi_f _ (ihx Ya), hl,
    mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, h2]

omit ihx ihl in
theorem io_l0_add_kapL_eq : ∀ Y, ∀ Ya ∈ fw.inv, io (L.l0 Y) + Fr.kapL L * (fw.xi Ya * fw.ee Y * fw.x Ya) =
    fw.xi Ya * fw.l L Y * fw.x Ya := by
  intro Y Ya hYa
  obtain ⟨h1, h2⟩ := hF.x_xi Ya hYa
  have hz := mem_zfns L
  have hl0 : Commute (fw.x Ya) (io (L.l0 Y)) := by
    rw [embed_lowering_constant]
    exact (hF.x_nab Ya).neg_right.sub_right (((Commute.one_right _).smul_right _).mul_right
      ((hF.x_fn Ya _ hz.2.2.1).mul_right (hF.x_fn Ya _ hz.2.2.2.2.2)))
  have hk : Commute (fw.x Ya) (Fr.kapL L) := by
    unfold Fr.kapL io
    rw [map_mul, map_mul]
    exact ((hF.x_fn Ya _ hz.2.2.1).mul_right (hF.x_fn Ya _ hz.2.1)).mul_right (hF.x_fn Ya _ hz.2.2.2.2.2)
  have e1 : fw.xi Ya * io (L.l0 Y) * fw.x Ya = io (L.l0 Y) := by
    rw [mul_assoc, ← hl0.eq, ← mul_assoc, h2, one_mul]
  have e2 : fw.xi Ya * Fr.kapL L = Fr.kapL L * fw.xi Ya := by
    calc fw.xi Ya * Fr.kapL L = fw.xi Ya * (Fr.kapL L * fw.x Ya) * fw.xi Ya := by
          rw [mul_assoc, mul_assoc, h1, mul_one]
      _ = fw.xi Ya * fw.x Ya * Fr.kapL L * fw.xi Ya := by rw [← hk.eq]; simp only [mul_assoc]
      _ = Fr.kapL L * fw.xi Ya := by rw [h2, one_mul]
  unfold Formalism.FourierDecayAlt.Fr.FrameData.l
  rw [mul_add, add_mul, e1]
  congr 1
  rw [← mul_assoc (fw.xi Ya) (Fr.kapL L) (fw.ee Y), e2]
  simp only [mul_assoc]

end Older

section Letters

variable (hW : WaveHyp L st f fi s) (fw : Fr.FrameData S A) (hF : Fr.IsFrame L fw) (a : S)
  (Ya : ℂ) (m0 : Ya ∈ fw.inv)
  (ihx : ∀ Y, Commute (io f : SlopeTestRemainingChoices S A) (fw.x Y))
  (ihl : ∀ Y ∈ fw.inv, Tw f fi s (fw.l L Y))
include hW hF m0 ihx ihl

omit m0 ihl in
theorem commute_io_plus_x : ∀ Y, Commute (io f : SlopeTestRemainingChoices S A) ((fw.plus L a Ya).x Y) := by
  intro Y
  show Commute (io f : SlopeTestRemainingChoices S A) (fw.x Y * ins a !![((Y - Ya) / (Y - Ya - 1)) • 1, 0; 0, 1])
  refine (ihx Y).mul_right (commute_io_ins_of_commute_entries f a _ ?_)
  intro i j
  fin_cases i <;> fin_cases j
  · show Commute (io f : SlopeTestRemainingChoices S A) (((Y - Ya) / (Y - Ya - 1)) • (1 : SlopeTestRemainingChoices S A))
    exact (Commute.one_right _).smul_right _
  · show Commute (io f : SlopeTestRemainingChoices S A) 0
    exact Commute.zero_right _
  · show Commute (io f : SlopeTestRemainingChoices S A) 0
    exact Commute.zero_right _
  · show Commute (io f : SlopeTestRemainingChoices S A) 1
    exact Commute.one_right _

omit m0 in
theorem plus_c (ihc : Commute (io f : SlopeTestRemainingChoices S A) fw.c) (m1 : Ya + 1 ∈ fw.inv) : Commute (io f : SlopeTestRemainingChoices S A) (fw.plus L a Ya).c := by
  show Commute (io f : SlopeTestRemainingChoices S A) (fw.c * ins a !![fw.q Ya • fw.xi (Ya + 1), 0; 0, fw.x Ya])
  refine ihc.mul_right (commute_io_ins_of_commute_entries f a _ ?_)
  intro i j
  have h1 := (io_commute_xi hW fw hF ihx ihl (Ya + 1) m1).smul_right (fw.q Ya)
  fin_cases i <;> fin_cases j
  · exact h1
  · exact Commute.zero_right _
  · exact Commute.zero_right _
  · exact ihx Ya

theorem plus_l : ∀ Y ∈ (fw.plus L a Ya).inv, Tw f fi s ((fw.plus L a Ya).l L Y) := by
  intro Y hY
  have hY0 : Y ∈ fw.inv := hY.1
  have hkap : FreeOf a (Fr.kapL L : SlopeTestRemainingChoices S A) := fun i j => by unfold Fr.kapL; exact (commute_io_eU _ a i j).symm
  show cj f fi (io (L.l0 Y) + Fr.kapL L * ins a !![fw.ee Y - fw.DD Y Ya + Fr.tz L, -((Y - Ya)⁻¹ • (1 : SlopeTestRemainingChoices S A));
      0, fw.xi Ya * fw.ee Y * fw.x Ya]) =
    io (L.l0 Y) + Fr.kapL L * ins a !![fw.ee Y - fw.DD Y Ya + Fr.tz L, -((Y - Ya)⁻¹ • (1 : SlopeTestRemainingChoices S A));
      0, fw.xi Ya * fw.ee Y * fw.x Ya] - s • (1 : SlopeTestRemainingChoices S A)
  rw [ins_combine_mk a _ _ hkap]
  refine tw_ins_mk a s _ _ _ _ ?_ ?_ ?_ ?_
  · have e : io (L.l0 Y) + Fr.kapL L * (fw.ee Y - fw.DD Y Ya + Fr.tz L) =
        fw.l L Y - Fr.kapL L * fw.DD Y Ya + Fr.kapL L * Fr.tz L := by
      unfold Formalism.FourierDecayAlt.Fr.FrameData.l
      rw [mul_add, mul_sub]
      abel
    have hl : cj f fi (fw.l L Y) = fw.l L Y - s • (1 : SlopeTestRemainingChoices S A) := ihl Y hY0
    show cj f fi _ = _ - s • (1 : SlopeTestRemainingChoices S A)
    rw [e, cj_add', cj_sub', hl, cj_kapL_DD hW fw hF ihx ihl Y hY0 Ya m0,
      cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right hW.tz)]
    abel
  · show cj f fi _ = _ - s • (1 : SlopeTestRemainingChoices S A)
    rw [io_l0_add_kapL_eq hW fw hF Y Ya m0]
    exact tw_xi_l_x hW fw hF ihx ihl Y hY0 Ya m0
  · exact cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right ((Commute.one_right _).smul_right _).neg_right)
  · exact cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right (Commute.zero_right _))

theorem plus_F (hfree : fw.Free a) (UU : SlopeTestRemainingChoices S A) (ihF : fw.F * (io f * UU) = io f * fw.F) :
    (fw.plus L a Ya).F * (io f * (ins a (lift0 (Uinv (A := A) s)) * UU)) = io f * (fw.plus L a Ya).F := by
  have hfl : FreeOf a (fw.l L Ya) := fun i j => by
    unfold Formalism.FourierDecayAlt.Fr.FrameData.l Fr.kapL
    exact ((commute_io_eU _ a i j).symm).add_right (((commute_io_eU _ a i j).symm).mul_right (hfree.2.2.2.2.2.2.2.2 Ya i j))
  have hD : FreeOf2 a (!![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * fw.l L Ya, io L.GG] : M2 (SlopeTestRemainingChoices S A)) := by
    rw [Matrix.mul_fin_two]
    intro p q i j
    have hio : ∀ g : A, Commute (eU a i j) (io g : SlopeTestRemainingChoices S A) := fun g => (commute_io_eU g a i j).symm
    fin_cases p <;> fin_cases q
    · exact ((hio _).mul_right (Commute.one_right _)).add_right ((Commute.zero_right _).mul_right ((hio _).mul_right (hfl i j)))
    · exact ((hio _).mul_right (Commute.zero_right _)).add_right ((Commute.zero_right _).mul_right (hio _))
    · exact ((Commute.zero_right _).mul_right (Commute.one_right _)).add_right ((hio _).mul_right ((hio _).mul_right (hfl i j)))
    · exact ((Commute.zero_right _).mul_right (Commute.zero_right _)).add_right ((hio _).mul_right (hio _))
  have hz := mem_zfns L
  have hE := block_twist hW.f_fi hW.fi_f s (io L.ζi) (io L.ζbi) (io L.GG) (fw.l L Ya) (hW.io_fn hz.2.1)
    (hW.io_fn hz.2.2.2.1) (hW.io_fn hz.2.2.2.2.1) (ihl Ya m0)
  exact frame_step hW.f_fi a s _ fw.F UU hD hfree.2.2.1 ihF hE

omit m0 ihl in
theorem commute_io_minus_x : ∀ Y, Commute (io f : SlopeTestRemainingChoices S A) ((fw.minus L a Ya).x Y) := by
  intro Y
  show Commute (io f : SlopeTestRemainingChoices S A) (fw.x Y * ins a !![((Ya - Y) / (Ya - Y - 1)) • 1, 0; 0, 1])
  refine (ihx Y).mul_right (commute_io_ins_of_commute_entries f a _ ?_)
  intro i j
  fin_cases i <;> fin_cases j
  · show Commute (io f : SlopeTestRemainingChoices S A) (((Ya - Y) / (Ya - Y - 1)) • (1 : SlopeTestRemainingChoices S A))
    exact (Commute.one_right _).smul_right _
  · show Commute (io f : SlopeTestRemainingChoices S A) 0
    exact Commute.zero_right _
  · show Commute (io f : SlopeTestRemainingChoices S A) 0
    exact Commute.zero_right _
  · show Commute (io f : SlopeTestRemainingChoices S A) 1
    exact Commute.one_right _

omit m0 in
theorem minus_c (ihc : Commute (io f : SlopeTestRemainingChoices S A) fw.c) (mm1 : Ya - 1 ∈ fw.inv) : Commute (io f : SlopeTestRemainingChoices S A) (fw.minus L a Ya).c := by
  show Commute (io f : SlopeTestRemainingChoices S A) (fw.c * ins a !![fw.q (Ya - 1) • fw.xi (Ya - 1), 0; 0, fw.x Ya])
  refine ihc.mul_right (commute_io_ins_of_commute_entries f a _ ?_)
  intro i j
  have h1 := (io_commute_xi hW fw hF ihx ihl (Ya - 1) mm1).smul_right (fw.q (Ya - 1))
  fin_cases i <;> fin_cases j
  · exact h1
  · exact Commute.zero_right _
  · exact Commute.zero_right _
  · exact ihx Ya

theorem minus_l (mm1 : Ya - 1 ∈ fw.inv) : ∀ Y ∈ (fw.minus L a Ya).inv, Tw f fi s ((fw.minus L a Ya).l L Y) := by
  intro Y hY
  have hY0 : Y ∈ fw.inv := hY.1
  have hkap : FreeOf a (Fr.kapL L : SlopeTestRemainingChoices S A) := fun i j => by unfold Fr.kapL; exact (commute_io_eU _ a i j).symm
  show cj f fi (io (L.l0 Y) + Fr.kapL L * ins a !![fw.ee Y, 0;
      -((fw.q (Ya - 1) / (Ya - Y - 1)) • (fw.xi Ya * fw.xi (Ya - 1))), fw.xi Ya * fw.ee Y * fw.x Ya - fw.DD Y Ya + Fr.tz L]) =
    io (L.l0 Y) + Fr.kapL L * ins a !![fw.ee Y, 0;
      -((fw.q (Ya - 1) / (Ya - Y - 1)) • (fw.xi Ya * fw.xi (Ya - 1))), fw.xi Ya * fw.ee Y * fw.x Ya - fw.DD Y Ya + Fr.tz L] -
      s • (1 : SlopeTestRemainingChoices S A)
  rw [ins_combine_mk a _ _ hkap]
  refine tw_ins_mk a s _ _ _ _ ?_ ?_ ?_ ?_
  · exact ihl Y hY0
  · have e : io (L.l0 Y) + Fr.kapL L * (fw.xi Ya * fw.ee Y * fw.x Ya - fw.DD Y Ya + Fr.tz L) =
        (io (L.l0 Y) + Fr.kapL L * (fw.xi Ya * fw.ee Y * fw.x Ya)) - Fr.kapL L * fw.DD Y Ya + Fr.kapL L * Fr.tz L := by
      rw [mul_add, mul_sub]
      abel
    have hl' : cj f fi (fw.xi Ya * fw.l L Y * fw.x Ya) = fw.xi Ya * fw.l L Y * fw.x Ya - s • (1 : SlopeTestRemainingChoices S A) :=
      tw_xi_l_x hW fw hF ihx ihl Y hY0 Ya m0
    show cj f fi _ = _ - s • (1 : SlopeTestRemainingChoices S A)
    rw [e, io_l0_add_kapL_eq hW fw hF Y Ya m0, cj_add', cj_sub', hl', cj_kapL_DD hW fw hF ihx ihl Y hY0 Ya m0,
      cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right hW.tz)]
    abel
  · exact cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right (Commute.zero_right _))
  · have h1 := io_commute_xi hW fw hF ihx ihl Ya m0
    have h2 := io_commute_xi hW fw hF ihx ihl (Ya - 1) mm1
    exact cj_eq_self_of_commute hW.fi_f _ (hW.kap.mul_right ((h1.mul_right h2).smul_right _).neg_right)

omit m0 in

theorem minus_m (ihc : Commute (io f : SlopeTestRemainingChoices S A) fw.c) (mm1 : Ya - 1 ∈ fw.inv) : Tw f fi (star s) (fw.m L Ya) := by
  obtain ⟨hcc, hcc'⟩ := hF.c_ci
  have hci : Commute (io f : SlopeTestRemainingChoices S A) fw.ci := by
    show (io f : SlopeTestRemainingChoices S A) * fw.ci = fw.ci * io f
    calc (io f : SlopeTestRemainingChoices S A) * fw.ci = fw.ci * fw.c * io f * fw.ci := by rw [hcc', one_mul]
      _ = fw.ci * (io f * fw.c) * fw.ci := by rw [ihc.eq]; simp only [mul_assoc]
      _ = fw.ci * io f := by rw [mul_assoc, mul_assoc, hcc, mul_one]
  have hdi : Commute (io f : SlopeTestRemainingChoices S A) (fw.di L) := by
    unfold Formalism.FourierDecayAlt.Fr.FrameData.di
    exact hci.mul_right ((WaveHyp.wti (S := S) hW).pow_right _)
  have hd : Commute (io f : SlopeTestRemainingChoices S A) (fw.d L) := by
    unfold Formalism.FourierDecayAlt.Fr.FrameData.d
    exact ((WaveHyp.wt (S := S) hW).pow_right _).mul_right ihc
  have hstar : ∀ x : A, star (io x : SlopeTestRemainingChoices S A) = io (star x) := by
    intro x
    first
      | (unfold io
         rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
         rfl)
      | (refine Matrix.ext fun i j => ?_
         simp [io, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.star_apply]
         split_ifs <;> simp_all)
  have hsf : star fi = f := by rw [← hW.star_f, star_star]
  have cjs : ∀ z : SlopeTestRemainingChoices S A, cj f fi (star z) = star (cj f fi z) := by
    intro z
    unfold cj
    rw [star_mul, star_mul, hstar, hstar, hW.star_f, hsf, mul_assoc]
  have hl : cj f fi (fw.l L (Ya - 1)) = fw.l L (Ya - 1) - s • (1 : SlopeTestRemainingChoices S A) := ihl (Ya - 1) mm1
  show cj f fi (fw.di L * star (fw.l L (Ya - 1)) * fw.d L) =
    fw.di L * star (fw.l L (Ya - 1)) * fw.d L - star s • (1 : SlopeTestRemainingChoices S A)
  rw [cj_mul_of_mul_inv_eq_one hW.f_fi, cj_mul_of_mul_inv_eq_one hW.f_fi, cj_eq_self_of_commute hW.fi_f _ hdi, cj_eq_self_of_commute hW.fi_f _ hd, cjs, hl,
    star_sub, star_smul, star_one, mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, di_d L fw hcc']

omit m0 in
theorem minus_F (hfree : fw.Free a) (ihc : Commute (io f : SlopeTestRemainingChoices S A) fw.c) (mm1 : Ya - 1 ∈ fw.inv) (UU : SlopeTestRemainingChoices S A) (ihF : fw.F * (io f * UU) = io f * fw.F) :
    (fw.minus L a Ya).F * (io f * (ins a (lift0 (Uinv (A := A) (star s))) * UU)) =
      io f * (fw.minus L a Ya).F := by
  have hfl : FreeOf a (fw.l L (Ya - 1)) := fun i j => by
    unfold Formalism.FourierDecayAlt.Fr.FrameData.l Fr.kapL
    exact ((commute_io_eU _ a i j).symm).add_right (((commute_io_eU _ a i j).symm).mul_right (hfree.2.2.2.2.2.2.2.2 (Ya - 1) i j))
  have hfm : FreeOf a (fw.m L Ya) := fun i j => by
    have hs : Commute (eU a i j) (star (fw.l L (Ya - 1))) := by
      have h := (hfl j i).star_star
      rwa [star_eU_apply_swap] at h
    unfold Formalism.FourierDecayAlt.Fr.FrameData.m Formalism.FourierDecayAlt.Fr.FrameData.di Formalism.FourierDecayAlt.Fr.FrameData.d Fr.wti Fr.wt
    exact (((hfree.2.2.2.2.2.2.2.1 i j).mul_right ((commute_io_eU _ a i j).symm.pow_right _)).mul_right hs).mul_right
      (((commute_io_eU _ a i j).symm.pow_right _).mul_right (hfree.2.2.2.2.2.2.1 i j))
  have hD : FreeOf2 a (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * fw.m L Ya, io L.GG] : M2 (SlopeTestRemainingChoices S A)) := by
    rw [Matrix.mul_fin_two]
    intro p q i j
    have hio : ∀ g : A, Commute (eU a i j) (io g : SlopeTestRemainingChoices S A) := fun g => (commute_io_eU g a i j).symm
    fin_cases p <;> fin_cases q
    · exact ((hio _).mul_right (Commute.one_right _)).add_right ((Commute.zero_right _).mul_right ((hio _).mul_right (hfm i j)))
    · exact ((hio _).mul_right (Commute.zero_right _)).add_right ((Commute.zero_right _).mul_right (hio _))
    · exact ((Commute.zero_right _).mul_right (Commute.one_right _)).add_right ((hio _).mul_right ((hio _).mul_right (hfm i j)))
    · exact ((Commute.zero_right _).mul_right (Commute.zero_right _)).add_right ((hio _).mul_right (hio _))
  have hz := mem_zfns L
  have hE := block_twist hW.f_fi hW.fi_f (star s) (io L.ζbi) (io L.ζi) (io L.GG) (fw.m L Ya) (hW.io_fn hz.2.2.2.1)
    (hW.io_fn hz.2.1) (hW.io_fn hz.2.2.2.2.1)
    (minus_m (hW := hW) (fw := fw) (hF := hF) (Ya := Ya) (ihx := ihx) (ihl := ihl) (ihc := ihc) (mm1 := mm1))
  exact frame_step hW.f_fi a (star s) _ fw.F UU hD hfree.2.2.1 ihF hE

end Letters

theorem frame_twist (hL : Fr.IsStarLevel L) (hst : Fr.IsLevelStart L st) (hW : WaveHyp L st f fi s) :
    ∀ w : List (Letter ℂ S), Fr.admitted st w →
      (∀ Y, Commute (io f : SlopeTestRemainingChoices S A) ((Fr.ofWord L st w).x Y)) ∧
      Commute (io f : SlopeTestRemainingChoices S A) (Fr.ofWord L st w).c ∧
      (∀ Y ∈ (Fr.ofWord L st w).inv, Tw f fi s ((Fr.ofWord L st w).l L Y)) ∧
      (Fr.ofWord L st w).F * Vw f s w = io f * (Fr.ofWord L st w).F := by
  intro w
  induction w with
  | nil =>
    intro _
    refine ⟨fun Y => commute_io_io (hW.x Y), Commute.one_right _, fun Y hY => ?_, ?_⟩
    · show Tw f fi s (io (L.l0 Y) + Fr.kapL L * io (st.ee Y))
      have e : (io (L.l0 Y) + Fr.kapL L * io (st.ee Y) : SlopeTestRemainingChoices S A) =
          io (L.l0 Y + L.ζb * L.ζi * L.GGi * st.ee Y) := by
        simp only [Fr.kapL, io_add', io_mul']
      rw [e]
      unfold Tw
      rw [cj_io, hW.l Y hY, io_sub', io_algebraMap]
    · show (1 : SlopeTestRemainingChoices S A) * (io f * 1) = io f * 1
      simp
  | cons l w ih =>
    intro hA
    obtain ⟨hnd, hre, hpt, hpw⟩ := hA
    have hnd' : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one ∧ (w.map Letter.intersection_update_fsHerm_neg_one).Nodup :=
      List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    have hpw' := List.pairwise_cons.mp hpw
    have hAw : Fr.admitted st w :=
      ⟨hnd'.2, fun l' h => hre l' (by simp [h]), fun l' h => hpt l' (by simp [h]), hpw'.2⟩
    obtain ⟨ihx, ihc, ihl, ihF⟩ := ih hAw
    have hF := Formalism.FourierDecayAlt.P.frame_of_admissible_word A S r L st w hL hst hAw
    have hfree := Formalism.FourierDecayAlt.P.frame_free_of_new_position A S r L st w l.intersection_update_fsHerm_neg_one hnd'.1
    obtain ⟨p0, p1, pm1, -, -⟩ := hpt l (by simp)
    have hd := hpw'.1
    have m0 : l.pt ∈ (Fr.ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p0 (fun l' hl' =>
      ⟨fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e)⟩)
    have m1 : l.pt + 1 ∈ (Fr.ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ p1 (fun l' hl' =>
      ⟨fun e => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination e)⟩)
    have mm1 : l.pt - 1 ∈ (Fr.ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ pm1 (fun l' hl' =>
      ⟨fun e => hd l' hl' 1 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 2 (by norm_num) (by push_cast; linear_combination e),
       fun e => hd l' hl' 0 (by norm_num) (by push_cast; linear_combination e)⟩)
    by_cases hp : l.plus
    · have e : Fr.ofWord L st (l :: w) = (Fr.ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [Fr.ofWord, hp]
      have eV : (Vw f s (l :: w) : SlopeTestRemainingChoices S A) = io f * (ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) s)) * UUiw s w) := by
        simp [Vw, UUiw, hp]
      rw [e, eV]
      exact ⟨commute_io_plus_x hW _ hF l.intersection_update_fsHerm_neg_one l.pt ihx, plus_c hW _ hF l.intersection_update_fsHerm_neg_one l.pt ihx ihl ihc m1,
        plus_l hW _ hF l.intersection_update_fsHerm_neg_one l.pt m0 ihx ihl, plus_F hW _ hF l.intersection_update_fsHerm_neg_one l.pt m0 ihx ihl hfree _ ihF⟩
    · have e : Fr.ofWord L st (l :: w) = (Fr.ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [Fr.ofWord, hp]
      have eV : (Vw f s (l :: w) : SlopeTestRemainingChoices S A) =
          io f * (ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (star s))) * UUiw s w) := by
        simp [Vw, UUiw, hp]
      rw [e, eV]
      exact ⟨commute_io_minus_x hW _ hF l.intersection_update_fsHerm_neg_one l.pt ihx, minus_c hW _ hF l.intersection_update_fsHerm_neg_one l.pt ihx ihl ihc mm1,
        minus_l hW _ hF l.intersection_update_fsHerm_neg_one l.pt m0 ihx ihl mm1, minus_F hW _ hF l.intersection_update_fsHerm_neg_one l.pt ihx ihl hfree ihc mm1 _ ihF⟩

theorem frame_twist_F (hL : Fr.IsStarLevel L) (hst : Fr.IsLevelStart L st) (hW : WaveHyp L st f fi s)
    (w : List (Letter ℂ S)) (hw : Fr.admitted st w) :
    (Fr.ofWord L st w).F * Vw f s w = io f * (Fr.ofWord L st w).F ∧
      Commute (io f : SlopeTestRemainingChoices S A) ((Fr.ofWord L st w).d L) := by
  obtain ⟨-, hc, -, hF⟩ := frame_twist hL hst hW w hw
  refine ⟨hF, ?_⟩
  unfold Formalism.FourierDecayAlt.Fr.FrameData.d
  exact ((WaveHyp.wt (S := S) hW).pow_right _).mul_right hc

end Frame

end TwistedTransfer

end Formalism.FourierDecayAlt.P5
