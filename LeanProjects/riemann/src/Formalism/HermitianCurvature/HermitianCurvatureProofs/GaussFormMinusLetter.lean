import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuasiDeterminantFromEntries

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

namespace Formalism.FourierDecayAlt.P.Fr8

section Mon

variable {M : Type} [Monoid M]

theorem mon1 {z zi w wi gi : M} (hz : z * zi = 1) (hw : w * wi = 1) (c1 : Commute gi zi)
    (c2 : Commute w zi) (c3 : Commute gi wi) : z * w * gi * zi * wi = gi := by
  calc z * w * gi * zi * wi = z * (w * (gi * zi)) * wi := by simp only [mul_assoc]
    _ = z * (w * zi * gi) * wi := by rw [c1.eq, ← mul_assoc w zi gi]
    _ = z * zi * (w * (gi * wi)) := by rw [c2.eq]; simp only [mul_assoc]
    _ = gi := by rw [hz, one_mul, c3.eq, ← mul_assoc w wi gi, hw, one_mul]

theorem mon2 {z zi w wi g gi : M} (hz : z * zi = 1) (hw : w * wi = 1) (hg : gi * g = 1) :
    z * w * gi * (g * wi) * (zi * g) = g := by
  simp only [mul_assoc]
  rw [← mul_assoc gi g, hg, one_mul, ← mul_assoc w wi, hw, one_mul, ← mul_assoc z zi, hz, one_mul]

theorem mon3 {z zi w wi g gi : M} (hz : zi * z = 1) (hw : wi * w = 1) (hg : g * gi = 1)
    (c : Commute wi z) : g * zi * wi * (z * w * gi) = 1 := by
  simp only [mul_assoc]
  rw [← mul_assoc wi z, c.eq, mul_assoc z wi, ← mul_assoc zi z, hz, one_mul, ← mul_assoc wi w, hw, one_mul, hg]

theorem comm_inv {x xi g : M} (h1 : x * xi = 1) (h2 : xi * x = 1) (c : Commute x g) : Commute xi g := by
  show xi * g = g * xi
  calc xi * g = xi * g * (x * xi) := by rw [h1, mul_one]
    _ = xi * (g * x) * xi := by simp only [mul_assoc]
    _ = xi * (x * g) * xi := by rw [← c.eq]
    _ = g * xi := by rw [← mul_assoc xi x g, h2, one_mul]

end Mon

theorem star_inv {R : Type} [Ring R] [StarRing R] {a b a' b' : R} (h1 : a * b = 1) (h : star a = a')
    (h2 : a' * b' = 1) : star b = b' := by
  have e : star b * a' = 1 := by rw [← h, ← star_mul, h1, star_one]
  calc star b = star b * (a' * b') := by rw [h2, mul_one]
    _ = b' := by rw [← mul_assoc, e, one_mul]

section Slots

variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem io_mul (x y : A) : (io (x * y) : SlopeTestRemainingChoices S A) = io x * io y := by
  simp only [Formalism.FourierDecayAlt.Wd.io, map_mul]

theorem io_one : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := by
  simp only [Formalism.FourierDecayAlt.Wd.io, map_one]

theorem io_star [StarRing A] (x : A) : star (io x : SlopeTestRemainingChoices S A) = io (star x) := by
  simp only [Formalism.FourierDecayAlt.Wd.io]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.star_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem free_io (c : S) (x : A) : FreeOf c (io x : SlopeTestRemainingChoices S A) := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf
  intro i j
  show Formalism.FourierDecayAlt.Wd.eU c i j * Formalism.FourierDecayAlt.Wd.io x = Formalism.FourierDecayAlt.Wd.io x * Formalism.FourierDecayAlt.Wd.eU c i j
  simp only [Formalism.FourierDecayAlt.Wd.io, Matrix.scalar_apply]
  refine Matrix.ext fun u v => ?_
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Formalism.FourierDecayAlt.Wd.eU, Matrix.of_apply]
  split_ifs <;> simp

theorem free_one (c : S) : FreeOf c (1 : SlopeTestRemainingChoices S A) := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf
  intro i j
  exact Commute.one_right _

theorem free_zero (c : S) : FreeOf c (0 : SlopeTestRemainingChoices S A) := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf
  intro i j
  exact Commute.zero_right _

theorem free_mul {c : S} {b b' : SlopeTestRemainingChoices S A} (h : FreeOf c b) (h' : FreeOf c b') : FreeOf c (b * b') := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf at h h' ⊢
  intro i j
  exact (h i j).mul_right (h' i j)

theorem free_add {c : S} {b b' : SlopeTestRemainingChoices S A} (h : FreeOf c b) (h' : FreeOf c b') : FreeOf c (b + b') := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf at h h' ⊢
  intro i j
  exact (h i j).add_right (h' i j)

theorem free_pow {c : S} {b : SlopeTestRemainingChoices S A} (h : FreeOf c b) (n : ℕ) : FreeOf c (b ^ n) := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf at h ⊢
  intro i j
  exact (h i j).pow_right n

theorem free_smul [Algebra ℂ A] {c : S} {b : SlopeTestRemainingChoices S A} (k : ℂ) (h : FreeOf c b) : FreeOf c (k • b) := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf at h ⊢
  intro i j
  exact (h i j).smul_right k

theorem free_star [StarRing A] {c : S} {b : SlopeTestRemainingChoices S A} (h : FreeOf c b) : FreeOf c (star b) := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf at h ⊢
  intro i j
  have key : star (Formalism.FourierDecayAlt.Wd.eU c j i : SlopeTestRemainingChoices S A) = Formalism.FourierDecayAlt.Wd.eU c i j := by
    refine Matrix.ext fun x y => ?_
    simp only [Matrix.star_apply, Formalism.FourierDecayAlt.Wd.eU, Matrix.of_apply]
    by_cases h1 : y c = j ∧ x c = i ∧ ∀ b, b ≠ c → y b = x b
    · rw [if_pos h1, if_pos ⟨h1.2.1, h1.1, fun b hb => (h1.2.2 b hb).symm⟩, star_one]
    · rw [if_neg h1, if_neg (fun h2 => h1 ⟨h2.2.1, h2.1, fun b hb => (h2.2.2 b hb).symm⟩), star_zero]
  have hs := (h j i).star_star
  rwa [key] at hs

theorem free2 {c : S} {p q r s : SlopeTestRemainingChoices S A} (hp : FreeOf c p) (hq : FreeOf c q) (hr : FreeOf c r)
    (hs : FreeOf c s) : FreeOf2 c !![p, q; r, s] := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf2
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, hs]

theorem ins2 (a : S) (p q r s : SlopeTestRemainingChoices S A) :
    ins a !![p, q; r, s] = eU a 0 0 * p + eU a 0 1 * q + eU a 1 0 * r + eU a 1 1 * s := by
  simp [Formalism.FourierDecayAlt.Wd.ins, Fin.sum_univ_two, add_assoc]

theorem ins_conj (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (P Q : SlopeTestRemainingChoices S A) (hP : FreeOf a P) :
    ins a (M.map fun b => P * b * Q) = P * ins a M * Q := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf at hP
  simp only [Formalism.FourierDecayAlt.Wd.ins, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Formalism.FourierDecayAlt.Wd.eU a i j * (P * M i j * Q) = Formalism.FourierDecayAlt.Wd.eU a i j * P * M i j * Q by
    simp only [mul_assoc], (hP i j).eq]
  simp only [mul_assoc]

end Slots

section Level

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem pow_inv {M : Type} [Monoid M] {a b : M} (h : a * b = 1) (n : ℕ) : a ^ n * b ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc a b, h, one_mul, ih]

theorem fcomm (L : LevelData A r) {x y : A} (hx : x ∈ zfns L) (hy : y ∈ zfns L) : Commute x y := by
  obtain ⟨p, pb, c, ci, cb, cbi, ζ, ζi, ζb, ζbi, GG, GGi, nab, nabs, TT, hc⟩ := L
  exact hc x (Set.mem_union_right _ hx) y (Set.mem_union_right _ hy)

theorem io_comm {x y : A} (h : Commute x y) : Commute (io x : SlopeTestRemainingChoices S A) (io y) := by
  simp only [Formalism.FourierDecayAlt.Wd.io]
  exact h.map _

theorem mζ (L : LevelData A r) : L.ζ ∈ zfns L := by
  simp [Formalism.FourierDecayAlt.Fr.zfns]
theorem mζi (L : LevelData A r) : L.ζi ∈ zfns L := by
  simp [Formalism.FourierDecayAlt.Fr.zfns]
theorem mζb (L : LevelData A r) : L.ζb ∈ zfns L := by
  simp [Formalism.FourierDecayAlt.Fr.zfns]
theorem mζbi (L : LevelData A r) : L.ζbi ∈ zfns L := by
  simp [Formalism.FourierDecayAlt.Fr.zfns]
theorem mGG (L : LevelData A r) : L.GG ∈ zfns L := by
  simp [Formalism.FourierDecayAlt.Fr.zfns]
theorem mGGi (L : LevelData A r) : L.GGi ∈ zfns L := by
  simp [Formalism.FourierDecayAlt.Fr.zfns]

theorem star_ζb {L : LevelData A r} (h : IsStarLevel L) : star L.ζb = L.ζ := by
  obtain ⟨h1, -, -⟩ := h
  rw [← h1, star_star]

theorem star_GG {L : LevelData A r} (h : IsStarLevel L) : star L.GG = L.GG := by
  obtain ⟨h1, -, h3⟩ := id h
  rw [L.GG_def, star_sub, star_mul, star_ζb h, h1, ← algebraMap_star_comm, h3]

theorem star_GGi {L : LevelData A r} (h : IsStarLevel L) : star L.GGi = L.GGi := star_inv L.GG_GGi (star_GG h) L.GG_GGi

theorem star_ζi {L : LevelData A r} (h : IsStarLevel L) : star L.ζi = L.ζbi := by
  obtain ⟨h1, -, -⟩ := h
  exact star_inv L.ζ_ζi h1 L.ζb_ζbi

theorem star_ζbi {L : LevelData A r} (h : IsStarLevel L) : star L.ζbi = L.ζi := star_inv L.ζb_ζbi (star_ζb h) L.ζ_ζi

theorem wt_eq (L : LevelData A r) : (wt L : SlopeTestRemainingChoices S A) = io L.ζ * io L.ζb * io L.GGi := by
  simp only [Formalism.FourierDecayAlt.Fr.wt, io_mul]

theorem star_wt {L : LevelData A r} (h : IsStarLevel L) : star (wt L : SlopeTestRemainingChoices S A) = wt L := by
  obtain ⟨h1, -, -⟩ := id h
  rw [Formalism.FourierDecayAlt.Fr.wt, io_star]
  congr 1
  rw [star_mul, star_mul, star_GGi h, star_ζb h, h1]
  exact ((fcomm L (mGGi L) (mζ L)).mul_right (fcomm L (mGGi L) (mζb L))).eq

theorem wt_fn (L : LevelData A r) {g : A} (hg : g ∈ zfns L) : Commute (wt L : SlopeTestRemainingChoices S A) (io g) := by
  unfold Formalism.FourierDecayAlt.Fr.wt
  exact io_comm (((fcomm L (mζ L) hg).mul_left (fcomm L (mζb L) hg)).mul_left (fcomm L (mGGi L) hg))

theorem wti_wt (L : LevelData A r) : (wti L : SlopeTestRemainingChoices S A) * wt L = 1 := by
  rw [Formalism.FourierDecayAlt.Fr.wti, Formalism.FourierDecayAlt.Fr.wt, ← io_mul, ← io_one]
  congr 1
  exact mon3 L.ζi_ζ L.ζbi_ζb L.GG_GGi (fcomm L (mζbi L) (mζ L))

variable {L : LevelData A r} {f : FrameData S A}

theorem c_wt (h : IsFrame L f) : Commute f.c (wt L) := by
  rw [wt_eq]
  exact ((h.c_fn _ (mζ L)).mul_right (h.c_fn _ (mζb L))).mul_right (h.c_fn _ (mGGi L))

theorem star_d (hS : IsStarLevel L) (h : IsFrame L f) : star (f.d L) = f.d L := by
  rw [Formalism.FourierDecayAlt.Fr.FrameData.d, star_mul, star_pow, star_wt hS, h.c_star]
  exact (c_wt h).pow_right f.N

theorem di_d (h : IsFrame L f) : f.di L * f.d L = 1 := by
  rw [Formalism.FourierDecayAlt.Fr.FrameData.di, Formalism.FourierDecayAlt.Fr.FrameData.d, mul_assoc, ← mul_assoc (Formalism.FourierDecayAlt.Fr.wti L ^ f.N),
    pow_inv (wti_wt L) f.N, one_mul, h.c_ci.2]

theorem d_m (hS : IsStarLevel L) (h : IsFrame L f) (Yb : ℂ) (hr : star Yb = Yb) (h0 : Yb ∈ f.inv)
    (h1 : Yb - 1 ∈ f.inv) :
    f.d L * mf f.hatT (fun Y => io L.GGi * f.xi Y) Yb = star (f.l L (Yb - 1)) * f.d L := by
  obtain ⟨H, Hl⟩ := frame_gives_one_letter_hyps A S r L f h
  have h1' : Yb - 1 + 1 ∈ f.inv := by rwa [sub_add_cancel]
  have hr1 : star (Yb - 1) = Yb - 1 := by rw [star_sub, hr, star_one]
  have hreg := h.inv_reg h1
  have hT : ∀ i j, f.hatT (Yb - 1) i j = f.F * f.TT (Yb - 1) i j * f.Fi := by
    intro i j; simp [FrameData.hatT, hreg]
  have sF : star f.Fi * star f.F = 1 := by rw [← star_mul, h.F_Fi, star_one]
  have key : ∀ i j, f.d L * f.hatT (Yb - 1) i j = star f.Fi * (f.RR * f.TT (Yb - 1) i j) * f.Fi := by
    intro i j
    rw [hT, h.form]
    calc f.d L * (f.F * f.TT (Yb - 1) i j * f.Fi)
        = (star f.Fi * star f.F) * f.d L * f.F * f.TT (Yb - 1) i j * f.Fi := by
          rw [sF, one_mul]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  have herm := h.module.herm _ hreg hr1
  have he : ∀ i j, star (f.RR * f.TT (Yb - 1) i j) = f.RR * f.TT (Yb - 1) j i := by
    intro i j
    have := congrFun (congrFun herm j) i
    simpa [Matrix.conjTranspose_apply, d0, Matrix.diagonal_mul] using this
  have hh : ∀ i j, star (f.d L * f.hatT (Yb - 1) i j) = f.d L * f.hatT (Yb - 1) j i := by
    intro i j
    rw [key, key, star_mul, star_mul, star_star, he]
    simp only [mul_assoc]
  have e := adjoint_l_shift_relation ℂ (SlopeTestRemainingChoices S A) f.hatT _ f.hatQ f.inv (f.d L) H (star_d hS h) (Yb - 1) h1 h1' hh
  rw [sub_add_cancel, Hl (Yb - 1) h1 h1'] at e
  exact e

end Level

theorem ct2 {R : Type} [Star R] (a b c d : R) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R)ᴴ = !![star a, star c; star b, star d] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

theorem asm {R : Type} [Ring R] [StarRing R] {F Fi d U D Λ : R} (hFFi : F * Fi = 1)
    (hU : d * U = star Λ * d) :
    star F * d * F * (Fi * (U * D * Λ) * F) = star (Λ * F) * (d * D) * (Λ * F) := by
  rw [star_mul]
  calc star F * d * F * (Fi * (U * D * Λ) * F) = star F * d * (F * Fi) * U * D * Λ * F := by
        simp only [mul_assoc]
    _ = star F * (d * U) * D * Λ * F := by rw [hFFi, mul_one]; simp only [mul_assoc]
    _ = star F * star Λ * (d * D) * (Λ * F) := by rw [hU]; simp only [mul_assoc]

theorem gaussFormMinus : GaussFormMinus := by
  intro A S _ _ _ _ _ _ r L f b Yb hyp
  obtain ⟨hS, h, hF, hr, h0, -, h1, -⟩ := hyp
  obtain ⟨H, Hl⟩ := frame_gives_one_letter_hyps A S r L f h
  obtain ⟨-, -, -, fFi, fx, fxi, fc, fci, fee⟩ := hF
  have h1' : Yb - 1 + 1 ∈ f.inv := by rwa [sub_add_cancel]
  have hdm := d_m hS h Yb hr h0 h1
  have hm : mf f.hatT (fun Y => io L.GGi * f.xi Y) Yb = f.m L Yb := by
    unfold FrameData.m
    rw [mul_assoc, ← hdm, ← mul_assoc, di_d h, one_mul]
  have G := gauss_decomp_minus_letter ℂ (SlopeTestRemainingChoices S A) f.hatT _ f.hatQ f.inv H Yb h0 h1
  have hQ : f.hatQ (Yb - 1) = f.q (Yb - 1) := by
    simp [FrameData.hatQ, h.inv_reg h1, h.inv_reg h0]
  have hτ : f.hatT Yb 1 1 = io L.GG * f.x Yb := by
    have : f.hatT Yb 1 1 = f.F * f.TT Yb 1 1 * f.Fi := by simp [FrameData.hatT, h.inv_reg h0]
    rw [this, h.frame_τ Yb (h.inv_reg h0), mul_assoc, h.F_Fi, mul_one]
  rw [hm, Hl (Yb - 1) h1 h1', hQ, hτ] at G
  rw [hm] at hdm
  have hT : (f.TT Yb)ᵀ = (f.hatT Yb)ᵀ.map (fun c => f.Fi * c * f.F) := by
    refine Matrix.ext fun i j => ?_
    have : f.hatT Yb j i = f.F * f.TT Yb j i * f.Fi := by simp [FrameData.hatT, h.inv_reg h0]
    rw [Matrix.map_apply, Matrix.transpose_apply, Matrix.transpose_apply, this]
    calc f.TT Yb j i = (f.Fi * f.F) * f.TT Yb j i * (f.Fi * f.F) := by rw [h.Fi_F, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]

  have fd : FreeOf b (f.d L) := free_mul (free_pow (free_io b _) _) fc
  have fdi : FreeOf b (f.di L) := free_mul fci (free_pow (free_io b _) _)
  have fl : FreeOf b (f.l L (Yb - 1)) := free_add (free_io b _) (free_mul (free_io b _) (fee _))
  have fm : FreeOf b (f.m L Yb) := free_mul (free_mul fdi (free_star fl)) fd
  have fU : FreeOf2 b !![1, f.l L (Yb - 1); 0, 1] := free2 (free_one b) fl (free_zero b) (free_one b)
  have fD : FreeOf2 b !![f.q (Yb - 1) • (io L.GGi * f.xi (Yb - 1)), 0; 0, io L.GG * f.x Yb] :=
    free2 (free_smul _ (free_mul (free_io b _) (fxi _))) (free_zero b) (free_zero b)
      (free_mul (free_io b _) (fx _))
  have fΛ : FreeOf2 b !![1, 0; f.m L Yb, 1] := free2 (free_one b) (free_zero b) fm (free_one b)
  have fUD : FreeOf2 b (!![1, f.l L (Yb - 1); 0, 1] *
      !![f.q (Yb - 1) • (io L.GGi * f.xi (Yb - 1)), 0; 0, io L.GG * f.x Yb]) := by
    intro i j k l
    rw [Matrix.mul_apply]
    exact Commute.sum_right _ _ _ fun m _ => (fU i m k l).mul_right (fD m j k l)
  have hsm : star (f.m L Yb) * f.d L = f.d L * f.l L (Yb - 1) := by
    have := congrArg star hdm
    rw [star_mul, star_mul, star_star, star_d hS h] at this
    exact this
  have hΛH : (!![1, 0; f.m L Yb, 1] : M2 (SlopeTestRemainingChoices S A))ᴴ = !![1, star (f.m L Yb); 0, 1] := by
    rw [ct2, star_one, star_zero]
  have hU : f.d L * ins b !![1, f.l L (Yb - 1); 0, 1] = star (ins b !![1, 0; f.m L Yb, 1]) * f.d L := by
    rw [Wd1.ins_star b _ fΛ, hΛH, ins2, ins2]
    simp only [mul_one, mul_zero, add_zero, mul_add, add_mul]
    rw [(fd 0 0).eq, (fd 1 1).eq, mul_assoc (eU b 0 1), hsm, ← mul_assoc, ← mul_assoc, (fd 0 1).eq]
  rw [hT, ins_conj b _ _ _ fFi, G, Wd1.ins_mul b _ _ fUD, Wd1.ins_mul b _ _ fU, h.form]
  exact asm h.F_Fi hU

theorem diag_mul {R : Type} [Ring R] (a b c d : R) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) R) * !![c, 0; 0, d] = !![a * c, 0; 0, b * d] := by
  rw [Matrix.mul_fin_two]
  simp

theorem minusForm : MinusForm := by
  intro A S _ _ _ _ _ _ r L f b Yb hyp
  have G := gaussFormMinus A S r L f b Yb hyp
  obtain ⟨hS, h, hF, hr, h0, -, h1, -⟩ := hyp
  obtain ⟨-, -, -, -, fx, fxi, fc, -, -⟩ := hF
  show f.RR * ins b (f.TT Yb)ᵀ =
    star (ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F) *
      (wt L ^ (f.N + 1) * (f.c * ins b !![f.q (Yb - 1) • f.xi (Yb - 1), 0; 0, f.x Yb])) *
      (ins b (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG]) * f.F)
  rw [G]
  have hEG : (!![io L.ζbi, 0; 0, io L.ζi] * !![1, 0; io L.GG * f.m L Yb, io L.GG] : M2 (SlopeTestRemainingChoices S A)) =
      !![io L.ζbi, 0; 0, io L.ζi * io L.GG] * !![1, 0; f.m L Yb, 1] := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]
  have fE : FreeOf2 b (!![io L.ζbi, 0; 0, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) :=
    free2 (free_io b _) (free_zero b) (free_zero b) (free_mul (free_io b _) (free_io b _))
  have fEH : FreeOf2 b (!![io L.ζi, 0; 0, io L.GG * io L.ζbi] : M2 (SlopeTestRemainingChoices S A)) :=
    free2 (free_io b _) (free_zero b) (free_zero b) (free_mul (free_io b _) (free_io b _))
  have fW : FreeOf2 b (!![wt L, 0; 0, wt L] : M2 (SlopeTestRemainingChoices S A)) :=
    free2 (free_io b _) (free_zero b) (free_zero b) (free_io b _)
  have hEH : (!![io L.ζbi, 0; 0, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A))ᴴ =
      !![io L.ζi, 0; 0, io L.GG * io L.ζbi] := by
    rw [ct2, star_zero, star_mul, io_star, io_star, io_star, star_ζbi hS, star_ζi hS, star_GG hS]
  have hW : ins b (!![wt L, 0; 0, wt L] : M2 (SlopeTestRemainingChoices S A)) = wt L := by
    have e : (!![wt L, 0; 0, wt L] : M2 (SlopeTestRemainingChoices S A)) = d0 (wt L) := by
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [d0]
    rw [e, Wd1.insert_diagonal_extract]

  have dg : ∀ g ∈ zfns L, Commute (wt L ^ (f.N + 1) * f.c) (io g) := fun g hg =>
    ((wt_fn L hg).pow_left _).mul_left (h.c_fn g hg)
  have cE : Commute (wt L ^ (f.N + 1) * f.c) (ins b (!![io L.ζi, 0; 0, io L.GG * io L.ζbi] : M2 (SlopeTestRemainingChoices S A))) := by
    refine Wd1.ins_comm b _ _ (free_mul (free_pow (free_io b _) _) fc) ?_
    intro i j
    fin_cases i <;> fin_cases j
    · exact dg _ (mζi L)
    · exact Commute.zero_right _
    · exact Commute.zero_right _
    · exact (dg _ (mGG L)).mul_right (dg _ (mζbi L))

  have iz : (io L.ζ : SlopeTestRemainingChoices S A) * io L.ζi = 1 := by rw [← io_mul, L.ζ_ζi, io_one]
  have iw : (io L.ζb : SlopeTestRemainingChoices S A) * io L.ζbi = 1 := by rw [← io_mul, L.ζb_ζbi, io_one]
  have ig : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by rw [← io_mul, L.GGi_GG, io_one]
  obtain ⟨x1, x2⟩ := h.x_xi _ h1
  have e00 : wt L * io L.ζi * (f.q (Yb - 1) • f.xi (Yb - 1)) * io L.ζbi =
      f.q (Yb - 1) • (io L.GGi * f.xi (Yb - 1)) := by
    rw [mul_smul_comm, smul_mul_assoc, mul_assoc, (comm_inv x1 x2 (h.x_fn _ _ (mζbi L))).eq, ← mul_assoc,
      wt_eq, mon1 iz iw (io_comm (fcomm L (mGGi L) (mζi L))) (io_comm (fcomm L (mζb L) (mζi L)))
        (io_comm (fcomm L (mGGi L) (mζbi L)))]
  have e11 : wt L * (io L.GG * io L.ζbi) * f.x Yb * (io L.ζi * io L.GG) = io L.GG * f.x Yb := by
    rw [mul_assoc, ((h.x_fn Yb _ (mζi L)).mul_right (h.x_fn Yb _ (mGG L))).eq, ← mul_assoc, wt_eq,
      mon2 iz iw ig]
  have key : f.d L * ins b !![f.q (Yb - 1) • (io L.GGi * f.xi (Yb - 1)), 0; 0, io L.GG * f.x Yb] =
      star (ins b !![io L.ζbi, 0; 0, io L.ζi * io L.GG]) *
        (wt L ^ (f.N + 1) * (f.c * ins b !![f.q (Yb - 1) • f.xi (Yb - 1), 0; 0, f.x Yb])) *
        ins b !![io L.ζbi, 0; 0, io L.ζi * io L.GG] := by
    rw [Wd1.ins_star b _ fE, hEH, ← e00, ← e11, ← diag_mul, ← diag_mul, ← diag_mul]
    have f1 : FreeOf2 b (!![wt L, 0; 0, wt L] * !![io L.ζi, 0; 0, io L.GG * io L.ζbi] : M2 (SlopeTestRemainingChoices S A)) := by
      rw [diag_mul]
      exact free2 (free_mul (free_io b _) (free_io b _)) (free_zero b) (free_zero b)
        (free_mul (free_io b _) (free_mul (free_io b _) (free_io b _)))
    have f2 : FreeOf2 b (!![wt L, 0; 0, wt L] * !![io L.ζi, 0; 0, io L.GG * io L.ζbi] *
        !![f.q (Yb - 1) • f.xi (Yb - 1), 0; 0, f.x Yb] : M2 (SlopeTestRemainingChoices S A)) := by
      rw [diag_mul, diag_mul]
      exact free2 (free_mul (free_mul (free_io b _) (free_io b _)) (free_smul _ (fxi _))) (free_zero b)
        (free_zero b) (free_mul (free_mul (free_io b _) (free_mul (free_io b _) (free_io b _))) (fx _))
    rw [Wd1.ins_mul b _ _ f2, Wd1.ins_mul b _ _ f1, Wd1.ins_mul b _ _ fW, hW]
    unfold FrameData.d
    generalize ins b (!![io L.ζi, 0; 0, io L.GG * io L.ζbi] : M2 (SlopeTestRemainingChoices S A)) = EH at cE ⊢
    generalize ins b (!![f.q (Yb - 1) • f.xi (Yb - 1), 0; 0, f.x Yb] : M2 (SlopeTestRemainingChoices S A)) = C
    generalize ins b (!![io L.ζbi, 0; 0, io L.ζi * io L.GG] : M2 (SlopeTestRemainingChoices S A)) = E
    calc wt L ^ f.N * f.c * (wt L * EH * C * E) = wt L ^ f.N * (f.c * wt L) * EH * C * E := by
          simp only [mul_assoc]
      _ = (wt L ^ f.N * wt L * f.c) * EH * C * E := by rw [(c_wt h).eq]; simp only [mul_assoc]
      _ = (wt L ^ (f.N + 1) * f.c) * EH * C * E := by rw [pow_succ]
      _ = EH * (wt L ^ (f.N + 1) * f.c) * C * E := by rw [cE.eq]
      _ = EH * (wt L ^ (f.N + 1) * (f.c * C)) * E := by simp only [mul_assoc]
  rw [hEG, Wd1.ins_mul b _ _ fE, key]
  simp only [star_mul, mul_assoc]

end Formalism.FourierDecayAlt.P.Fr8

namespace Formalism.FourierDecayAlt.P

theorem gauss_form_minus_letter : Formalism.FourierDecayAlt.Fr.GaussFormMinus := Formalism.FourierDecayAlt.P.Fr8.gaussFormMinus

theorem minus_letter_form : Formalism.FourierDecayAlt.Fr.MinusForm := Formalism.FourierDecayAlt.P.Fr8.minusForm

end Formalism.FourierDecayAlt.P
