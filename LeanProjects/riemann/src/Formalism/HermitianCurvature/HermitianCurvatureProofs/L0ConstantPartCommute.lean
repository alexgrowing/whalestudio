import Formalism.HermitianCurvature.StatementFr
import Formalism.YangianSpanCharacter.YangianRelationFirst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleSS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuasiDeterminantFromEntries

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

namespace Formalism.FourierDecayAlt.P.Fr3

section Io

variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

lemma io_mul (x y : A) : (io (x * y) : SlopeTestRemainingChoices S A) = io x * io y := by
  unfold io
  exact map_mul _ x y

lemma io_add (x y : A) : (io (x + y) : SlopeTestRemainingChoices S A) = io x + io y := by
  unfold io
  exact map_add _ x y

lemma io_one : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := by
  unfold io
  exact map_one _

lemma io_comm {x y : A} (h : Commute x y) : Commute (io x : SlopeTestRemainingChoices S A) (io y) := by
  unfold Commute SemiconjBy
  rw [← io_mul, ← io_mul, h.eq]

lemma io_star [StarRing A] (x : A) : star (io x : SlopeTestRemainingChoices S A) = io (star x) := by
  unfold io
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose]
  rfl

end Io

section Level

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

lemma zsub {x : A} (hx : x ∈ zfns L) : x ∈ L.fns := by
  unfold zfns at hx
  unfold LevelData.fns
  simp only [Set.mem_union]
  tauto

lemma zc {x y : A} (hx : x ∈ zfns L) (hy : y ∈ zfns L) : Commute x y :=
  L.fns_comm x (zsub L hx) y (zsub L hy)

lemma mζ : L.ζ ∈ zfns L := by
  unfold zfns
  simp
lemma mζi : L.ζi ∈ zfns L := by
  unfold zfns
  simp
lemma mζb : L.ζb ∈ zfns L := by
  unfold zfns
  simp
lemma mζbi : L.ζbi ∈ zfns L := by
  unfold zfns
  simp
lemma mGG : L.GG ∈ zfns L := by
  unfold zfns
  simp
lemma mGGi : L.GGi ∈ zfns L := by
  unfold zfns
  simp

lemma l0_constant_part_commute (Y : ℂ) {g : A} (hg : g ∈ zfns L) :
    Commute (algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) g :=
  (Algebra.commute_algebraMap_left _ g).mul_left ((zc L (mζb L) hg).mul_left (zc L (mGGi L) hg))

lemma zetaInv_mul_l0_mul_zeta (Y : ℂ) : L.ζi * L.l0 Y * L.ζ = L.l0 Y - L.ζi := by
  have c := l0_constant_part_commute L Y (mζ L)
  have h1 : L.ζi * (-L.nab) * L.ζ = -L.nab - L.ζi := by
    rw [mul_neg, neg_mul, mul_assoc, L.nab_ζ, mul_add, ← mul_assoc, L.ζi_ζ, one_mul, mul_one]; abel
  have h2 : L.ζi * (algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) * L.ζ =
      algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi) := by
    rw [mul_assoc, c.eq, ← mul_assoc, L.ζi_ζ, one_mul]
  unfold LevelData.l0
  rw [mul_sub, sub_mul, h1, h2]; abel

lemma l0_mul_gg_eq_gg_mul_sub (Y : ℂ) : L.l0 Y * L.GG = L.GG * (L.l0 Y - L.ζb * L.GGi) := by
  have c := l0_constant_part_commute L Y (mGG L)
  have h : L.GG * (L.ζb * L.GGi) = L.ζb := by
    rw [(zc L (mζb L) (mGGi L)).eq, ← mul_assoc, L.GG_GGi, one_mul]
  unfold LevelData.l0
  rw [sub_mul, c.eq, neg_mul, L.nab_GG, mul_sub, mul_sub, h, mul_neg]; abel

lemma zetaConj2 : L.ζb * L.GGi - L.ζi = L.TT • (L.ζi * L.GGi) := by
  obtain ⟨p, pb, c, ci, cb, cbi, ζ, ζi, ζb, ζbi, GG, GGi, nab, nabs, TT, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12⟩ := L
  dsimp only
  subst h12
  have e : ζi * (ζ * ζb - algebraMap ℂ A TT) = ζb - TT • ζi := by
    rw [mul_sub, ← mul_assoc, h7, one_mul, Algebra.smul_def, Algebra.commutes]
  calc ζb * GGi - ζi = ζb * GGi - ζi * ((ζ * ζb - algebraMap ℂ A TT) * GGi) := by
        rw [h10, mul_one]
    _ = ζb * GGi - (ζb - TT • ζi) * GGi := by rw [← mul_assoc, e]
    _ = TT • (ζi * GGi) := by
        rw [sub_mul, smul_mul_assoc]
        abel

end Level

lemma eeConj_abs {B : Type} [Ring B] (G Gi x xi l0 z κ κi e D : B)
    (hG : Gi * G = 1) (hκ : κi * κ = 1) (hx : xi * x = 1)
    (c1 : l0 * G = G * (l0 - z)) (cxl : Commute x l0) (cxz : Commute x z) (cxκ : Commute x κ)
    (cκG : Commute κ G) (ceG : Commute e G)
    (h : G * x * (l0 + κ * e) - (l0 + κ * e) * (G * x) = -(G * x * (-z + κ * D))) :
    xi * e * x - D = e := by
  have e1 : (l0 + κ * e) * (G * x) = G * (x * l0) - G * (x * z) + G * (κ * (e * x)) := by
    calc (l0 + κ * e) * (G * x) = (l0 * G) * x + κ * (e * G) * x := by noncomm_ring
      _ = G * (l0 - z) * x + κ * (G * e) * x := by rw [c1, ceG.eq]
      _ = G * (l0 * x) - G * (z * x) + (κ * G) * (e * x) := by noncomm_ring
      _ = _ := by rw [← cxl.eq, ← cxz.eq, cκG.eq, mul_assoc]
  have e2 : G * x * (l0 + κ * e) = G * (x * l0) + G * (κ * (x * e)) := by
    calc G * x * (l0 + κ * e) = G * (x * l0) + G * ((x * κ) * e) := by noncomm_ring
      _ = _ := by rw [cxκ.eq, mul_assoc]
  have e3 : G * x * (-z + κ * D) = -(G * (x * z)) + G * (κ * (x * D)) := by
    calc G * x * (-z + κ * D) = -(G * (x * z)) + G * ((x * κ) * D) := by noncomm_ring
      _ = _ := by rw [cxκ.eq, mul_assoc]
  rw [e1, e2, e3] at h
  have h' : G * (κ * (x * e + x * D - e * x)) = 0 := by
    have t : G * (κ * (x * e + x * D - e * x)) =
        (G * (x * l0) + G * (κ * (x * e)) - (G * (x * l0) - G * (x * z) + G * (κ * (e * x)))) -
          -(-(G * (x * z)) + G * (κ * (x * D))) := by noncomm_ring
    rw [t, h, sub_self]
  have h'' : x * e + x * D - e * x = 0 := by
    calc x * e + x * D - e * x = κi * (Gi * (G * (κ * (x * e + x * D - e * x)))) := by
          rw [← mul_assoc Gi, hG, one_mul, ← mul_assoc κi, hκ, one_mul]
      _ = 0 := by rw [h', mul_zero, mul_zero]
  have h3 : e * x = x * e + x * D := (sub_eq_zero.mp h'').symm
  rw [mul_assoc, h3, mul_add, ← mul_assoc, ← mul_assoc, hx, one_mul, one_mul, add_sub_cancel_right]

section Frame

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ} {L : LevelData A r} {f : FrameData S A}

lemma io_alg (c : ℂ) : (io (algebraMap ℂ A c) : SlopeTestRemainingChoices S A) = algebraMap ℂ (SlopeTestRemainingChoices S A) c := by
  unfold io
  rw [Matrix.scalar_apply, Matrix.algebraMap_eq_diagonal]
  rfl

lemma hat_apply {Y : ℂ} (hY : Y ∈ f.reg) (i j : Fin 2) : f.hatT Y i j = f.F * f.TT Y i j * f.Fi := by
  simp [FrameData.hatT, hY]

lemma hat_τ (hf : IsFrame L f) {Y : ℂ} (hY : Y ∈ f.reg) : f.hatT Y 1 1 = io L.GG * f.x Y := by
  rw [hat_apply hY, hf.frame_τ Y hY, mul_assoc, hf.F_Fi, mul_one]

lemma commute_x_l0 (hf : IsFrame L f) (Ya Y : ℂ) : Commute (f.x Ya) (io (L.l0 Y)) := by
  unfold LevelData.l0
  have e : (io (-L.nab - algebraMap ℂ A (Y + 1 / 2) * (L.ζb * L.GGi)) : SlopeTestRemainingChoices S A) =
      -io L.nab - algebraMap ℂ (SlopeTestRemainingChoices S A) (Y + 1 / 2) * (io L.ζb * io L.GGi) := by
    rw [← io_alg, ← io_mul, ← io_mul]; simp only [io, map_sub, map_neg]
  rw [e]
  exact ((hf.x_nab Ya).neg_right).sub_right ((Algebra.commute_algebraMap_right _ _).mul_right
    ((hf.x_fn Ya _ (mζb L)).mul_right (hf.x_fn Ya _ (mGGi L))))

lemma star_ζb (hL : IsStarLevel L) : star L.ζb = L.ζ := by rw [← hL.1, star_star]

lemma star_GG (hL : IsStarLevel L) : star L.GG = L.GG := by
  rw [L.GG_def, star_sub, star_mul, hL.1, star_ζb hL, ← algebraMap_star_comm, hL.2.2]

lemma star_GGi (hL : IsStarLevel L) : star L.GGi = L.GGi := by
  calc star L.GGi = star L.GGi * (L.GG * L.GGi) := by rw [L.GG_GGi, mul_one]
    _ = star (L.GG * L.GGi) * L.GGi := by rw [star_mul, star_GG hL, mul_assoc]
    _ = L.GGi := by rw [L.GG_GGi, star_one, one_mul]

lemma wt_star (hL : IsStarLevel L) : star (wt L : SlopeTestRemainingChoices S A) = wt L := by
  unfold wt
  rw [io_star, star_mul, star_mul, hL.1, star_ζb hL, star_GGi hL,
    ((zc L (mGGi L) (mζ L)).mul_right (zc L (mGGi L) (mζb L))).eq]

lemma c_wt (hf : IsFrame L f) : Commute f.c (wt L) := by
  unfold wt; rw [io_mul, io_mul]
  exact ((hf.c_fn _ (mζ L)).mul_right (hf.c_fn _ (mζb L))).mul_right (hf.c_fn _ (mGGi L))

lemma d_star (hL : IsStarLevel L) (hf : IsFrame L f) : star (f.d L) = f.d L := by
  unfold FrameData.d
  rw [star_mul, star_pow, wt_star hL, hf.c_star, ((c_wt hf).pow_right _).eq]

lemma wti_wt : (wti L : SlopeTestRemainingChoices S A) * wt L = 1 := by
  have e : L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi) = 1 := by
    calc L.GG * L.ζi * L.ζbi * (L.ζ * L.ζb * L.GGi)
        = L.GG * L.ζi * (L.ζbi * L.ζ) * L.ζb * L.GGi := by simp only [mul_assoc]
      _ = L.GG * L.ζi * (L.ζ * L.ζbi) * L.ζb * L.GGi := by rw [(zc L (mζbi L) (mζ L)).eq]
      _ = L.GG * (L.ζi * L.ζ) * (L.ζbi * L.ζb) * L.GGi := by simp only [mul_assoc]
      _ = 1 := by rw [L.ζi_ζ, L.ζbi_ζb, mul_one, mul_one, L.GG_GGi]
  unfold wti wt
  rw [← io_mul, e, io_one]

lemma di_d (hf : IsFrame L f) : f.di L * f.d L = 1 := by
  have p : ∀ n : ℕ, (wti L : SlopeTestRemainingChoices S A) ^ n * wt L ^ n = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc (wti L), wti_wt, one_mul, ih]
  unfold FrameData.di FrameData.d
  rw [mul_assoc, ← mul_assoc (wti L ^ f.N), p, one_mul, hf.c_ci.2]

omit [StarRing A] [StarModule ℂ A] [Algebra ℂ A] [Fintype S] [DecidableEq S] in
lemma cancel2 {B : Type} [Ring B] {P Pi Q Qi X Y : B} (h1 : Pi * P = 1) (h2 : Q * Qi = 1)
    (h : P * X * Q = P * Y * Q) : X = Y := by
  calc X = Pi * P * X * (Q * Qi) := by rw [h1, h2, one_mul, mul_one]
    _ = Pi * (P * X * Q) * Qi := by noncomm_ring
    _ = Pi * (P * Y * Q) * Qi := by rw [h]
    _ = Pi * P * Y * (Q * Qi) := by noncomm_ring
    _ = Y := by rw [h1, h2, one_mul, mul_one]

lemma hat_herm (hf : IsFrame L f) {Z : ℂ} (hZ : Z ∈ f.reg) (hr : star Z = Z) (i j : Fin 2) :
    star (f.d L * f.hatT Z i j) = f.d L * f.hatT Z j i := by
  have h0 := hf.module.herm Z hZ hr
  have hh : ∀ i j, star (f.RR * f.TT Z i j) = f.RR * f.TT Z j i := by
    intro i j
    have := congrFun (congrFun h0 j) i
    simpa [d0, Matrix.conjTranspose_apply, Matrix.diagonal_mul] using this
  have hF : ∀ i j, f.RR * f.TT Z i j = star f.F * (f.d L * f.hatT Z i j) * f.F := by
    intro i j
    rw [hat_apply hZ, hf.form]
    calc star f.F * f.d L * f.F * f.TT Z i j
        = star f.F * f.d L * f.F * f.TT Z i j * (f.Fi * f.F) := by rw [hf.Fi_F, mul_one]
      _ = _ := by simp only [mul_assoc]
  have sF : star f.Fi * star f.F = 1 := by rw [← star_mul, hf.F_Fi, star_one]
  refine cancel2 sF hf.F_Fi ?_
  have := hh i j
  rw [hF i j, hF j i, star_mul, star_mul, star_star, ← mul_assoc] at this
  exact this

end Frame

end Formalism.FourierDecayAlt.P.Fr3

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.Fr3

theorem zeta_conj_nabla : Formalism.FourierDecayAlt.Fr.ZetaConj := by
  intro A S _ _ _ _ _ _ r L f Y hee
  refine ⟨?_, zetaConj2 L⟩
  have c : Commute (kapL L * f.ee Y : SlopeTestRemainingChoices S A) (io L.ζ) := by
    refine Commute.mul_left ?_ (hee _ (mζ L))
    exact io_comm (((zc L (mζb L) (mζ L)).mul_left (zc L (mζi L) (mζ L))).mul_left (zc L (mGGi L) (mζ L)))
  have i1 : (io L.ζi : SlopeTestRemainingChoices S A) * io L.ζ = 1 := by rw [← io_mul, L.ζi_ζ, io_one]
  have h1 : (io L.ζi : SlopeTestRemainingChoices S A) * io (L.l0 Y) * io L.ζ = io (L.l0 Y) - io L.ζi := by
    rw [← io_mul, ← io_mul, zetaInv_mul_l0_mul_zeta]; simp only [io, map_sub]
  have h2 : (io L.ζi : SlopeTestRemainingChoices S A) * (kapL L * f.ee Y) * io L.ζ = kapL L * f.ee Y := by
    rw [mul_assoc, c.eq, ← mul_assoc, i1, one_mul]
  unfold FrameData.l
  rw [mul_add, add_mul, h1, h2]; abel

theorem start_ee : Formalism.FourierDecayAlt.Fr.StartEe := by
  intro A _ _ r L SS
  have cz := (RuleSS.comm_fns_D L (zsub L (mζ L))).1
  have czb := (RuleSS.comm_fns_D L (zsub L (mζbi L))).1
  unfold LevelData.D LevelData.Dbi
  calc L.Dr * L.ζ * (L.ζbi * L.Drbi) * (L.Drb * L.Dri * SS)
      = L.Dr * (L.ζ * L.ζbi) * (L.Drbi * L.Drb) * L.Dri * SS := by simp only [mul_assoc]
    _ = (L.ζ * L.ζbi) * (L.Dr * L.Dri) * SS := by
        rw [RuleGD.Drbi_Drb, mul_one, ← (cz.mul_left czb).eq]; simp only [mul_assoc]
    _ = L.ζ * L.ζbi * SS := by rw [RuleGD.Dr_Dri, mul_one]

theorem ee_conjugation : Formalism.FourierDecayAlt.Fr.EeConj := by
  intro A S _ _ _ _ _ _ r L f Y Ya hf hY hY1 hYa hYa1 hne
  obtain ⟨H, Hl⟩ := frame_gives_one_letter_hyps A S r L f hf
  have y1 := Formalism.YangianSpanCharacter.P.wedgeMapInLieAlgebra ℂ (SlopeTestRemainingChoices S A) f.hatT (fun Y => io L.GGi * f.xi Y) f.hatQ f.inv H Ya Y hYa hY
    hne.symm
  have hη := divided_difference_l A S r L f Ya Y hne.symm
  have hDD : f.DD Ya Y = f.DD Y Ya := by
    unfold FrameData.DD
    rw [← neg_sub Y Ya, ← neg_sub (f.ee Y) (f.ee Ya), inv_neg, smul_neg, neg_smul, neg_neg]
  unfold eta at y1
  rw [Hl Y hY hY1, Hl Ya hYa hYa1, hη, hat_τ hf (hf.inv_reg hYa), hDD] at y1
  unfold FrameData.l at y1
  refine eeConj_abs (io L.GG) (io L.GGi) (f.x Ya) (f.xi Ya) (io (L.l0 Y)) (io (L.ζb * L.GGi)) (kapL L)
    (io (L.GG * L.ζ * L.ζbi)) (f.ee Y) (f.DD Y Ya) ?_ ?_ (hf.x_xi Ya hYa).2 ?_ (commute_x_l0 hf Ya Y) ?_ ?_ ?_
    (hf.ee_fn Y _ (mGG L)) y1
  · rw [← io_mul, L.GGi_GG, io_one]
  · unfold kapL
    rw [← io_mul]
    have e : L.GG * L.ζ * L.ζbi * (L.ζb * L.ζi * L.GGi) = 1 := by
      calc L.GG * L.ζ * L.ζbi * (L.ζb * L.ζi * L.GGi)
          = L.GG * (L.ζ * ((L.ζbi * L.ζb) * L.ζi)) * L.GGi := by simp only [mul_assoc]
        _ = 1 := by rw [L.ζbi_ζb, one_mul, L.ζ_ζi, mul_one, L.GG_GGi]
    rw [e, io_one]
  · rw [← io_mul, l0_mul_gg_eq_gg_mul_sub, io_mul]; simp only [io, map_sub]
  · rw [io_mul]; exact (hf.x_fn Ya _ (mζb L)).mul_right (hf.x_fn Ya _ (mGGi L))
  · unfold kapL; rw [io_mul, io_mul]
    exact ((hf.x_fn Ya _ (mζb L)).mul_right (hf.x_fn Ya _ (mζi L))).mul_right (hf.x_fn Ya _ (mGGi L))
  · exact io_comm (((zc L (mζb L) (mGG L)).mul_left (zc L (mζi L) (mGG L))).mul_left (zc L (mGGi L) (mGG L)))

theorem frame_adjoint_m : Formalism.FourierDecayAlt.Fr.FrameM := by
  intro A S _ _ _ _ _ _ r L f Y hL hf hr hY hYm
  obtain ⟨H, Hl⟩ := frame_gives_one_letter_hyps A S r L f hf
  have hr' : star (Y - 1) = Y - 1 := by rw [star_sub, hr, star_one]
  have hY' : Y - 1 + 1 ∈ f.inv := by rwa [sub_add_cancel]
  have adj := adjoint_l_shift_relation ℂ (SlopeTestRemainingChoices S A) f.hatT (fun Y => io L.GGi * f.xi Y) f.hatQ f.inv (f.d L) H
    (d_star hL hf) (Y - 1) hYm hY' (hat_herm hf (hf.inv_reg hYm) hr')
  rw [Hl (Y - 1) hYm hY', sub_add_cancel] at adj
  have hm : mf f.hatT (fun Y => io L.GGi * f.xi Y) Y = f.m L Y := by
    unfold FrameData.m
    rw [mul_assoc, ← adj, ← mul_assoc, di_d hf, one_mul]
  have hτ : io L.GG * f.x Y * (io L.GGi * f.xi Y) = 1 := by
    have := (H.2.2.2.1 Y hY).1
    rwa [hat_τ hf (hf.inv_reg hY)] at this
  rw [← hm]
  unfold mf
  rw [← mul_assoc (io L.GG * f.x Y), hτ, one_mul, hat_apply (hf.inv_reg hY), mul_assoc, hf.Fi_F, mul_one]

theorem minus_letter_last_entry : Formalism.FourierDecayAlt.Fr.MinusLast := by
  intro A S _ _ _ _ _ _ r L f b Yb hH Y hY hY1
  obtain ⟨hL, hf, hfree, hre, i0, i1, im1, hq⟩ := hH
  have e := ee_conjugation A S r L f Y Yb hf hY.1 hY1.1 i0 i1 (by intro e; apply hY.2.1; rw [e]; ring)
  simp only [FrameData.minus]
  rw [e]

theorem new_vector_letter_plus : Formalism.FourierDecayAlt.Fr.NewLetterPlus := by
  intro A S _ _ _ _ _ _ r L f Y hee
  have a1 : L.Di * L.Ahat Y = L.ζi * L.Ar Y := by
    unfold LevelData.Di LevelData.Ahat
    rw [mul_assoc, ← mul_assoc L.Dri, RuleGD.Dri_Dr, one_mul]
  have a2 : L.Dbi * L.R0 Y = L.ζbi * L.GG * (L.l0 Y * L.Ar Y + L.Br Y) := by
    unfold LevelData.Dbi LevelData.R0
    simp only [mul_assoc]; rw [← mul_assoc L.Drbi, RuleGD.Drbi_Drb, one_mul]
  have k0 : L.ζbi * L.GG * (L.ζb * L.ζi * L.GGi) = L.ζi := by
    calc L.ζbi * L.GG * (L.ζb * L.ζi * L.GGi) = L.ζbi * (L.GG * (L.ζb * L.ζi)) * L.GGi := by
          simp only [mul_assoc]
      _ = L.ζbi * ((L.ζb * L.ζi) * L.GG) * L.GGi := by
          rw [((zc L (mGG L) (mζb L)).mul_right (zc L (mGG L) (mζi L))).eq]
      _ = (L.ζbi * L.ζb) * L.ζi * (L.GG * L.GGi) := by simp only [mul_assoc]
      _ = L.ζi := by rw [L.ζbi_ζb, L.GG_GGi, one_mul, mul_one]
  have k : (io L.ζbi : SlopeTestRemainingChoices S A) * io L.GG * kapL L = io L.ζi := by
    unfold kapL; rw [← io_mul, ← io_mul, k0]
  have key : (io L.ζbi : SlopeTestRemainingChoices S A) * (io L.GG * f.l L Y) * io (L.Ar Y) + io L.ζbi * io L.GG * io (L.Br Y) =
      io L.ζbi * io L.GG * (io (L.l0 Y) * io (L.Ar Y) + io (L.Br Y)) +
        f.ee Y * (io L.ζi * io (L.Ar Y)) := by
    unfold FrameData.l
    calc (io L.ζbi : SlopeTestRemainingChoices S A) * (io L.GG * (io (L.l0 Y) + kapL L * f.ee Y)) * io (L.Ar Y) +
          io L.ζbi * io L.GG * io (L.Br Y)
        = io L.ζbi * io L.GG * (io (L.l0 Y) * io (L.Ar Y) + io (L.Br Y)) +
          (io L.ζbi * io L.GG * kapL L) * f.ee Y * io (L.Ar Y) := by noncomm_ring
      _ = _ := by rw [k, ← (hee _ (mζi L)).eq, mul_assoc (f.ee Y)]
  ext1 i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, a1, io_mul]
  · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, a1, a2, io_mul, io_add] using key

end Formalism.FourierDecayAlt.P
