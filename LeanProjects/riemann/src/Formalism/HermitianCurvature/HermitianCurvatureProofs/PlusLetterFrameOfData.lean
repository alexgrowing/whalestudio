import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

namespace Formalism.FourierDecayAlt.P.Fr7

open Formalism.FourierDecayAlt.P.Wd1

theorem comm_inv {B : Type} [Monoid B] {x xi b : B} (h1 : x * xi = 1) (h2 : xi * x = 1)
    (h : Commute x b) : Commute xi b := by
  show xi * b = b * xi
  calc xi * b = xi * b * (x * xi) := by rw [h1, mul_one]
    _ = xi * (x * b) * xi := by rw [h.eq]; simp only [mul_assoc]
    _ = b * xi := by rw [← mul_assoc, h2, one_mul]

theorem star_inv {B : Type} [Monoid B] [StarMul B] {x xi : B} (h1 : x * xi = 1)
    (h : star x = x) : star xi = xi := by
  have h2 : star xi * x = 1 := by
    have := congrArg star h1
    rwa [star_mul, h, star_one] at this
  calc star xi = star xi * (x * xi) := by rw [h1, mul_one]
    _ = (star xi * x) * xi := (mul_assoc _ _ _).symm
    _ = xi := by rw [h2, one_mul]

theorem mul_mul_one {B : Type} [Monoid B] {c ci d di : B} (h1 : c * ci = 1) (h2 : d * di = 1)
    (h : Commute d ci) : c * d * (ci * di) = 1 := by
  calc c * d * (ci * di) = c * (d * ci) * di := by simp only [mul_assoc]
    _ = c * (ci * d) * di := by rw [h.eq]
    _ = (c * ci) * (d * di) := by simp only [mul_assoc]
    _ = 1 := by rw [h1, h2, one_mul]

theorem mat1 {B : Type} [Ring B] (z zi w wi G Gi l : B) (hz : zi * z = 1) (hw : wi * w = 1)
    (hG : G * Gi = 1) :
    (!![zi, 0; 0, wi] * !![1, 0; G * l, G]) * (!![1, 0; -l, Gi] * !![z, 0; 0, w]) = 1 := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp only [mul_one, mul_zero, zero_mul, add_zero, zero_add, one_mul]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp
  · exact hz
  · noncomm_ring
  · rw [← mul_assoc, mul_assoc wi G Gi, hG, mul_one, hw]

theorem mat2 {B : Type} [Ring B] (z zi w wi G Gi l : B) (hz : z * zi = 1) (hw : w * wi = 1)
    (hG : Gi * G = 1) :
    (!![1, 0; -l, Gi] * !![z, 0; 0, w]) * (!![zi, 0; 0, wi] * !![1, 0; G * l, G]) = 1 := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp only [mul_one, mul_zero, zero_mul, add_zero, zero_add, one_mul]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp
  · exact hz
  · rw [mul_assoc l, hz, mul_one, mul_assoc Gi, ← mul_assoc w, hw, one_mul, ← mul_assoc, hG,
      one_mul, neg_add_cancel]
  · rw [mul_assoc Gi, ← mul_assoc w, hw, one_mul, hG]

theorem key_rel {B : Type} [Ring B] [Algebra ℂ B] (b b' t t' : B) (Y Y' Ya : ℂ) (hne : Y ≠ Y')
    (H1 : (Y - Y') • (t * b' - b' * t) = t * b' - t' * b)
    (H2 : (Y' - Y) • (t' * b - b * t') = t' * b - t * b') :
    (Y - Ya - 1) • (b * t') + (Y' - Ya) • (t * b') = (Y' - Ya - 1) • (b' * t) + (Y - Ya) • (t' * b) := by
  have hS : (Y - Y') • (b * t' + t * b' - b' * t - t' * b) = 0 := by
    linear_combination (norm := module) H1 + H2
  have hS0 : b * t' + t * b' - b' * t - t' * b = 0 :=
    (smul_eq_zero.mp hS).resolve_left (sub_ne_zero.mpr hne)
  linear_combination (norm := module) (Y' - Ya - 1) • hS0 + H2

theorem tri_comm {B : Type} [Ring B] [Algebra ℂ B] (b b' t t' e n : B) (D D' : ℂ)
    (hee : e * e = e) (hen : e * n = n) (hne : n * e = 0) (hnn : n * n = 0)
    (eb : e * b = b * e) (eb' : e * b' = b' * e) (et : e * t = t * e) (et' : e * t' = t' * e)
    (nb : n * b = b * n) (nb' : n * b' = b' * n) (nt : n * t = t * n) (nt' : n * t' = t' * n)
    (hbb : b * b' = b' * b)
    (K : (D - 1) • (b * t') + D' • (t * b') = (D' - 1) • (b' * t) + D • (t' * b)) :
    Commute (D • b - b * e - t * n) (D' • b' - b' * e - t' * n) := by
  have eb_x : ∀ x, e * (b * x) = b * (e * x) := fun x => by rw [← mul_assoc, eb, mul_assoc]
  have eb'_x : ∀ x, e * (b' * x) = b' * (e * x) := fun x => by rw [← mul_assoc, eb', mul_assoc]
  have et_x : ∀ x, e * (t * x) = t * (e * x) := fun x => by rw [← mul_assoc, et, mul_assoc]
  have et'_x : ∀ x, e * (t' * x) = t' * (e * x) := fun x => by rw [← mul_assoc, et', mul_assoc]
  have nb_x : ∀ x, n * (b * x) = b * (n * x) := fun x => by rw [← mul_assoc, nb, mul_assoc]
  have nb'_x : ∀ x, n * (b' * x) = b' * (n * x) := fun x => by rw [← mul_assoc, nb', mul_assoc]
  have nt_x : ∀ x, n * (t * x) = t * (n * x) := fun x => by rw [← mul_assoc, nt, mul_assoc]
  have nt'_x : ∀ x, n * (t' * x) = t' * (n * x) := fun x => by rw [← mul_assoc, nt', mul_assoc]
  have bb_x : ∀ x, b * (b' * x) = b' * (b * x) := fun x => by rw [← mul_assoc, hbb, mul_assoc]
  have Kn := congrArg (· * n) K
  simp only [add_mul, smul_mul_assoc, mul_assoc] at Kn
  show _ * _ = _ * _
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc, smul_sub, eb_x, eb'_x,
    et_x, et'_x, nb_x, nb'_x, nt_x, nt'_x, bb_x, eb, eb', nb, nb', hee, hen, hne, hnn, hbb, mul_zero,
    sub_zero]
  linear_combination (norm := module) (-1 : ℂ) • Kn

section Slots

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {a : S}

theorem io_mul (x y : A) : (io (x * y) : SlopeTestRemainingChoices S A) = io x * io y :=
  (Matrix.scalar (Ix S)).map_mul x y

theorem io_one : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 :=
  (Matrix.scalar (Ix S)).map_one

theorem io_inv {x y : A} (h : x * y = 1) : (io x : SlopeTestRemainingChoices S A) * io y = 1 := by
  rw [← io_mul, h, io_one]

theorem io_comm {x y : A} (h : x * y = y * x) : Commute (io x : SlopeTestRemainingChoices S A) (io y) := by
  show io x * io y = io y * io x
  rw [← io_mul, ← io_mul, h]

theorem free_io (a : S) (x : A) : FreeOf a (io x : SlopeTestRemainingChoices S A) := by
  intro i j
  show eU a i j * io x = io x * eU a i j
  ext p q
  simp only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, eU, Matrix.of_apply]
  split_ifs <;> simp

theorem free_one : FreeOf a (1 : SlopeTestRemainingChoices S A) :=
  fun _ _ => Commute.one_right _

theorem free_zero : FreeOf a (0 : SlopeTestRemainingChoices S A) :=
  fun _ _ => Commute.zero_right _

theorem free_mul {x y : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x * y) :=
  fun i j => (hx i j).mul_right (hy i j)

theorem free_add {x y : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x + y) :=
  fun i j => (hx i j).add_right (hy i j)

theorem free_neg {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) : FreeOf a (-x) :=
  fun i j => (hx i j).neg_right

theorem free_smul (c : ℂ) {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) : FreeOf a (c • x) :=
  fun i j => (hx i j).smul_right c

theorem free2 {p q s t : SlopeTestRemainingChoices S A} (hp : FreeOf a p) (hq : FreeOf a q) (hs : FreeOf a s) (ht : FreeOf a t) :
    FreeOf2 a !![p, q; s, t] := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa

theorem freeOf2_mul {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) (hN : FreeOf2 a N) : FreeOf2 a (M * N) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact free_add (free_mul (hM i 0) (hN 0 j)) (free_mul (hM i 1) (hN 1 j))

theorem comm2 {b p q s t : SlopeTestRemainingChoices S A} (hp : Commute b p) (hq : Commute b q) (hs : Commute b s) (ht : Commute b t) :
    ∀ i j, Commute b ((!![p, q; s, t] : M2 (SlopeTestRemainingChoices S A)) i j) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa

theorem dg_mul {p q p' q' : SlopeTestRemainingChoices S A} (hp : FreeOf a p) (hq : FreeOf a q) :
    ins a !![p, 0; 0, q] * ins a !![p', 0; 0, q'] = ins a !![p * p', 0; 0, q * q'] := by
  rw [← ins_mul a _ _ (free2 hp free_zero free_zero hq)]
  congr 1
  rw [Matrix.mul_fin_two]
  simp

theorem dg_one : ins a !![(1 : SlopeTestRemainingChoices S A), 0; 0, 1] = 1 := by
  rw [← Matrix.one_fin_two]
  exact ins_one a

theorem dg_comm {p q p' q' : SlopeTestRemainingChoices S A} (hp : FreeOf a p) (hq : FreeOf a q) (hp' : FreeOf a p')
    (hq' : FreeOf a q') (h1 : Commute p p') (h2 : Commute q q') :
    Commute (ins a !![p, 0; 0, q]) (ins a !![p', 0; 0, q']) := by
  show _ * _ = _ * _
  rw [dg_mul hp hq, dg_mul hp' hq', h1.eq, h2.eq]

theorem dg_star {p q : SlopeTestRemainingChoices S A} (hp : FreeOf a p) (hq : FreeOf a q) :
    star (ins a !![p, 0; 0, q]) = ins a !![star p, 0; 0, star q] := by
  rw [ins_star a _ (free2 hp free_zero free_zero hq)]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

theorem comm_dg {b p q : SlopeTestRemainingChoices S A} (hb : FreeOf a b) (h1 : Commute b p) (h2 : Commute b q) :
    Commute b (ins a !![p, 0; 0, q]) :=
  ins_comm a _ b hb (comm2 h1 (Commute.zero_right b) (Commute.zero_right b) h2)

theorem comm_sc {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) (φ : ℂ) :
    Commute b (ins a !![φ • (1 : SlopeTestRemainingChoices S A), 0; 0, 1]) :=
  comm_dg hb ((Commute.one_right b).smul_right φ) (Commute.one_right b)

theorem freeOf_smul_one (φ : ℂ) : FreeOf a (φ • (1 : SlopeTestRemainingChoices S A)) :=
  free_smul φ free_one

theorem mul_rh0_apply_one_zero (M : M2 (SlopeTestRemainingChoices S A)) (D : ℂ) :
    (M * Rh0 a D : M2 (SlopeTestRemainingChoices S A)) 1 0 = (D - 1)⁻¹ • (D • M 1 0 - M 1 0 * eU a 0 0 - M 1 1 * eU a 0 1) := by
  simp only [Rh0, P0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.of_apply]
  simp only [mul_smul_comm, mul_sub, smul_sub]
  simp
  module

end Slots

section Step

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem zfns_comm (L : LevelData A r) {g h : A} (hg : g ∈ zfns L) (hh : h ∈ zfns L) : g * h = h * g :=
  L.fns_comm g (Set.mem_union_right _ hg) h (Set.mem_union_right _ hh)

theorem plusStep_of (hLP : LetterPlus) (hRTT : RTTEntries) (hForm : PlusForm) (hTau : PlusTau) (hPL : PlusL)
    (L : LevelData A r) (f : FrameData S A) (a : S) (Ya : ℂ) (h : PlusHyp L f a Ya) :
    IsFrame L (f.plus L a Ya) := by
  have hH := h
  obtain ⟨hstar, hf, hfree, hYa, hYaI, hYa1I, hq⟩ := h
  obtain ⟨fRR, fTT, fF, fFi, fx, fxi, fc, fci, fee⟩ := hfree
  have xiYa := hf.x_xi Ya hYaI
  have xiYa1 := hf.x_xi (Ya + 1) hYa1I
  have hYaR : Ya ∈ f.reg := hf.inv_reg hYaI
  have xi_c : ∀ Y ∈ f.inv, Commute (f.xi Y) f.c := fun Y hY =>
    comm_inv (hf.x_xi Y hY).1 (hf.x_xi Y hY).2 (hf.x_c Y)
  have x_ci : ∀ Y, Commute (f.x Y) f.ci := fun Y =>
    (comm_inv hf.c_ci.1 hf.c_ci.2 (hf.x_c Y).symm).symm
  have xi_ci : ∀ Y ∈ f.inv, Commute (f.xi Y) f.ci := fun Y hY =>
    (comm_inv hf.c_ci.1 hf.c_ci.2 (xi_c Y hY).symm).symm
  have xi_x : ∀ Y ∈ f.inv, ∀ Y', Commute (f.xi Y) (f.x Y') := fun Y hY Y' =>
    comm_inv (hf.x_xi Y hY).1 (hf.x_xi Y hY).2 (hf.x_commute Y Y')
  have xi_fn : ∀ Y ∈ f.inv, ∀ g ∈ zfns L, Commute (f.xi Y) (io g) := fun Y hY g hg =>
    comm_inv (hf.x_xi Y hY).1 (hf.x_xi Y hY).2 (hf.x_fn Y g hg)
  have hl : FreeOf a (f.l L Ya) := by
    simp only [FrameData.l, kapL]
    exact free_add (free_io a _) (free_mul (free_io a _) (fee Ya))
  have hs : ∀ (u v : SlopeTestRemainingChoices S A) (c d : ℂ), (c • u) * (d • v) = (c * d) • (u * v) := fun u v c d => by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hD12 : ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya] *
      ins a !![(f.q Ya)⁻¹ • f.x (Ya + 1), 0; 0, f.xi Ya] = 1 := by
    rw [dg_mul (free_smul _ (fxi _)) (fx _), hs, mul_inv_cancel₀ hq, one_smul, xiYa1.2, xiYa.1,
      dg_one]
  have hD21 : ins a !![(f.q Ya)⁻¹ • f.x (Ya + 1), 0; 0, f.xi Ya] *
      ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya] = 1 := by
    rw [dg_mul (free_smul _ (fx _)) (fxi _), hs, inv_mul_cancel₀ hq, one_smul, xiYa1.1, xiYa.2,
      dg_one]
  have diagonalShiftOneMinus : Commute f.c (ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya]) :=
    comm_dg fc ((xi_c (Ya + 1) hYa1I).symm.smul_right _) (hf.x_c Ya).symm
  have ciD1 : Commute f.ci (ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya]) :=
    comm_dg fci ((xi_ci (Ya + 1) hYa1I).symm.smul_right _) (x_ci Ya).symm
  have cD2 : Commute f.c (ins a !![(f.q Ya)⁻¹ • f.x (Ya + 1), 0; 0, f.xi Ya]) :=
    comm_dg fc ((hf.x_c (Ya + 1)).symm.smul_right _) (xi_c Ya hYaI).symm
  have assoc4 : ∀ u v w x : SlopeTestRemainingChoices S A, u * v * (w * x) = u * (v * w) * x := fun _ _ _ _ => by
    simp only [mul_assoc]
  refine
    { module := hLP ℂ A S f.reg f.RR f.TT f.q a Ya hf.module fRR fTT hYaR hYa
      lowerLeftEntry_commute := ?_
      inv_reg := fun Y hY => ⟨hf.inv_reg hY.1, hY.2.2⟩
      F_Fi := ?_
      Fi_F := ?_
      x_xi := ?_
      c_ci := ⟨mul_mul_one hf.c_ci.1 hD12 ciD1.symm, mul_mul_one hf.c_ci.2 hD21 cD2.symm⟩
      x_commute := ?_
      x_c := ?_
      x_fn := ?_
      x_nab := ?_
      c_fn := ?_
      x_star := ?_
      c_star := ?_
      ee_fn := ?_
      form := hForm A S r L f a Ya hH
      frame_τ := hTau A S r L f a Ya hH
      frame_l := hPL A S r L f a Ya hH }
  · intro Y hY Y' hY'
    show Commute ((f.TT Y * Rh0 a (Y - Ya) : M2 (SlopeTestRemainingChoices S A)) 1 0)
      ((f.TT Y' * Rh0 a (Y' - Ya) : M2 (SlopeTestRemainingChoices S A)) 1 0)
    rw [mul_rh0_apply_one_zero, mul_rh0_apply_one_zero]
    by_cases hYY : Y = Y'
    · subst hYY
      exact Commute.refl _
    have hee : (eU a 0 0 : SlopeTestRemainingChoices S A) * eU a 0 0 = eU a 0 0 := by rw [eU_mul_eU]; simp
    have hen : (eU a 0 0 : SlopeTestRemainingChoices S A) * eU a 0 1 = eU a 0 1 := by rw [eU_mul_eU]; simp
    have hne : (eU a 0 1 : SlopeTestRemainingChoices S A) * eU a 0 0 = 0 := by rw [eU_mul_eU]; simp
    have hnn : (eU a 0 1 : SlopeTestRemainingChoices S A) * eU a 0 1 = 0 := by rw [eU_mul_eU]; simp
    have K := key_rel _ _ _ _ Y Y' Ya hYY
      (hRTT ℂ (SlopeTestRemainingChoices S A) f.TT Y' Y (hf.module.rtt Y' hY'.1 Y hY.1) 1 1 1 0)
      (hRTT ℂ (SlopeTestRemainingChoices S A) f.TT Y Y' (hf.module.rtt Y hY.1 Y' hY'.1) 1 1 1 0)
    exact ((tri_comm _ _ _ _ (eU a 0 0) (eU a 0 1) (Y - Ya) (Y' - Ya) hee hen hne hnn
      (fTT Y 1 0 0 0).eq (fTT Y' 1 0 0 0).eq (fTT Y 1 1 0 0).eq (fTT Y' 1 1 0 0).eq
      (fTT Y 1 0 0 1).eq (fTT Y' 1 0 0 1).eq (fTT Y 1 1 0 1).eq (fTT Y' 1 1 0 1).eq
      (hf.lowerLeftEntry_commute Y hY.1 Y' hY'.1).eq K).smul_left _).smul_right _
  · have hM : FreeOf2 a (!![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * f.l L Ya, io L.GG] :
        M2 (SlopeTestRemainingChoices S A)) :=
      freeOf2_mul (free2 (free_io a _) free_zero free_zero (free_io a _))
        (free2 free_one free_zero (free_mul (free_io a _) hl) (free_io a _))
    show ins a _ * f.F * (f.Fi * ins a _) = 1
    rw [assoc4, hf.F_Fi, mul_one, ← ins_mul a _ _ hM,
      mat1 (io L.ζ) (io L.ζi) (io L.ζb) (io L.ζbi) (io L.GG) (io L.GGi) (f.l L Ya)
        (io_inv L.ζi_ζ) (io_inv L.ζbi_ζb) (io_inv L.GG_GGi), ins_one]
  · have hN : FreeOf2 a (!![1, 0; -f.l L Ya, io L.GGi] * !![io L.ζ, 0; 0, io L.ζb] :
        M2 (SlopeTestRemainingChoices S A)) :=
      freeOf2_mul (free2 free_one free_zero (free_neg hl) (free_io a _))
        (free2 (free_io a _) free_zero free_zero (free_io a _))
    show f.Fi * ins a _ * (ins a _ * f.F) = 1
    rw [assoc4, ← ins_mul a _ _ hN,
      mat2 (io L.ζ) (io L.ζi) (io L.ζb) (io L.ζbi) (io L.GG) (io L.GGi) (f.l L Ya)
        (io_inv L.ζ_ζi) (io_inv L.ζb_ζbi) (io_inv L.GGi_GG), ins_one, mul_one, hf.Fi_F]
  · intro Y hY
    obtain ⟨hYI, hY0, hY1⟩ := hY
    have hY1' : Y - Ya - 1 ≠ 0 := sub_ne_zero.mpr hY1
    have hab : ((Y - Ya) / (Y - Ya - 1)) * ((Y - Ya - 1) / (Y - Ya)) = 1 := by
      field_simp
    have hba : ((Y - Ya - 1) / (Y - Ya)) * ((Y - Ya) / (Y - Ya - 1)) = 1 := by
      rw [mul_comm]; exact hab
    have d1 : ins a !![((Y - Ya) / (Y - Ya - 1)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] *
        ins a !![((Y - Ya - 1) / (Y - Ya)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] = 1 := by
      rw [dg_mul (freeOf_smul_one _) free_one, hs, hab, one_smul, one_mul, dg_one]
    have d2 : ins a !![((Y - Ya - 1) / (Y - Ya)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] *
        ins a !![((Y - Ya) / (Y - Ya - 1)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1] = 1 := by
      rw [dg_mul (freeOf_smul_one _) free_one, hs, hba, one_smul, one_mul, dg_one]
    exact ⟨mul_mul_one (hf.x_xi Y hYI).1 d1 (comm_sc (fxi Y) _).symm,
      mul_mul_one (hf.x_xi Y hYI).2 d2 (comm_sc (fx Y) _).symm⟩
  · intro Y Y'
    exact ((hf.x_commute Y Y').mul_right (comm_sc (fx Y) _)).mul_left
      ((comm_sc (fx Y') _).symm.mul_right (dg_comm (freeOf_smul_one _) free_one (freeOf_smul_one _) free_one
        (((Commute.refl (1 : SlopeTestRemainingChoices S A)).smul_left _).smul_right _) (Commute.refl 1)))
  · intro Y
    exact ((hf.x_c Y).mul_right (comm_dg (fx Y) ((xi_x (Ya + 1) hYa1I Y).symm.smul_right _)
        (hf.x_commute Y Ya))).mul_left
      ((comm_sc fc _).symm.mul_right (dg_comm (freeOf_smul_one _) free_one (free_smul _ (fxi _)) (fx _)
        ((Commute.one_left _).smul_left _) (Commute.one_left _)))
  · intro Y g hg
    exact (hf.x_fn Y g hg).mul_left (comm_sc (free_io a g) _).symm
  · intro Y
    exact (hf.x_nab Y).mul_left (comm_sc (free_io a _) _).symm
  · intro g hg
    exact (hf.c_fn g hg).mul_left (comm_dg (free_io a g)
      ((xi_fn (Ya + 1) hYa1I g hg).symm.smul_right _) (hf.x_fn Ya g hg).symm).symm
  · intro Y hY
    have hα : star ((Y - Ya) / (Y - Ya - 1)) = (Y - Ya) / (Y - Ya - 1) := by
      simp [hY, hYa]
    show star (f.x Y * ins a !![((Y - Ya) / (Y - Ya - 1)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1]) =
      f.x Y * ins a !![((Y - Ya) / (Y - Ya - 1)) • (1 : SlopeTestRemainingChoices S A), 0; 0, 1]
    rw [star_mul, dg_star (freeOf_smul_one _) free_one, star_smul, star_one, hα, hf.x_star Y hY]
    exact (comm_sc (fx Y) _).eq.symm
  · have hqR : star (f.q Ya) = f.q Ya := hf.module.q_real Ya hYa
    have hxi1 : star (f.xi (Ya + 1)) = f.xi (Ya + 1) :=
      star_inv xiYa1.1 (hf.x_star (Ya + 1) (by simp [hYa]))
    show star (f.c * ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya]) =
      f.c * ins a !![f.q Ya • f.xi (Ya + 1), 0; 0, f.x Ya]
    rw [star_mul, dg_star (free_smul _ (fxi _)) (fx _), star_smul, hqR, hxi1, hf.x_star Ya hYa,
      hf.c_star]
    exact diagonalShiftOneMinus.eq.symm
  · intro Y g hg
    have hz : L.ζbi ∈ zfns L := by simp [zfns]
    have htz : Commute (io g : SlopeTestRemainingChoices S A) (tz L) := by
      unfold tz
      exact io_comm (by rw [mul_smul_comm, smul_mul_assoc, zfns_comm L hg hz])
    have hDD : Commute (io g : SlopeTestRemainingChoices S A) (f.DD Y Ya) := by
      unfold FrameData.DD
      exact ((hf.ee_fn Y g hg).symm.sub_right (hf.ee_fn Ya g hg).symm).smul_right _
    exact (ins_comm a _ (io g) (free_io a g)
      (comm2 (((hf.ee_fn Y g hg).symm.sub_right hDD).add_right htz)
        ((Commute.one_right _).smul_right _).neg_right (Commute.zero_right _)
        (((xi_fn Ya hYaI g hg).symm.mul_right (hf.ee_fn Y g hg).symm).mul_right
          (hf.x_fn Ya g hg).symm))).symm

end Step

end Formalism.FourierDecayAlt.P.Fr7

namespace Formalism.FourierDecayAlt.P

theorem plus_letter_frame_of_data : Formalism.FourierDecayAlt.Fr.PlusAssemble := by
  unfold Formalism.FourierDecayAlt.Fr.PlusAssemble Formalism.FourierDecayAlt.Fr.PlusStep
  intro _ _ _ _ hLP hRTT hForm hTau hPL A S _ _ _ _ _ _ r L f a Ya h
  exact Formalism.FourierDecayAlt.P.Fr7.plusStep_of hLP hRTT hForm hTau hPL L f a Ya h

end Formalism.FourierDecayAlt.P
