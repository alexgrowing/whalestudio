import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferMatrixFactorization
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuasiDeterminantFromEntries

open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

namespace Formalism.FourierDecayAlt.P.Fr6

set_option linter.unusedSimpArgs false

local macro "noncomm_match_scalars" : tactic => `(tactic|
  ((try simp only [mul_assoc, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc,
      mul_smul_comm, neg_mul, mul_neg, mul_one, one_mul, smul_add, smul_sub, smul_neg, smul_smul, mul_zero, zero_mul,
      add_zero, zero_add, smul_zero, sub_zero, zero_sub, neg_neg, neg_zero, Algebra.algebraMap_eq_smul_one]);
   (match_scalars <;> first | ring1 | (field_simp; ring1) | field_simp)))

section Gen
variable {B : Type} [Ring B] [Algebra ℂ B]

theorem matrix2_congr {a b c d a' b' c' d' : B} (h1 : a = a') (h2 : b = b') (h3 : c = c') (h4 : d = d') :
    !![a, b; c, d] = !![a', b'; c', d'] := by subst h1 h2 h3 h4; rfl

theorem core1 (D : ℂ) (F τY τa sY sa T Ta Tai la : B)
    (h1 : F * τY = T * F) (h2 : F * τa = Ta * F) (h3 : F * sa = Ta * la * F)
    (hc : T * Ta = Ta * T) (hi : Tai * Ta = 1)
    (rtt : D • (τY * sa - sa * τY) = τY * sa - τa * sY) :
    D • (T * la * F - la * T * F) = T * la * F - F * sY := by
  have a1 : F * (τY * sa) = Ta * (T * la * F) := by
    rw [← mul_assoc, h1, mul_assoc, h3]; simp only [← mul_assoc]; rw [hc]
  have a2 : F * (sa * τY) = Ta * (la * T * F) := by
    rw [← mul_assoc, h3, mul_assoc, h1]; simp only [mul_assoc]
  have a3 : F * (τa * sY) = Ta * (F * sY) := by rw [← mul_assoc, h2, mul_assoc]
  have e : Ta * (D • (T * la * F - la * T * F)) = Ta * (T * la * F - F * sY) := by
    rw [mul_smul_comm, mul_sub, mul_sub, ← a1, ← a2, ← a3, ← mul_sub, ← mul_sub, ← mul_smul_comm, rtt]
  have := congrArg (Tai * ·) e
  simpa only [← mul_assoc, hi, one_mul] using this

theorem tau_mat (D : ℂ) (hD1 : D - 1 ≠ 0) (zi zbi G la F τ s T : B)
    (hτ : F * τ = T * F) (hTzi : T * zi = zi * T) (hTw : T * (zbi * G) = zbi * G * T)
    (hcore : D • (T * la * F - la * T * F) = T * la * F - F * s) :
    (!![zi, 0; 0, zbi] * !![1, 0; G * la, G]) *
        (!![F, 0; 0, F] * ((D - 1)⁻¹ • !![D • τ, 0; -s, (D - 1) • τ])) =
      !![T, 0; 0, T] * (!![(D / (D - 1)) • 1, 0; 0, 1] *
        ((!![zi, 0; 0, zbi] * !![1, 0; G * la, G]) * !![F, 0; 0, F])) := by
  simp only [Matrix.mul_fin_two, Matrix.smul_of, Matrix.smul_cons, Matrix.smul_empty]
  refine matrix2_congr ?_ ?_ ?_ ?_
  · linear_combination (norm := noncomm_match_scalars) ((D - 1)⁻¹ * D) • (zi * hτ) - ((D - 1)⁻¹ * D) • (hTzi * F)
  · simp
  · linear_combination (norm := noncomm_match_scalars) ((D - 1)⁻¹ * D) • (zbi * G * la * hτ) - (hTw * la * F) - (D - 1)⁻¹ • (zbi * G * hcore)
  · linear_combination (norm := noncomm_match_scalars) (zbi * G * hτ) - (hTw * F)

end Gen

section Gen2
variable {B : Type} [Ring B] [Algebra ℂ B]

theorem smul_cancel {D : ℂ} (hD : D ≠ 0) {u v : B} (h : D • u = D • v) : u = v := by
  have := congrArg (D⁻¹ • ·) h
  simpa [smul_smul, inv_mul_cancel₀ hD] using this

theorem lcancel {u ui p q : B} (h : ui * u = 1) (e : u * p = u * q) : p = q := by
  have := congrArg (ui * ·) e
  simpa only [← mul_assoc, h, one_mul] using this

theorem core2 (D : ℂ) (F Fi T la l : B) (hF : F * Fi = 1)
    (h : D • (T * la * F - la * T * F) = T * la * F - T * l * F) :
    D • (T * la - la * T) = T * la - T * l := by
  have := congrArg (· * Fi) h
  simp only [sub_mul, smul_mul_assoc, mul_assoc, hF, mul_one] at this
  simpa only [mul_assoc] using this

theorem rel1 {D : ℂ} (hD : D ≠ 0) (T m m' η : B) (hm : m' = m + D • η)
    (r1 : D • (T * m - m * T) = T * m - T * m') : m * T = T * (m + η) := by
  subst hm
  apply smul_cancel hD
  linear_combination (norm := noncomm_match_scalars) -r1

theorem rel3 (T Ti Ta Tai l la η : B) (c1 : la * T = T * (la + η)) (c2 : l * Ta = Ta * (l + η))
    (r3 : T * l * (Ta * la) = Ta * la * (T * l)) (hc : T * Ta = Ta * T) (hTi : Ti * T = 1) (hTai : Tai * Ta = 1) :
    (l + η) * la = (la + η) * l := by
  have e : T * Ta * ((l + η) * la) = T * Ta * ((la + η) * l) := by
    linear_combination (norm := noncomm_match_scalars) r3 - T * c2 * la + Ta * c1 * l - hc * ((la + η) * l)
  rw [mul_assoc, mul_assoc] at e
  exact lcancel hTai (lcancel hTi e)

theorem conj_abs (G Gi xa xai κ κi l0 β e dd : B)
    (c2 : (l0 + κ * e) * (G * xa) = G * xa * ((l0 + κ * e) + (-β + κ * dd)))
    (hlG : l0 * G = G * (l0 - β)) (hκG : κ * G = G * κ) (heG : e * G = G * e) (hGi : Gi * G = 1)
    (hlx : l0 * xa = xa * l0) (hβx : β * xa = xa * β) (hκx : κ * xa = xa * κ) (hκi : κi * κ = 1)
    (hxi : xai * xa = 1) : xai * e * xa = e + dd := by
  have e1 : G * (κ * (e * xa)) = G * (κ * (xa * (e + dd))) := by
    linear_combination (norm := noncomm_match_scalars) c2 - hlG * xa - κ * heG * xa - hκG * e * xa - G * hlx + G * hβx
      - G * hκx * (e + dd)
  have e2 := lcancel hκi (lcancel hGi e1)
  rw [mul_assoc, e2, ← mul_assoc, hxi, one_mul]

end Gen2

section Gen3
variable {B : Type} [Ring B] [Algebra ℂ B]

theorem entA (D : ℂ) (hD : D ≠ 0) (hD1 : D - 1 ≠ 0) (zi w β κ lam l0 ea e dd t la l : B)
    (hl0 : l0 = lam - D • β) (he : e = ea + D • dd) (hla : la = lam + κ * ea) (hl : l = l0 + κ * e)
    (hlzi : lam * zi = zi * lam + zi * zi) (hβzi : β * zi = zi * β) (hκzi : κ * zi = zi * κ)
    (heazi : ea * zi = zi * ea) (hddzi : dd * zi = zi * dd) (htzi : t * zi = zi * t)
    (hκw : κ * w = zi) (hz : zi + κ * t = β) :
    (D / (D - 1)) • ((l0 + κ * (e - dd + t)) * zi + κ * (-(D⁻¹ • 1)) * (w * la)) = zi * l := by
  subst hl hla he hl0
  linear_combination (norm := noncomm_match_scalars) (D / (D - 1)) • (hlzi - D • hβzi + κ * heazi + hκzi * ea
    + (D - 1) • (κ * hddzi + hκzi * dd) + κ * htzi + hκzi * t - D⁻¹ • (hκw * lam + hκw * κ * ea) + zi * hz)

theorem entE (D : ℂ) (w β κ lam l0 ea e dd xa xai l η : B)
    (hl0 : l0 = lam - D • β) (he : e = ea + D • dd) (hl : l = l0 + κ * e) (hη : η = -β + κ * dd)
    (hconj : xai * e * xa = e + dd)
    (hlw : lam * w = w * (lam - β)) (hβw : β * w = w * β)
    (hκw' : κ * w = w * κ) (heaw : ea * w = w * ea) (hddw : dd * w = w * dd) :
    (l0 + κ * (xai * e * xa)) * w = w * (l + η) := by
  rw [hconj]
  subst hl hη he hl0
  linear_combination (norm := noncomm_match_scalars) hlw - D • hβw + κ * heaw + hκw' * ea + (D + 1) • (κ * hddw + hκw' * dd)

theorem entC (D : ℂ) (hD1 : D - 1 ≠ 0) (w la l η T liftZP_unit : B) (hlη : l = la + D • η)
    (c1 : la * T = T * (la + η)) (hTw : T * w = w * T) (hE : liftZP_unit * w = w * (l + η)) :
    (D - 1)⁻¹ • (-(w * la * T) + D • (w * T * l)) = T * (liftZP_unit * w) := by
  subst hlη
  linear_combination (norm := noncomm_match_scalars) -(D - 1)⁻¹ • (w * c1) - T * hE - hTw * (la + D • η + η)

theorem entD (w la l η T liftZP_unit : B)
    (c1 : la * T = T * (la + η)) (c3 : (l + η) * la = (la + η) * l) (hTw : T * w = w * T)
    (hE : liftZP_unit * w = w * (l + η)) :
    w * la * T * l = T * (liftZP_unit * (w * la)) := by
  linear_combination (norm := noncomm_match_scalars) w * c1 * l - T * hE * la - hTw * (l + η) * la - w * T * c3

theorem L_mat (D : ℂ) (hD : D ≠ 0) (hD1 : D - 1 ≠ 0)
    (zi zbi G β κ lam l0 ea e dd t xa xai la l η F τ s T : B)
    (hl0 : l0 = lam - D • β) (he : e = ea + D • dd) (hla : la = lam + κ * ea) (hl : l = l0 + κ * e)
    (hη : η = -β + κ * dd)
    (hτ : F * τ = T * F) (hs : F * s = T * l * F)
    (hTzi : T * zi = zi * T) (hTw : T * (zbi * G) = zbi * G * T)
    (c1 : la * T = T * (la + η)) (c3 : (l + η) * la = (la + η) * l) (hconj : xai * e * xa = e + dd)
    (hlzi : lam * zi = zi * lam + zi * zi) (hβzi : β * zi = zi * β) (hκzi : κ * zi = zi * κ)
    (heazi : ea * zi = zi * ea) (hddzi : dd * zi = zi * dd) (htzi : t * zi = zi * t)
    (hκw : κ * (zbi * G) = zi) (hz : zi + κ * t = β)
    (hlw : lam * (zbi * G) = zbi * G * (lam - β)) (hβw : β * (zbi * G) = zbi * G * β)
    (hκw' : κ * (zbi * G) = zbi * G * κ) (heaw : ea * (zbi * G) = zbi * G * ea)
    (hddw : dd * (zbi * G) = zbi * G * dd) :
    (!![zi, 0; 0, zbi] * !![1, 0; G * la, G]) *
        (!![F, 0; 0, F] * ((D - 1)⁻¹ • !![(D - 1) • s, -τ; 0, D • s])) =
      !![T, 0; 0, T] * (!![(D / (D - 1)) • 1, 0; 0, 1] *
        (!![l0 + κ * (e - dd + t), κ * (-(D⁻¹ • 1)); 0, l0 + κ * (xai * e * xa)] *
        ((!![zi, 0; 0, zbi] * !![1, 0; G * la, G]) * !![F, 0; 0, F]))) := by
  have hlη : l = la + D • η := by
    subst hl hla hη he hl0
    noncomm_match_scalars
  have hA := entA D hD hD1 zi (zbi * G) β κ lam l0 ea e dd t la l hl0 he hla hl hlzi hβzi hκzi heazi hddzi htzi hκw hz
  have hE := entE D (zbi * G) β κ lam l0 ea e dd xa xai l η hl0 he hl hη hconj hlw hβw hκw' heaw hddw
  have hC := entC D hD1 (zbi * G) la l η T _ hlη c1 hTw hE
  have hDD := entD (zbi * G) la l η T _ c1 c3 hTw hE
  simp only [Matrix.mul_fin_two, Matrix.smul_of, Matrix.smul_cons, Matrix.smul_empty]
  refine matrix2_congr ?_ ?_ ?_ ?_
  · linear_combination (norm := noncomm_match_scalars) zi * hs - T * hA * F - hTzi * l * F
  · linear_combination (norm := noncomm_match_scalars) -(D - 1)⁻¹ • (zi * hτ) + (D - 1)⁻¹ • (T * hκw * F) + (D - 1)⁻¹ • (hTzi * F)
  · linear_combination (norm := noncomm_match_scalars) zbi * G * la * hs + hDD * F
  · linear_combination (norm := noncomm_match_scalars) -(D - 1)⁻¹ • (zbi * G * la * hτ) + ((D - 1)⁻¹ * D) • (zbi * G * hs) + hC * F

end Gen3

section Gen4
variable {B : Type} [Ring B] [Algebra ℂ B]

theorem commute_of_conj_alt (F Fi s sa U Ua : B) (hF : F * Fi = 1) (hs : F * s = U * F) (hsa : F * sa = Ua * F)
    (hc : s * sa = sa * s) : U * Ua = Ua * U := by
  linear_combination (norm := noncomm_match_scalars) F * hc * Fi - hs * sa * Fi - U * hsa * Fi - U * Ua * hF + hsa * s * Fi
    + Ua * hs * Fi + Ua * U * hF

end Gen4

section Slot
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

theorem d0_eq (b : SlopeTestRemainingChoices S A) : d0 b = !![b, 0; 0, b] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [d0]

theorem fr_mul {a : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x * y) :=
  fun i j => (hx i j).mul_right (hy i j)
theorem fr_add {a : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x + y) :=
  fun i j => (hx i j).add_right (hy i j)
theorem fr_sub {a : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) : FreeOf a (x - y) :=
  fun i j => (hx i j).sub_right (hy i j)
theorem fr_neg {a : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) : FreeOf a (-x) :=
  fun i j => (hx i j).neg_right
theorem fr_smul {a : S} {x : SlopeTestRemainingChoices S A} (c : ℂ) (hx : FreeOf a x) : FreeOf a (c • x) :=
  fun i j => (hx i j).smul_right c
theorem fr_one (a : S) : FreeOf a (1 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.one_right _
theorem fr_zero (a : S) : FreeOf a (0 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.zero_right _
theorem fr_io (a : S) (x : A) : FreeOf a (io x : SlopeTestRemainingChoices S A) := Wd5.free_io a x

theorem fr2 {a : S} {p q r s : SlopeTestRemainingChoices S A} (hp : FreeOf a p) (hq : FreeOf a q) (hr : FreeOf a r)
    (hs : FreeOf a s) : FreeOf2 a !![p, q; r, s] := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa

theorem freeOf2_mul_of_free {a : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) (hN : FreeOf2 a N) : FreeOf2 a (M * N) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact fr_add (fr_mul (hM _ _) (hN _ _)) (fr_mul (hM _ _) (hN _ _))

theorem ins_add (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) : ins a (M + N) = ins a M + ins a N := by
  simp [ins, mul_add, Finset.sum_add_distrib]

theorem ins_smul (a : S) (c : ℂ) (M : M2 (SlopeTestRemainingChoices S A)) : ins a (c • M) = c • ins a M := by
  simp [ins, Finset.smul_sum]

theorem ins_dd (a : S) (b : SlopeTestRemainingChoices S A) : ins a !![b, 0; 0, b] = b := by
  rw [← d0_eq]; exact Wd1.insert_diagonal_extract a b

theorem tau_after_rmatrix (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 a M) (D : ℂ) :
    (M * Rh0 a D : M2 (SlopeTestRemainingChoices S A)) 1 1 = ins a ((D - 1)⁻¹ • !![D • M 1 1, 0; -M 1 0, (D - 1) • M 1 1]) := by
  have h1 := Wd1.sum_eU_diag (A := A) a
  rw [Fin.sum_univ_two] at h1
  have c0 := (hM 1 0 1 0).eq
  have c1 := (hM 1 1 1 1).eq
  rw [ins_smul]
  simp only [Rh0, Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_sub, Matrix.sub_apply, Matrix.mul_apply,
    Fin.sum_univ_two, P0, Matrix.of_apply, ins, Matrix.one_apply]
  simp
  linear_combination (norm := noncomm_match_scalars) (D - 1)⁻¹ • (c0 + c1 - D • (h1 * M 1 1))

theorem t21_after_rmatrix (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 a M) (D : ℂ) :
    (M * Rh0 a D : M2 (SlopeTestRemainingChoices S A)) 1 0 = ins a ((D - 1)⁻¹ • !![(D - 1) • M 1 0, -M 1 1; 0, D • M 1 0]) := by
  have h1 := Wd1.sum_eU_diag (A := A) a
  rw [Fin.sum_univ_two] at h1
  have c0 := (hM 1 0 0 0).eq
  have c1 := (hM 1 1 0 1).eq
  rw [ins_smul]
  simp only [Rh0, Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_sub, Matrix.sub_apply, Matrix.mul_apply,
    Fin.sum_univ_two, P0, Matrix.of_apply, ins, Matrix.one_apply]
  simp
  linear_combination (norm := noncomm_match_scalars) (D - 1)⁻¹ • (c0 + c1 - D • (h1 * M 1 0))

end Slot

section Position2
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

theorem ins_affine (a : S) (p κ errorNonneg bivariateExponentMonomial E11 : SlopeTestRemainingChoices S A) (hκ : FreeOf a κ) :
    p + κ * ins a !![errorNonneg, bivariateExponentMonomial; 0, E11] = ins a !![p + κ * errorNonneg, κ * bivariateExponentMonomial; 0, p + κ * E11] := by
  have h1 := Wd1.sum_eU_diag (A := A) a
  rw [Fin.sum_univ_two] at h1
  have c00 := (hκ 0 0).eq
  have c01 := (hκ 0 1).eq
  have c11 := (hκ 1 1).eq
  simp only [ins, Fin.sum_univ_two]
  simp
  linear_combination (norm := noncomm_match_scalars) -(h1 * p) - c00 * errorNonneg - c01 * bivariateExponentMonomial - c11 * E11

end Position2

section Level
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

theorem zeta_GG_mul_inv : L.ζb * L.GGi * (L.ζbi * L.GG) = 1 := by
  have h := L.fns_comm L.GGi (by simp) L.ζbi (by simp)
  linear_combination (norm := noncomm_match_scalars) L.ζb * h * L.GG + L.ζb_ζbi * L.GGi * L.GG + L.GGi_GG

theorem GG_zeta_mul_inv : L.ζbi * L.GG * (L.ζb * L.GGi) = 1 := by
  have h := L.fns_comm L.GG (by simp) L.ζb (by simp)
  linear_combination (norm := noncomm_match_scalars) L.ζbi * h * L.GGi + L.ζbi_ζb * L.GG * L.GGi + L.GG_GGi

theorem a_κw : L.ζb * L.ζi * L.GGi * (L.ζbi * L.GG) = L.ζi := by
  have h1 := L.fns_comm L.GGi (by simp) L.ζbi (by simp)
  have h2 := L.fns_comm L.ζi (by simp) L.ζbi (by simp)
  linear_combination (norm := noncomm_match_scalars) L.ζb * L.ζi * h1 * L.GG + L.ζb * L.ζi * L.ζbi * L.GGi_GG + L.ζb * h2
    + L.ζb_ζbi * L.ζi

theorem a_κi : L.ζ * L.ζbi * L.GG * (L.ζb * L.ζi * L.GGi) = 1 := by
  have h1 := L.fns_comm L.GG (by simp) L.ζb (by simp)
  have h2 := L.fns_comm L.GG (by simp) L.ζi (by simp)
  linear_combination (norm := noncomm_match_scalars) L.ζ * L.ζbi * h1 * L.ζi * L.GGi + L.ζ * L.ζbi_ζb * L.GG * L.ζi * L.GGi
    + L.ζ * h2 * L.GGi + L.ζ_ζi * L.GG * L.GGi + L.GG_GGi

theorem zeta_GG_identity : L.ζi + L.ζb * L.ζi * L.GGi * (L.TT • L.ζbi) = L.ζb * L.GGi := by
  have h1 := L.fns_comm L.GGi (by simp) L.ζbi (by simp)
  have h2 := L.fns_comm L.ζi (by simp) L.ζbi (by simp)
  linear_combination (norm := noncomm_match_scalars) L.TT • (L.ζb * L.ζi * h1 + L.ζb * h2 * L.GGi + L.ζb_ζbi * L.ζi * L.GGi)
    - L.ζi * L.GG_GGi + L.ζi * L.GG_def * L.GGi + L.ζi_ζ * L.ζb * L.GGi

theorem a_l0zi (Y : ℂ) : L.l0 Y * L.ζi = L.ζi * L.l0 Y + L.ζi * L.ζi := by
  have h1 := L.fns_comm L.GGi (by simp) L.ζi (by simp)
  have h2 := L.fns_comm L.ζb (by simp) L.ζi (by simp)
  unfold LevelData.l0
  linear_combination (norm := noncomm_match_scalars) -L.nab_ζi - (Y + 1 / 2) • (L.ζb * h1 + h2 * L.GGi)

theorem l0_conj_zeta_GG (Y : ℂ) : L.l0 Y * (L.ζbi * L.GG) = L.ζbi * L.GG * (L.l0 Y - L.ζb * L.GGi) := by
  have u1 := zeta_GG_mul_inv L
  have u2 := GG_zeta_mul_inv L
  unfold LevelData.l0
  linear_combination (norm := noncomm_match_scalars) -L.nab_ζbi * L.GG - L.ζbi * L.nab_GG - (Y + 1 / 2) • (u1 - u2) + u2 - L.ζbi_ζb

theorem a_l0G (Y : ℂ) : L.l0 Y * L.GG = L.GG * (L.l0 Y - L.ζb * L.GGi) := by
  have h := L.fns_comm L.GG (by simp) L.ζb (by simp)
  have u3 : L.GG * L.ζb * L.GGi = L.ζb := by
    linear_combination (norm := noncomm_match_scalars) h * L.GGi + L.ζb * L.GG_GGi
  have u4 : L.ζb * L.GGi * L.GG = L.ζb := by
    linear_combination (norm := noncomm_match_scalars) L.ζb * L.GGi_GG
  unfold LevelData.l0
  linear_combination (norm := noncomm_match_scalars) -L.nab_GG - (Y + 1 / 2) • (u4 - u3) + u3

theorem l0_linear_in_Y (Y Ya : ℂ) : L.l0 Y = L.l0 Ya - (Y - Ya) • (L.ζb * L.GGi) := by
  unfold LevelData.l0
  noncomm_match_scalars

end Level

section Main
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem io_mul (x y : A) : (io (x * y) : SlopeTestRemainingChoices S A) = io x * io y := by simp [io]

theorem fn_comm (L : LevelData A r) {g h : A} (hg : g ∈ zfns L) (hh : h ∈ zfns L) :
    (io g : SlopeTestRemainingChoices S A) * io h = io h * io g := by
  rw [← io_mul, ← io_mul, L.fns_comm g (Or.inr hg) h (Or.inr hh)]

theorem mζ (L : LevelData A r) : L.ζ ∈ zfns L := by simp [zfns]
theorem mζi (L : LevelData A r) : L.ζi ∈ zfns L := by simp [zfns]
theorem mζb (L : LevelData A r) : L.ζb ∈ zfns L := by simp [zfns]
theorem mζbi (L : LevelData A r) : L.ζbi ∈ zfns L := by simp [zfns]
theorem mG (L : LevelData A r) : L.GG ∈ zfns L := by simp [zfns]
theorem mGi (L : LevelData A r) : L.GGi ∈ zfns L := by simp [zfns]

theorem T_fn {L : LevelData A r} {f : FrameData S A} (hf : IsFrame L f) (Y : ℂ) {g : A} (hg : g ∈ zfns L) :
    io L.GG * f.x Y * io g = io g * (io L.GG * f.x Y) := by
  rw [mul_assoc, (hf.x_fn Y g hg).eq, ← mul_assoc, fn_comm L (mG L) hg, mul_assoc]

theorem frame_x_commute {L : LevelData A r} {f : FrameData S A} (hf : IsFrame L f) (Y Y' : ℂ) :
    io L.GG * f.x Y * (io L.GG * f.x Y') = io L.GG * f.x Y' * (io L.GG * f.x Y) := by
  have h1 := (hf.x_fn Y _ (mG L)).eq
  have h2 := (hf.x_fn Y' _ (mG L)).eq
  have h3 := (hf.x_commute Y Y').eq
  linear_combination (norm := noncomm_match_scalars) io L.GG * h1 * f.x Y' - io L.GG * h2 * f.x Y + io L.GG * io L.GG * h3

theorem frame_x_inv_mul_x {L : LevelData A r} {f : FrameData S A} (hf : IsFrame L f) {Y : ℂ} (hY : Y ∈ f.inv) :
    f.xi Y * io L.GGi * (io L.GG * f.x Y) = 1 := by
  have h1 : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by rw [← io_mul, L.GGi_GG]; simp [io]
  rw [mul_assoc, ← mul_assoc (io L.GGi), h1, one_mul, (hf.x_xi Y hY).2]

theorem frame_core {L : LevelData A r} {f : FrameData S A} (hf : IsFrame L f) {Y Ya : ℂ} (hY : Y ∈ f.reg)
    (hYa : Ya ∈ f.inv) (hYa1 : Ya + 1 ∈ f.inv) :
    (Y - Ya) • (io L.GG * f.x Y * f.l L Ya * f.F - f.l L Ya * (io L.GG * f.x Y) * f.F) =
      io L.GG * f.x Y * f.l L Ya * f.F - f.F * f.TT Y 1 0 :=
  core1 (Y - Ya) f.F (f.TT Y 1 1) (f.TT Ya 1 1) (f.TT Y 1 0) (f.TT Ya 1 0) (io L.GG * f.x Y) (io L.GG * f.x Ya)
    (f.xi Ya * io L.GGi) (f.l L Ya) (hf.frame_τ Y hY) (hf.frame_τ Ya (hf.inv_reg hYa)) (hf.frame_l Ya hYa hYa1)
    (frame_x_commute hf Y Ya) (frame_x_inv_mul_x hf hYa)
    (rtt_relation_entries ℂ (SlopeTestRemainingChoices S A) f.TT Ya Y (hf.module.rtt Ya (hf.inv_reg hYa) Y hY) 1 1 1 0)

theorem free_l {L : LevelData A r} {f : FrameData S A} {a : S} (hfree : f.Free a) (Y : ℂ) : FreeOf a (f.l L Y) :=
  fr_add (fr_io a _) (fr_mul (fr_io a _) (hfree.2.2.2.2.2.2.2.2 Y))

theorem free_P {L : LevelData A r} {f : FrameData S A} {a : S} (hfree : f.Free a) (Ya : ℂ) :
    FreeOf2 a (!![io L.ζi, 0; 0, io L.ζbi] * !![1, 0; io L.GG * f.l L Ya, io L.GG] : M2 (SlopeTestRemainingChoices S A)) :=
  freeOf2_mul_of_free (fr2 (fr_io a _) (fr_zero a) (fr_zero a) (fr_io a _))
    (fr2 (fr_one a) (fr_zero a) (fr_mul (fr_io a _) (free_l hfree Ya)) (fr_io a _))

theorem plusTau : PlusTau := by
  intro A S _ _ _ _ _ _ r L f a Ya ⟨_, hf, hfree, _, hYa, hYa1, _⟩ Y ⟨hY, hD⟩
  have hD1 : Y - Ya - 1 ≠ 0 := sub_ne_zero.mpr hD
  have hP := free_P (L := L) hfree Ya
  have hFf : FreeOf a f.F := hfree.2.2.1
  have hTf : FreeOf a (io L.GG * f.x Y) := fr_mul (fr_io a _) (hfree.2.2.2.2.1 Y)
  have key := tau_mat (Y - Ya) hD1 (io L.ζi) (io L.ζbi) (io L.GG) (f.l L Ya) f.F (f.TT Y 1 1) (f.TT Y 1 0)
    (io L.GG * f.x Y) (hf.frame_τ Y hY) (T_fn hf Y (mζi L))
    (by rw [← mul_assoc, T_fn hf Y (mζbi L), mul_assoc, T_fn hf Y (mG L), ← mul_assoc])
    (frame_core hf hY hYa hYa1)
  have key2 := congrArg (ins a) key
  rw [Wd1.ins_mul a _ _ hP, Wd1.ins_mul a _ _ (fr2 hFf (fr_zero a) (fr_zero a) hFf), ins_dd,
    Wd1.ins_mul a _ _ (fr2 hTf (fr_zero a) (fr_zero a) hTf), ins_dd,
    Wd1.ins_mul a _ _ (fr2 (fr_smul _ (fr_one a)) (fr_zero a) (fr_zero a) (fr_one a)),
    Wd1.ins_mul a _ _ hP, ins_dd, ← tau_after_rmatrix a _ (hfree.2.1 Y)] at key2
  simp only [FrameData.plus]
  rw [mul_assoc, key2]
  simp only [mul_assoc]

end Main

section Main2
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem io_add (x y : A) : (io (x + y) : SlopeTestRemainingChoices S A) = io x + io y := by simp [io]
theorem io_sub (x y : A) : (io (x - y) : SlopeTestRemainingChoices S A) = io x - io y := by simp [io]
theorem io_neg (x : A) : (io (-x) : SlopeTestRemainingChoices S A) = -io x := by simp [io]
theorem io_one : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := by simp [io]
theorem io_smul (c : ℂ) (x : A) : (io (c • x) : SlopeTestRemainingChoices S A) = c • io x := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j <;> simp [io, h]

theorem fnC (L : LevelData A r) {y : SlopeTestRemainingChoices S A} (h : ∀ g ∈ zfns L, Commute y (io g)) :
    y * kapL L = kapL L * y ∧ y * io (L.ζb * L.GGi) = io (L.ζb * L.GGi) * y ∧
      y * (io L.ζbi * io L.GG) = io L.ζbi * io L.GG * y ∧ y * tz L = tz L * y := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold kapL
    rw [io_mul, io_mul]
    exact (((h _ (mζb L)).mul_right (h _ (mζi L))).mul_right (h _ (mGi L))).eq
  · rw [io_mul]
    exact ((h _ (mζb L)).mul_right (h _ (mGi L))).eq
  · exact ((h _ (mζbi L)).mul_right (h _ (mG L))).eq
  · unfold tz
    rw [io_smul]
    exact ((h _ (mζbi L)).smul_right L.TT).eq

theorem fn_fn (L : LevelData A r) {g : A} (hg : g ∈ zfns L) : ∀ h ∈ zfns L, Commute (io g : SlopeTestRemainingChoices S A) (io h) :=
  fun _ hh => fn_comm L hg hh

theorem kap_fn (L : LevelData A r) : ∀ g ∈ zfns L, Commute (kapL L : SlopeTestRemainingChoices S A) (io g) :=
  fun _ hg => ((fnC L (fn_fn L hg)).1).symm

theorem bet_fn (L : LevelData A r) : ∀ g ∈ zfns L, Commute (io (L.ζb * L.GGi) : SlopeTestRemainingChoices S A) (io g) :=
  fun _ hg => ((fnC L (fn_fn L hg)).2.1).symm

theorem embed_lowering_constant (L : LevelData A r) (Y : ℂ) :
    (io (L.l0 Y) : SlopeTestRemainingChoices S A) = -io L.nab - (Y + 1 / 2) • io (L.ζb * L.GGi) := by
  unfold LevelData.l0
  rw [io_sub, io_neg, ← Algebra.smul_def, io_smul]

theorem plusL : PlusL := by
  intro A S _ _ _ _ _ _ r L f a Ya ⟨_, hf, hfree, _, hYa, hYa1, _⟩ Y ⟨hY, hD0, hD⟩ ⟨hY1, _, _⟩
  have hD0 : Y - Ya ≠ 0 := hD0
  have hD1 : Y - Ya - 1 ≠ 0 := sub_ne_zero.mpr hD
  have hD0' : Ya - Y ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.mpr hD0
  have hYr := hf.inv_reg hY
  have hYar := hf.inv_reg hYa
  have hP := free_P (L := L) hfree Ya
  have hFf : FreeOf a f.F := hfree.2.2.1
  have hxf := hfree.2.2.2.2.1
  have hxif := hfree.2.2.2.2.2.1
  have hef := hfree.2.2.2.2.2.2.2.2
  have hTf : FreeOf a (io L.GG * f.x Y) := fr_mul (fr_io a _) (hxf Y)
  have hκf : FreeOf a (kapL L : SlopeTestRemainingChoices S A) := fr_io a _
  have hddf : FreeOf a (f.DD Y Ya) := fr_smul _ (fr_sub (hef Y) (hef Ya))

  have he : f.ee Y = f.ee Ya + (Y - Ya) • f.DD Y Ya := by
    simp [FrameData.DD, smul_smul, mul_inv_cancel₀ hD0]
  have hl0 : (io (L.l0 Y) : SlopeTestRemainingChoices S A) = io (L.l0 Ya) - (Y - Ya) • io (L.ζb * L.GGi) := by
    rw [← io_smul, ← io_sub, ← l0_linear_in_Y]
  have hlη : f.l L Y = f.l L Ya + (Y - Ya) • (-io (L.ζb * L.GGi) + kapL L * f.DD Y Ya) := by
    unfold FrameData.l
    rw [hl0, he]
    noncomm_match_scalars
  have hlη' : f.l L Ya = f.l L Y + (Ya - Y) • (-io (L.ζb * L.GGi) + kapL L * f.DD Y Ya) := by
    rw [hlη]
    noncomm_match_scalars
  have hdd_fn : ∀ g ∈ zfns L, Commute (f.DD Y Ya) (io g) := fun g hg =>
    ((hf.ee_fn Y g hg).sub_left (hf.ee_fn Ya g hg)).smul_left _

  have hs := hf.frame_l Y hY hY1
  have hsa := hf.frame_l Ya hYa hYa1
  have r1 := core2 (Y - Ya) f.F f.Fi (io L.GG * f.x Y) (f.l L Ya) (f.l L Y) hf.F_Fi
    (by rw [← hs]; exact frame_core hf hYr hYa hYa1)
  have r2 := core2 (Ya - Y) f.F f.Fi (io L.GG * f.x Ya) (f.l L Y) (f.l L Ya) hf.F_Fi
    (by rw [← hsa]; exact frame_core hf hYar hY hY1)
  have c1 := rel1 hD0 _ _ _ _ hlη r1
  have c2 := rel1 hD0' _ _ _ _ hlη' r2
  have r3 := commute_of_conj_alt f.F f.Fi (f.TT Y 1 0) (f.TT Ya 1 0) _ _ hf.F_Fi hs hsa (hf.lowerLeftEntry_commute Y hYr Ya hYar).eq
  have c3 := rel3 _ _ _ _ _ _ _ c1 c2 r3 (frame_x_commute hf Y Ya) (frame_x_inv_mul_x hf hY) (frame_x_inv_mul_x hf hYa)
  have hGi : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by rw [← io_mul, L.GGi_GG, io_one]
  have hlx : (io (L.l0 Y) : SlopeTestRemainingChoices S A) * f.x Ya = f.x Ya * io (L.l0 Y) := by
    rw [embed_lowering_constant]
    exact (((hf.x_nab Ya).neg_right).sub_right
      (Commute.smul_right (show Commute _ _ from (fnC L (hf.x_fn Ya)).2.1) _)).eq.symm
  have hconj := conj_abs (io L.GG) (io L.GGi) (f.x Ya) (f.xi Ya) (kapL L) (io (L.ζ * L.ζbi * L.GG)) (io (L.l0 Y))
    (io (L.ζb * L.GGi)) (f.ee Y) (f.DD Y Ya) c2
    (by rw [← io_sub, ← io_mul, ← io_mul, a_l0G]) (kap_fn L _ (mG L)).eq (hf.ee_fn Y _ (mG L)).eq hGi hlx
    (fnC L (hf.x_fn Ya)).2.1.symm (fnC L (hf.x_fn Ya)).1.symm
    (by unfold kapL; rw [← io_mul, a_κi, io_one]) (hf.x_xi Ya hYa).2
  have key := L_mat (Y - Ya) hD0 hD1 (io L.ζi) (io L.ζbi) (io L.GG) (io (L.ζb * L.GGi)) (kapL L) (io (L.l0 Ya))
    (io (L.l0 Y)) (f.ee Ya) (f.ee Y) (f.DD Y Ya) (tz L) (f.x Ya) (f.xi Ya) (f.l L Ya) (f.l L Y)
    (-io (L.ζb * L.GGi) + kapL L * f.DD Y Ya) f.F (f.TT Y 1 1) (f.TT Y 1 0) (io L.GG * f.x Y)
    hl0 he rfl rfl rfl (hf.frame_τ Y hYr) hs (T_fn hf Y (mζi L))
    (by rw [← mul_assoc, T_fn hf Y (mζbi L), mul_assoc, T_fn hf Y (mG L), ← mul_assoc])
    c1 c3 hconj
    (by rw [← io_mul, a_l0zi, io_add, io_mul, io_mul])
    (bet_fn L _ (mζi L)).eq (kap_fn L _ (mζi L)).eq (hf.ee_fn Ya _ (mζi L)).eq (hdd_fn _ (mζi L)).eq
    (fnC L (fn_fn L (mζi L))).2.2.2.symm
    (by unfold kapL; rw [← io_mul, ← io_mul, a_κw])
    (by unfold kapL tz; rw [← io_mul, ← io_add, zeta_GG_identity])
    (by rw [← io_mul, ← io_mul, l0_conj_zeta_GG, io_mul, io_mul, io_sub])
    (fnC L (bet_fn L)).2.2.1 (fnC L (kap_fn L)).2.2.1 (fnC L (hf.ee_fn Ya)).2.2.1 (fnC L hdd_fn).2.2.1
  have hLm : FreeOf2 a !![io (L.l0 Y) + kapL L * (f.ee Y - f.DD Y Ya + tz L), kapL L * (-((Y - Ya)⁻¹ • 1)); 0,
      io (L.l0 Y) + kapL L * (f.xi Ya * f.ee Y * f.x Ya)] :=
    fr2 (fr_add (fr_io a _) (fr_mul hκf (fr_add (fr_sub (hef Y) hddf) (fr_io a _))))
      (fr_mul hκf (fr_neg (fr_smul _ (fr_one a)))) (fr_zero a)
      (fr_add (fr_io a _) (fr_mul hκf (fr_mul (fr_mul (hxif Ya) (hef Y)) (hxf Ya))))
  have key2 := congrArg (ins a) key
  rw [Wd1.ins_mul a _ _ hP, Wd1.ins_mul a _ _ (fr2 hFf (fr_zero a) (fr_zero a) hFf), ins_dd,
    Wd1.ins_mul a _ _ (fr2 hTf (fr_zero a) (fr_zero a) hTf), ins_dd,
    Wd1.ins_mul a _ _ (fr2 (fr_smul _ (fr_one a)) (fr_zero a) (fr_zero a) (fr_one a)),
    Wd1.ins_mul a _ _ hLm, Wd1.ins_mul a _ _ hP, ins_dd, ← t21_after_rmatrix a _ (hfree.2.1 Y),
    ← ins_affine a _ _ _ _ _ hκf] at key2
  have hl' : (f.plus L a Ya).l L Y = io (L.l0 Y) + kapL L * ins a !![f.ee Y - f.DD Y Ya + tz L,
      -((Y - Ya)⁻¹ • 1); 0, f.xi Ya * f.ee Y * f.x Ya] := rfl
  rw [hl']
  simp only [FrameData.plus]
  rw [mul_assoc, key2]
  simp only [mul_assoc]

end Main2

end Formalism.FourierDecayAlt.P.Fr6

namespace Formalism.FourierDecayAlt.P

theorem plus_letter_tau : Formalism.FourierDecayAlt.Fr.PlusTau := Fr6.plusTau

theorem plus_letter_l : Formalism.FourierDecayAlt.Fr.PlusL := Fr6.plusL

end Formalism.FourierDecayAlt.P
