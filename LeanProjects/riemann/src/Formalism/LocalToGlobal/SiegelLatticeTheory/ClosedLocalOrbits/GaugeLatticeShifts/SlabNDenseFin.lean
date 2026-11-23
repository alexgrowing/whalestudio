import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDenseSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDenseRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictLat

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB PIW.AdelClassFin

section Alg

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K] [Invertible (2 : K)]
variable {J J' : Matrix ι ι K}

theorem sharp_mul' (h : J * J' = 1) (A B : Matrix ι ι K) : sharp J J' (A * B) = sharp J J' B * sharp J J' A := by
  unfold sharp
  rw [conjTranspose_mul]
  calc J' * (Bᴴ * Aᴴ) * J = J' * Bᴴ * (J * J') * Aᴴ * J := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem sharp_pow' (h : J * J' = 1) (h' : J' * J = 1) (A : Matrix ι ι K) (j : ℕ) :
    sharp J J' (A ^ j) = sharp J J' A ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, sharp_one h']
  | succ j ih => rw [pow_succ, sharp_mul' h, ih, pow_succ']

theorem sharp_geo (h : J * J' = 1) (h' : J' * J = 1) (A : Matrix ι ι K) (N : ℕ) :
    sharp J J' (geo N A) = geo N (sharp J J' A) := by
  unfold geo
  induction N with
  | zero => simp [sharp]
  | succ N ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, sharp_add, ih, sharp_pow' h h']

def icay (N : ℕ) (M : Matrix ι ι K) : Matrix ι ι K := (M - 1) * geo N (-((⅟2 : K) • (M - 1)))

theorem cay_icay {N : ℕ} {M : Matrix ι ι K} (hT : ((⅟2 : K) • (M - 1)) ^ N = 0)
    (hZ : ((⅟2 : K) • icay N M) ^ N = 0) : cay N (icay N M) = M := by
  set A : Matrix ι ι K := (⅟2 : K) • (M - 1) with hA
  set G := geo N (-A) with hG
  have hAN : (-A) ^ N = 0 := by rw [neg_pow, hT, mul_zero]
  have hAG : (1 + A) * G = 1 := by
    have := mul_neg_geom_sum (-A) N
    rw [sub_neg_eq_add, hAN, sub_zero] at this
    exact this
  have hZ2 : (⅟2 : K) • icay N M = A * G := by rw [icay, Matrix.smul_mul]
  have h1 : 1 - A * G = G := by
    have e : (1 + A) * G = G + A * G := by rw [Matrix.add_mul, Matrix.one_mul]
    rw [e] at hAG
    rw [← hAG]; abel
  have hgeo : (1 - (⅟2 : K) • icay N M) * geo N ((⅟2 : K) • icay N M) = 1 := by
    rw [geo, mul_neg_geom_sum, hZ, sub_zero]
  rw [hZ2, h1] at hgeo
  have hg : geo N ((⅟2 : K) • icay N M) = 1 + A := by
    calc geo N ((⅟2 : K) • icay N M) = (1 + A) * G * geo N ((⅟2 : K) • icay N M) := by rw [hAG, Matrix.one_mul]
      _ = 1 + A := by rw [Matrix.mul_assoc, hZ2, hgeo, Matrix.mul_one]
  have hGA : G * (1 + A) = 1 := by
    have := geom_sum_mul_neg (-A) N
    rw [sub_neg_eq_add, hAN, sub_zero] at this
    exact this
  unfold cay
  rw [hg, icay, ← hG, Matrix.mul_assoc, hGA, Matrix.mul_one]
  abel

theorem icay_skew (h : J * J' = 1) (h' : J' * J = 1) {N : ℕ} {M P : Matrix ι ι K} (hS : sharp J J' M = P)
    (hPM : P * M = 1) (hT : ((⅟2 : K) • (M - 1)) ^ N = 0) (hT' : ((⅟2 : K) • (P - 1)) ^ N = 0) :
    sharp J J' (icay N M) = -icay N M := by
  set A : Matrix ι ι K := (⅟2 : K) • (M - 1) with hA
  set B : Matrix ι ι K := (⅟2 : K) • (P - 1) with hB
  have hsA : sharp J J' A = B := by rw [hA, hB, sharp_smul, star_half, sharp_sub, hS, sharp_one h']
  have hAN : (-A) ^ N = 0 := by rw [neg_pow, hT, mul_zero]
  have hBN : (-B) ^ N = 0 := by rw [neg_pow, hT', mul_zero]
  have hAG : (1 + A) * geo N (-A) = 1 := by
    have := mul_neg_geom_sum (-A) N
    rw [sub_neg_eq_add, hAN, sub_zero] at this
    exact this
  have hGB : geo N (-B) * (1 + B) = 1 := by
    have := geom_sum_mul_neg (-B) N
    rw [sub_neg_eq_add, hBN, sub_zero] at this
    exact this
  have hQ : (P - 1) * (M - 1) = (1 + 1) - P - M := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPM]
    abel
  have hH : (⅟2 : K) • ((P - 1) * (M - 1)) + (⅟2 : K) • ((P - 1) * (M - 1)) = (1 + 1) - P - M := by
    rw [half_add_half', hQ]
  have key : (P - 1) * (1 + A) = -((1 + B) * (M - 1)) := by
    have e1 : (P - 1) * (1 + A) = (P - 1) + (⅟2 : K) • ((P - 1) * (M - 1)) := by
      rw [Matrix.mul_add, Matrix.mul_one, hA, Matrix.mul_smul]
    have e2 : (1 + B) * (M - 1) = (M - 1) + (⅟2 : K) • ((P - 1) * (M - 1)) := by
      rw [Matrix.add_mul, Matrix.one_mul, hB, Matrix.smul_mul]
    rw [e1, e2]
    refine eq_neg_of_add_eq_zero_left ?_
    calc (P - 1) + (⅟2 : K) • ((P - 1) * (M - 1)) + ((M - 1) + (⅟2 : K) • ((P - 1) * (M - 1)))
        = ((⅟2 : K) • ((P - 1) * (M - 1)) + (⅟2 : K) • ((P - 1) * (M - 1))) + (P - 1) + (M - 1) := by abel
      _ = 0 := by rw [hH]; abel
  have hs : sharp J J' (icay N M) = geo N (-B) * (P - 1) := by
    rw [icay, sharp_mul' h, sharp_geo h h', sharp_neg, hsA, sharp_sub, hS, sharp_one h']
  rw [hs]
  calc geo N (-B) * (P - 1) = geo N (-B) * ((P - 1) * (1 + A)) * geo N (-A) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, hAG, Matrix.mul_one]
    _ = -(geo N (-B) * (1 + B) * ((M - 1) * geo N (-A))) := by
        rw [key]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -icay N M := by rw [hGB, Matrix.one_mul, icay]

end Alg

section Star

variable {D : D7} (X : HidaSetting D)

abbrev sA : RA X →+* RA X := Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)

theorem sA_invol (r : RA X) : sA X (sA X r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    show Algebra.TensorProduct.map X.B.I.cm.sig (AlgHom.id X.B.I.F (Af X.B.I.F))
      (Algebra.TensorProduct.map X.B.I.cm.sig (AlgHom.id X.B.I.F (Af X.B.I.F)) (a ⊗ₜ[X.B.I.F] b)) =
        a ⊗ₜ[X.B.I.F] b
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    have e : X.B.I.cm.sig (X.B.I.cm.sig a) = a := star_star a
    rw [e]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

@[reducible] def starRA : StarRing (RA X) where
  star := sA X
  star_involutive := sA_invol X
  star_mul := fun a b => by rw [map_mul, mul_comm]
  star_add := fun a b => map_add _ a b

attribute [local instance] starRA

theorem star_ic (e : X.B.I.E) : star (ic X e) = ic X (star e) := DictLat.sigR_inclE X.B.I e

theorem map_cT {m p : Type*} (M : Matrix m p X.B.I.E) : (M.map (ic X))ᴴ = (Mᴴ).map (ic X) := by
  ext i j
  simp only [conjTranspose_apply, map_apply]
  exact star_ic X _

theorem cT_eqR {m p : Type} (M : Matrix m p (RA X)) :
    Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) M = Mᴴ := by
  ext i j
  rfl

abbrev JA : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (RA X) := X.B.I.J.map (ic X)
def JBf' : Matrix (Kap X) (Kap X) (RA X) := (JB' X).map (ic X)

theorem Bf_mul_Bf' : Bf X * Bf' X = 1 := by
  unfold Bf Bf'
  rw [← Matrix.map_mul, Bm_mul_Bm', Matrix.map_one _ (map_zero _) (map_one _)]

theorem Bf'_mul_Bf : Bf' X * Bf X = 1 := by
  unfold Bf Bf'
  rw [← Matrix.map_mul, Bm'_mul_Bm, Matrix.map_one _ (map_zero _) (map_one _)]

theorem JBf'_mul : JBf' X * JBf X = 1 := by
  unfold JBf JBf'
  rw [← Matrix.map_mul, JB'_mul_JB, Matrix.map_one _ (map_zero _) (map_one _)]

theorem JBf_mul : JBf X * JBf' X = 1 := by
  unfold JBf JBf'
  rw [← Matrix.map_mul, JB_mul_JB', Matrix.map_one _ (map_zero _) (map_one _)]

theorem JBf_graded : Graded (lvk X) (2 * D.R.rS + 2) (JBf X) := fun i j h =>
  JB_graded X i j fun h0 => h (by simp [JBf, h0])

theorem JBf'_graded : Graded (lvk X) (2 * D.R.rS + 2) (JBf' X) := fun i j h =>
  JB'_graded X i j fun h0 => h (by simp [JBf', h0])

theorem JBf_eq : JBf X = (Bf X)ᴴ * JA X * Bf X := by
  unfold JBf Bf
  rw [JB_eq, Matrix.map_mul, Matrix.map_mul, map_cT]

theorem fmat_unitary (x : X.B.I.Gf) : (X.B.I.fmat x)ᴴ * JA X * X.B.I.fmat x = JA X := by
  have hx : Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (X.B.I.fmat x) * JA X * X.B.I.fmat x = JA X :=
    x.2
  rwa [cT_eqR] at hx

theorem Mf_mul (x y : X.B.I.Gf) : Mf X (x * y) = Mf X x * Mf X y := by
  have e : X.B.I.fmat (x * y) = X.B.I.fmat x * X.B.I.fmat y := rfl
  unfold Mf
  rw [e]
  calc Bf' X * (X.B.I.fmat x * X.B.I.fmat y) * Bf X
      = Bf' X * X.B.I.fmat x * (Bf X * Bf' X) * X.B.I.fmat y * Bf X := by
        rw [Bf_mul_Bf', Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem Mf_one : Mf X 1 = 1 := by
  have e : X.B.I.fmat 1 = 1 := by simp [AutInst.fmat]
  unfold Mf
  rw [e, Matrix.mul_one, Bf'_mul_Bf]

theorem Mf_unitary (x : X.B.I.Gf) : (Mf X x)ᴴ * JBf X * Mf X x = JBf X := by
  have hh : (Bf' X)ᴴ * (Bf X)ᴴ = 1 := by rw [← conjTranspose_mul, Bf_mul_Bf', conjTranspose_one]
  have hu := fmat_unitary X x
  rw [JBf_eq]
  unfold Mf
  calc (Bf' X * X.B.I.fmat x * Bf X)ᴴ * ((Bf X)ᴴ * JA X * Bf X) * (Bf' X * X.B.I.fmat x * Bf X)
      = (Bf X)ᴴ * (X.B.I.fmat x)ᴴ * ((Bf' X)ᴴ * (Bf X)ᴴ) * JA X * (Bf X * Bf' X) * X.B.I.fmat x * Bf X := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (Bf X)ᴴ * ((X.B.I.fmat x)ᴴ * JA X * X.B.I.fmat x) * Bf X := by
        rw [hh, Bf_mul_Bf', Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu]

theorem Mf_inv (x : X.B.I.Gf) : Mf X x⁻¹ = sharp (JBf X) (JBf' X) (Mf X x) := by
  have h1 : Mf X x * Mf X x⁻¹ = 1 := by rw [← Mf_mul, mul_inv_cancel, Mf_one]
  have h2 := sharp_mul_self (JBf'_mul X) (Mf_unitary X x)
  calc Mf X x⁻¹ = (sharp (JBf X) (JBf' X) (Mf X x) * Mf X x) * Mf X x⁻¹ := by rw [h2, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]

end Star

end Formalism.L2.SG.Pf.SlabNDensePf
