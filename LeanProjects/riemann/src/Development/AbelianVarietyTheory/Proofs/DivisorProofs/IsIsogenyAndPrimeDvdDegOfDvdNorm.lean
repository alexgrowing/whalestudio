import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAevalEqProdAroots
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqMinpolyPow

open CategoryTheory GlobalTheory.AV GlobalTheory.AV.AbVar NumberField Polynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.DegNorm

theorem dvd_algebraMap_norm {S : Type} [CommRing S] [Module.Free ℤ S] [Module.Finite ℤ S] (x : S) :
    x ∣ algebraMap ℤ S (Algebra.norm ℤ x) := by
  classical
  let b := Module.Free.chooseBasis ℤ S
  let M := Algebra.leftMulMatrix b x
  have h0 : aeval x M.charpoly = 0 := by
    apply Algebra.leftMulMatrix_injective b
    rw [map_zero, ← Polynomial.aeval_algHom_apply]
    exact Matrix.aeval_self_charpoly M
  have hsplit : aeval x M.charpoly = x * aeval x M.charpoly.divX + algebraMap ℤ S (M.charpoly.coeff 0) := by
    conv_lhs => rw [← X_mul_divX_add M.charpoly]
    rw [map_add, map_mul, aeval_X, aeval_C]
  rw [h0] at hsplit
  refine ⟨-(algebraMap ℤ S ((-1) ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ S)) * aeval x M.charpoly.divX), ?_⟩
  rw [Algebra.norm_eq_matrix_det b, Matrix.det_eq_sign_charpoly_coeff, map_mul]
  linear_combination (-(algebraMap ℤ S ((-1) ^ Fintype.card (Module.Free.ChooseBasisIndex ℤ S)))) * hsplit

theorem isIsogeny_and_deg_ne_zero {K : Type} [Field K] (A : AbVar K) {F : Type} [Field F] [NumberField F]
    (ι : 𝓞 F →+* End A) (z : 𝓞 F) (hz : z ≠ 0) :
    IsIsogeny (A := A) (B := A) (ι z) ∧ deg (A := A) (B := A) (ι z) ≠ 0 := by
  obtain ⟨y, hy⟩ := dvd_algebraMap_norm z
  have hN : Algebra.norm ℤ z ≠ 0 := by
    intro h
    have h1 := Algebra.coe_norm_int z
    rw [h, Int.cast_zero, eq_comm, Algebra.norm_eq_zero_iff] at h1
    exact hz (by exact_mod_cast h1)
  have hc : ι y ≫ ι z = Algebra.norm ℤ z • 𝟙 A := by
    change ι z * ι y = _
    rw [← map_mul, ← hy, algebraMap_int_eq, Int.coe_castRingHom, map_intCast, ← zsmul_one]
    rfl
  have h := isIsogeny_comp_iff_and_deg_comp K A A A (ι y) (ι z) rfl rfl
  obtain ⟨hi, hd⟩ := GlobalTheory.MulIsogeny.mul_isogeny K A _ hN
  rw [hc] at h
  refine ⟨(h.1.1 hi).2, fun h0 => ?_⟩
  rw [h0, mul_zero] at h
  rw [h.2] at hd
  exact pow_ne_zero _ (Int.natAbs_ne_zero.2 hN) hd.symm

end GlobalTheory.AV.AbVar.DegNorm

namespace GlobalTheory.AV.AbVar.DegNorm

theorem charpoly_eq_minpoly_pow {K : Type} [Field K] (A : AbVar K) (hA : A.dim ≠ 0) {F : Type} [Field F]
    [NumberField F] (ι : 𝓞 F →+* End A) (x : 𝓞 F) :
    ∃ k : ℕ, 0 < k ∧ (charpoly (ι x)).map (Int.castRingHom ℚ) = minpoly ℚ (x : F) ^ k := by
  first
  | exact @_root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow
  | exact _root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow
  | (apply _root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CharpolyMinpolyPower.charpoly_eq_minpoly_pow ..)

end GlobalTheory.AV.AbVar.DegNorm

namespace GlobalTheory.AV.AbVar.DegNorm

open IntermediateField

end GlobalTheory.AV.AbVar.DegNorm
