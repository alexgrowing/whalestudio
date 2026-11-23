import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDetUnitAndTwist
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat

theorem nrmL_dlt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u β : B.A, IsUnit (GlobalTheory.TwLat.gram e b β) → B.σ β = β * ((-1) ^ (m - 1) * u) → (nrmL m w (GlobalTheory.TwLat.dlt e b β)).val = GlobalTheory.TwLat.mulMat e b u := by
  intro E _ _ _ _ w hw K e hec _ _ B m b u β hG hβ
  let B' : GlobalTheory.UnitLemma.InvAlg K := { B with g := u }
  have hGc0 := GlobalTheory.GramTwistNorm.gram_map_conj B' (w.adicCompletion E) e (cj w) hec m β hβ b
  set G := gram e b β with hGdef
  set P := mulMat e b u with hP
  set Φ := GlobalTheory.Tw.Phi m (w.adicCompletion E) with hΦ
  set s : w.adicCompletion E := (-1) ^ (m - 1) with hs
  have hGc : G.map (cj w) = s • (Gᵀ * P) := hGc0
  have hGd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have hΦT : Φᵀ * Φ = 1 := mul_eq_one_comm.1 (GlobalTheory.GramTwistNorm.phi_mul_transpose m)
  have hd : (dlt e b β).val = (G⁻¹)ᵀ * Φᵀ := by
    rw [dlt, dif_pos hG]
    change ((hG.unit⁻¹ : (Matrix (Fin m) (Fin m) (w.adicCompletion E))ˣ).val)ᵀ * Φᵀ = _
    rw [Matrix.coe_units_inv, IsUnit.unit_spec]
  have hdi : ((dlt e b β)⁻¹).val = Φ * Gᵀ := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hd, Matrix.mul_assoc, ← Matrix.mul_assoc Φᵀ, hΦT, Matrix.one_mul, ← Matrix.transpose_mul,
      Matrix.mul_nonsing_inv G hGd, Matrix.transpose_one]
  have hΦΦ : Φᵀ * Φᵀ = s • (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
    rw [← Matrix.transpose_mul, hΦ, GlobalTheory.GramTwistNorm.phi_mul_self, Matrix.transpose_smul, Matrix.transpose_one]
  have hθ : (thetaGL m (cj w) (dlt e b β)).val = Φ * (((dlt e b β)⁻¹).val.map (cj w))ᵀ * Φᵀ := rfl
  have hGG : (G⁻¹)ᵀ * Gᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv G hGd, Matrix.transpose_one]
  have hss : s * s = 1 := by rw [hs, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [nrmL, if_neg hw, Units.val_mul, hθ, hdi, Matrix.map_mul, hΦ, GlobalTheory.GramTwistNorm.phi_map, ← hΦ,
    Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose, hGc, hd]
  calc (G⁻¹)ᵀ * Φᵀ * (Φ * (s • (Gᵀ * P) * Φᵀ) * Φᵀ)
      = s • (((G⁻¹)ᵀ * Gᵀ) * P * (Φᵀ * Φᵀ)) + (0 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
        rw [add_zero]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Φᵀ Φ, hΦT, Matrix.one_mul]
    _ = P := by
        rw [add_zero, hGG, hΦΦ, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hss, one_smul]

end GlobalTheory.TwLat
