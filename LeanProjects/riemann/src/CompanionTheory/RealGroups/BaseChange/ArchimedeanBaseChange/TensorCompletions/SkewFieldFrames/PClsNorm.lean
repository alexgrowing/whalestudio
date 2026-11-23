import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDetUnitAndTwist

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3.ClsNormP

theorem thetaGL_val' {k : Type} [CommRing k] (n : ℕ) (c : k →+* k) (g : GL (Fin n) k) :
    (thetaGL n c g).val = GlobalTheory.Tw.Phi n k * ((g⁻¹).val.map c)ᵀ * (GlobalTheory.Tw.Phi n k)ᵀ := rfl

theorem phi_mul_transpose_eq_one {k : Type} [CommRing k] (n : ℕ) : GlobalTheory.Tw.Phi n k * (GlobalTheory.Tw.Phi n k)ᵀ = 1 :=
  GlobalTheory.GramTwistNorm.phi_mul_transpose n

theorem units_map_val {k : Type} [Field k] {n : ℕ} {B : Type} [CommRing B]
    (ρ : B →+* Matrix (Fin n) (Fin n) k) (t : Bˣ) : (Units.map ρ.toMonoidHom t).val = ρ t := rfl

theorem units_map_inv_val {k : Type} [Field k] {n : ℕ} {B : Type} [CommRing B]
    (ρ : B →+* Matrix (Fin n) (Fin n) k) (t : Bˣ) : ((Units.map ρ.toMonoidHom t)⁻¹).val = ρ (↑t⁻¹ : B) := by
  rw [← map_inv]; rfl

theorem delta_theta {k : Type} [Field k] {n : ℕ} {c : k →+* k} {δ : GL (Fin n) k} {s : k} {B : Type} [CommRing B]
    {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} (hF : IsFrame c δ s d ρ) (t : Bˣ) :
    δ.val * (thetaGL n c (Units.map ρ.toMonoidHom t)).val = ρ (↑t⁻¹ : B) * δ.val := by
  rw [thetaGL_val', units_map_inv_val]
  calc δ.val * (GlobalTheory.Tw.Phi n k * ((ρ (↑t⁻¹ : B)).map c)ᵀ * (GlobalTheory.Tw.Phi n k)ᵀ)
      = (δ.val * GlobalTheory.Tw.Phi n k * ((ρ (↑t⁻¹ : B)).map c)ᵀ) * (GlobalTheory.Tw.Phi n k)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = ρ (↑t⁻¹ : B) * (δ.val * GlobalTheory.Tw.Phi n k) * (GlobalTheory.Tw.Phi n k)ᵀ := by rw [← hF.adj]
    _ = ρ (↑t⁻¹ : B) * δ.val := by rw [Matrix.mul_assoc, Matrix.mul_assoc, phi_mul_transpose_eq_one, Matrix.mul_one]

end CompanionTheory.Rg.BcB.G3.ClsNormP

namespace CompanionTheory.Rg.BcB.G3

theorem clsNorm_pf : ClsNorm := by
  intro k _ _ n c _ δ s _ _ B _ d ρ hF t
  apply Units.ext
  simp only [pt, map_mul, Units.val_mul]
  rw [ClsNormP.units_map_val]
  have h := ClsNormP.delta_theta hF t
  have h1 : ρ (t : B) * ρ (↑t⁻¹ : B) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  calc ρ (t : B) * δ.val * ((thetaGL n c (Units.map ρ.toMonoidHom t)).val * (thetaGL n c δ).val)
      = ρ (t : B) * (δ.val * (thetaGL n c (Units.map ρ.toMonoidHom t)).val) * (thetaGL n c δ).val := by
        simp only [Matrix.mul_assoc]
    _ = δ.val * (thetaGL n c δ).val := by
        rw [h, ← Matrix.mul_assoc, h1, Matrix.one_mul]

end CompanionTheory.Rg.BcB.G3

end
