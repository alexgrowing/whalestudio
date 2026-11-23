import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FnEquivApply
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat GlobalTheory.WholeFlag.Glue GlobalTheory.ConstLat.CramerFrame
open scoped Classical

namespace GlobalTheory.ConstLat.CramerFrame.LeftInverseFrame

local notation:70 A:70 " ⬝ₘ " B:71 => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

variable {R : Type} [CommRing R] {g : ℕ}

theorem leftInv_eq (U : Matrix (Fin (g + g)) (Fin g) R) (τ : Fin g → Fin (g + g)) :
    leftInv U τ = (rowSel τ ⬝ₘ U)⁻¹ ⬝ₘ (rowSel τ : Matrix (Fin g) (Fin (g + g)) R) := rfl

theorem leftInv_mul (M : Matrix (Fin (g + g)) (Fin g) R) (τ : Fin g → Fin (g + g))
    (hdet : ((rowSel τ : Matrix (Fin g) (Fin (g + g)) R) ⬝ₘ M).det = 1) : leftInv M τ ⬝ₘ M = 1 := by
  rw [leftInv_eq, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one)]

theorem leftInv_regAt {Z : Scheme.{0}} [IsIntegral Z] (M : Matrix (Fin (g + g)) (Fin g) Z.functionField)
    (τ : Fin g → Fin (g + g)) (hdet : ((rowSel τ : Matrix (Fin g) (Fin (g + g)) Z.functionField) ⬝ₘ M).det = 1)
    (x : Z) (hx : ∀ r k, RegAt x (M r k)) (l : Fin g) (r : Fin (g + g)) : RegAt x (leftInv M τ l r) := by
  have hinv : ((rowSel τ : Matrix (Fin g) (Fin (g + g)) Z.functionField) ⬝ₘ M)⁻¹ =
      ((rowSel τ : Matrix (Fin g) (Fin (g + g)) Z.functionField) ⬝ₘ M).adjugate := by
    rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  choose N hN using hx
  have hM : M = (Matrix.of N).map (algebraMap (Z.presheaf.stalk x) Z.functionField) := by
    ext a b; simp [hN]
  have hS : (rowSel τ : Matrix (Fin g) (Fin (g + g)) Z.functionField) =
      (rowSel τ : Matrix (Fin g) (Fin (g + g)) (Z.presheaf.stalk x)).map
        (algebraMap (Z.presheaf.stalk x) Z.functionField) := by
    ext a b; simp only [rowSel, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp
  have key : leftInv M τ = (((rowSel τ : Matrix (Fin g) (Fin (g + g)) (Z.presheaf.stalk x)) ⬝ₘ
      Matrix.of N).adjugate ⬝ₘ (rowSel τ : Matrix (Fin g) (Fin (g + g)) (Z.presheaf.stalk x))).map
      (algebraMap (Z.presheaf.stalk x) Z.functionField) := by
    rw [leftInv_eq, hinv, hM, hS, ← Matrix.map_mul, ← RingHom.mapMatrix_apply,
      ← RingHom.map_adjugate, RingHom.mapMatrix_apply, ← Matrix.map_mul]
  exact ⟨_, (congrFun (congrFun key l) r).symm⟩

end GlobalTheory.ConstLat.CramerFrame.LeftInverseFrame

theorem GlobalTheory.ConstLat.CramerFrame.leftInv_cramer_regular : ∀ {Z : Scheme.{0}} [IsIntegral Z] {g : ℕ} (M : Matrix (Fin (g + g)) (Fin g) Z.functionField) (τ : Fin g → Fin (g + g)), (rowSel τ * M).det = 1 → leftInv M τ * M = 1 ∧ ∀ x : Z, (∀ r k, RegAt x (M r k)) → ∀ l r, RegAt x (leftInv M τ l r) := by
  intro Z _ g M τ hdet
  exact ⟨LeftInverseFrame.leftInv_mul M τ hdet, fun x hx l r => LeftInverseFrame.leftInv_regAt M τ hdet x hx l r⟩
