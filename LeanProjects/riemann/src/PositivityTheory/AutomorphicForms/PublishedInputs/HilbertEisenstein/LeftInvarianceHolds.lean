import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

namespace LeftInvarianceEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem rowA_vecMul (ξ : Fin 2 → F) (γ : GL (Fin 2) F) :
    rowA ξ ᵥ* ((ratGL F 2 γ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) =
      rowA (ξ ᵥ* (γ : Matrix (Fin 2) (Fin 2) F)) := by
  funext i
  exact (RingHom.map_vecMul (algebraMap F (Ad F)) (γ : Matrix (Fin 2) (Fin 2) F) ξ i).symm

def permE (γ : GL (Fin 2) F) : {ξ : Fin 2 → F // ξ ≠ 0} ≃ {ξ : Fin 2 → F // ξ ≠ 0} where
  toFun ξ := ⟨ξ.1 ᵥ* (γ : Matrix (Fin 2) (Fin 2) F), fun h => ξ.2 (by
    have := congrArg (· ᵥ* ((γ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
    simpa [Matrix.vecMul_vecMul] using this)⟩
  invFun ξ := ⟨ξ.1 ᵥ* ((γ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), fun h => ξ.2 (by
    have := congrArg (· ᵥ* (γ : Matrix (Fin 2) (Fin 2) F)) h
    simpa [Matrix.vecMul_vecMul] using this)⟩
  left_inv ξ := Subtype.ext (by simp [Matrix.vecMul_vecMul])
  right_inv ξ := Subtype.ext (by simp [Matrix.vecMul_vecMul])

theorem thetaS_ratGL (Ψ : (Fin 2 → Ad F) → ℂ) (a : (Ad F)ˣ) (γ : GL (Fin 2) F) (g : GA F 2) :
    thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) a * (ratGL F 2 γ * g)) =
      thetaS Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) a * g) := by
  unfold thetaS
  refine Eq.trans ?_ ((permE γ).tsum_eq (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} =>
    Ψ (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) :
      Matrix (Fin 2) (Fin 2) (Ad F)))))
  refine tsum_congr fun ξ => ?_
  rw [← mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, mul_assoc, Units.val_mul,
    ← Matrix.vecMul_vecMul, rowA_vecMul]
  rfl

theorem absD_ratGL (γ : GL (Fin 2) F) (g : GA F 2) : absD (ratGL F 2 γ * g) = absD g := by
  have h : Matrix.GeneralLinearGroup.det (ratGL F 2 γ) =
      IdeleGroup.diagonal F (Matrix.GeneralLinearGroup.det γ) := by
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap F (Ad F)) γ) = _
    rw [Matrix.GeneralLinearGroup.map_det]
    rfl
  unfold absD
  rw [map_mul, map_mul, h, IdeleGroup.ideleModule_diagonal, one_mul]

end LeftInvarianceEisenstein

theorem left_invariance_holds : SPois → SInt → SSmooth → SLeft := by
  intro _ _ _ F _ _ _ ω c γ g
  unfold Eis eisInt
  simp_rw [LeftInvarianceEisenstein.thetaS_ratGL, LeftInvarianceEisenstein.absD_ratGL]

end UpperTheory.HilbertEisensteinWeightOne
