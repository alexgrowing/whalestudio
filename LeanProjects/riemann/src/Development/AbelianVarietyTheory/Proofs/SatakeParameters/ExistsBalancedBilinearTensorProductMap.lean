import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CharpolyEqOfIsNilpotentSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFrobSSWdRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitOfStableLine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DmulMulDRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters

noncomputable section

namespace GlobalTheory.LetterDescent

open TensorProduct

variable {LL U D₁ D₂ D₃ : Type} [Field LL] [Field U] [AddCommGroup D₁] [Module LL D₁] [AddCommGroup D₂]
  [Module LL D₂] [AddCommGroup D₃] [Module LL D₃] (F : Type) [Field F] [Algebra LL F]

def baseBil (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) : F ⊗[LL] D₁ →ₗ[F] F ⊗[LL] D₂ →ₗ[F] F ⊗[LL] D₃ :=
  ((LinearMap.baseChangeHom LL F D₂ D₃) ∘ₗ β).liftBaseChange F

theorem baseBil_tmul (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (a b : F) (x : D₁) (y : D₂) :
    baseBil F β (a ⊗ₜ x) (b ⊗ₜ y) = (a * b) ⊗ₜ β x y := by
  simp [baseBil, LinearMap.liftBaseChange_tmul, TensorProduct.smul_tmul']

theorem baseBil_left (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (f₁ : Module.End LL D₁) (f₃ : Module.End LL D₃)
    (h : ∀ x y, β (f₁ x) y = f₃ (β x y)) (w : F ⊗[LL] D₁) (z : F ⊗[LL] D₂) :
    baseBil F β (f₁.baseChange F w) z = f₃.baseChange F (baseBil F β w z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp [map_add, LinearMap.add_apply, hw, hw']
  | tmul a x =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul b y => simp [LinearMap.baseChange_tmul, baseBil_tmul, h]

theorem baseBil_right (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (f₂ : Module.End LL D₂) (f₃ : Module.End LL D₃)
    (h : ∀ x y, β x (f₂ y) = f₃ (β x y)) (w : F ⊗[LL] D₁) (z : F ⊗[LL] D₂) :
    baseBil F β w (f₂.baseChange F z) = f₃.baseChange F (baseBil F β w z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => simp [map_add, LinearMap.add_apply, hw, hw']
  | tmul a x =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul b y => simp [LinearMap.baseChange_tmul, baseBil_tmul, h]

end GlobalTheory.LetterDescent

namespace GlobalTheory.LetterDescent

open TensorProduct

theorem exists_letter_tensor_map {LL U D₁ D₂ D₃ : Type} [Field LL] [Field U] [AddCommGroup D₁] [Module LL D₁]
    [AddCommGroup D₂] [Module LL D₂] [AddCommGroup D₃] [Module LL D₃] (m₁ : U →+* Module.End LL D₁)
    (m₂ : U →+* Module.End LL D₂) (m₃ : U →+* Module.End LL D₃) (F : Type) [Field F] [Algebra LL F]
    (τ : U →+* F) (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃) (h₁ : ∀ c x y, β (m₁ c x) y = m₃ c (β x y))
    (h₂ : ∀ c x y, β x (m₂ c y) = m₃ c (β x y)) :
    ∃ Φ : GlobalTheory.Pst.Letter m₁ F τ ⊗[F] GlobalTheory.Pst.Letter m₂ F τ →ₗ[F] GlobalTheory.Pst.Letter m₃ F τ,
      ∀ x y, Φ (GlobalTheory.Pst.letterMk m₁ F τ x ⊗ₜ GlobalTheory.Pst.letterMk m₂ F τ y) =
        GlobalTheory.Pst.letterMk m₃ F τ (β x y) := by
  let C : F ⊗[LL] D₁ →ₗ[F] F ⊗[LL] D₂ →ₗ[F] GlobalTheory.Pst.Letter m₃ F τ :=
    (baseBil F β).compr₂ (GlobalTheory.Pst.letterQ m₃ F τ)
  have hmem : ∀ (c : U) (v : F ⊗[LL] D₃),
      GlobalTheory.Pst.letterQ m₃ F τ ((m₃ c).baseChange F v - τ c • v) = 0 := by
    intro c v
    rw [← LinearMap.mem_ker, GlobalTheory.Pst.ker_letterQ]
    exact Submodule.mem_iSup_of_mem c ⟨v, rfl⟩
  have k₂ : GlobalTheory.Pst.letterKer m₂ F τ ≤ LinearMap.ker C.flip := by
    refine iSup_le fun c => ?_
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    ext w
    simp only [C, LinearMap.flip_apply, LinearMap.compr₂_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_sub, map_smul, baseBil_right F β (m₂ c) (m₃ c) (h₂ c), LinearMap.zero_apply]
    rw [← map_smul, ← map_sub]
    exact hmem c _
  let C₂ := (GlobalTheory.Pst.letterKer m₂ F τ).liftQ C.flip k₂
  have k₁ : GlobalTheory.Pst.letterKer m₁ F τ ≤ LinearMap.ker C₂.flip := by
    refine iSup_le fun c => ?_
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun q => ?_
    obtain ⟨z, rfl⟩ := GlobalTheory.Pst.letterQ_surjective m₂ F τ q
    change GlobalTheory.Pst.letterQ m₃ F τ (baseBil F β (((m₁ c).baseChange F - τ c • LinearMap.id : F ⊗[LL] D₁ →ₗ[F] F ⊗[LL] D₁) w) z) = 0
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, baseBil_left F β (m₁ c) (m₃ c) (h₁ c)]
    exact hmem c _
  refine ⟨TensorProduct.lift ((GlobalTheory.Pst.letterKer m₁ F τ).liftQ C₂.flip k₁), fun x y => ?_⟩
  change GlobalTheory.Pst.letterQ m₃ F τ (baseBil F β (1 ⊗ₜ x) (1 ⊗ₜ y)) = _
  rw [baseBil_tmul, mul_one]
  rfl

end GlobalTheory.LetterDescent
