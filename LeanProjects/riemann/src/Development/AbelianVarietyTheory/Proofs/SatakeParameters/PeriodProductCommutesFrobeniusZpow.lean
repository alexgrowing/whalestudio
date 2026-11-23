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

namespace GlobalTheory.Pst.TwistLetters

theorem units_zpow_bilin_comm {R M₁ M₂ M₃ : Type} [CommRing R] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    (B : M₁ →ₗ[R] M₂ →ₗ[R] M₃) (u₁ : (Module.End R M₁)ˣ) (u₂ : (Module.End R M₂)ˣ) (u₃ : (Module.End R M₃)ˣ)
    (h : ∀ x y, (u₃ : Module.End R M₃) (B x y) = B ((u₁ : Module.End R M₁) x) ((u₂ : Module.End R M₂) y))
    (n : ℤ) (x : M₁) (y : M₂) :
    ((u₃ ^ n : (Module.End R M₃)ˣ) : Module.End R M₃) (B x y) =
      B (((u₁ ^ n : (Module.End R M₁)ˣ) : Module.End R M₁) x) (((u₂ ^ n : (Module.End R M₂)ˣ) : Module.End R M₂) y) := by
  have hinv : ∀ x y, ((u₃⁻¹ : (Module.End R M₃)ˣ) : Module.End R M₃) (B x y) =
      B (((u₁⁻¹ : (Module.End R M₁)ˣ) : Module.End R M₁) x) (((u₂⁻¹ : (Module.End R M₂)ˣ) : Module.End R M₂) y) := by
    intro x y
    have e₁ := LinearMap.congr_fun (Units.mul_inv u₁) x
    have e₂ := LinearMap.congr_fun (Units.mul_inv u₂) y
    rw [Module.End.mul_apply, Module.End.one_apply] at e₁ e₂
    conv_lhs => rw [← e₁, ← e₂, ← h]
    have e₃ := LinearMap.congr_fun (Units.inv_mul u₃) (B (((u₁⁻¹ : (Module.End R M₁)ˣ) : Module.End R M₁) x) (((u₂⁻¹ : (Module.End R M₂)ˣ) : Module.End R M₂) y))
    rw [Module.End.mul_apply, Module.End.one_apply] at e₃
    exact e₃
  induction n using Int.induction_on generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one, zpow_add_one, Units.val_mul, Units.val_mul, Units.val_mul,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, h, ih]
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one, zpow_sub_one, Units.val_mul, Units.val_mul, Units.val_mul,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hinv, ih]

end GlobalTheory.Pst.TwistLetters

namespace GlobalTheory.Pst.TwistLetters

theorem phiU_zpow_dmul : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V) (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1) (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρs)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρm)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρt)] (n : ℤ) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)), ((phiU P ρt ^ n : (Module.End ↥L.1 ↥(Dpst P ρt))ˣ) : Module.End ↥L.1 ↥(Dpst P ρt)) (GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht x y) = GlobalTheory.Pst.TwistLetters.dmul P ρs ρt ρm χ hm ht (((phiU P ρs ^ n : (Module.End ↥L.1 ↥(Dpst P ρs))ˣ) : Module.End ↥L.1 ↥(Dpst P ρs)) x) (((phiU P ρm ^ n : (Module.End ↥L.1 ↥(Dpst P ρm))ˣ) : Module.End ↥L.1 ↥(Dpst P ρm)) y) := by
  intro l _ P K L V _ _ _ _ ρs ρt ρm χ hm ht _ _ _ n x y
  exact units_zpow_bilin_comm (dmul P ρs ρt ρm χ hm ht) (phiU P ρs) (phiU P ρm) (phiU P ρt)
    (fun x y => phiD_dmul P ρs ρt ρm χ hm ht x y) n x y

end GlobalTheory.Pst.TwistLetters
