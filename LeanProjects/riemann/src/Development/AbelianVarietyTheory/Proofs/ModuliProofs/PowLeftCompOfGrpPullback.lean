import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

open GlobalTheory.ThetaObjPull

theorem pow_left_comp_of_grpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A]
    [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (x' : Out.baseOver S' ⟶ A')
    (x : Out.baseOver S ⟶ A) (e : x'.left ≫ φ = f ≫ x.left) (n : ℕ) :
    (x' ^ n).left ≫ φ = f ≫ (x ^ n).left := by
  have e₁ : pushHom h _ x' = toBase f ≫ x := Over.OverMorphism.ext e
  have e₂ : pushHom h _ (x' ^ n) = toBase f ≫ (x ^ n) := by
    rw [map_pow, e₁]
    exact (map_pow (preHom (toBase f)) _ _).symm
  exact congrArg (fun z => z.left) e₂

theorem gLies_pull : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S S₁ S₂ : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (c : S₁ ⟶ S) (s₁ : S₁ ⟶ Sp o) (t₁ : TObj g (N' ^ 2) J b s₁) (ψ₁ : t₁.A.left ⟶ A.left) (y : S₂ ⟶ S₁) (s₂ : S₂ ⟶ Sp o), L.IsLB → GLies A act Q c t₁ ψ₁ → LBIso t₁.L (L.pull ψ₁) → y ≫ s₁ = s₂ → ∃ (u : TObj g (N' ^ 2) J b s₂) (ψ : u.A.left ⟶ A.left), TMap u t₁ y ∧ GLies A act Q (y ≫ c) u ψ ∧ LBIso u.L (L.pull ψ) ∧ ∀ i, (u.pt i).left ≫ ψ = y ≫ (t₁.pt i).left ≫ ψ₁ := by
  intro o _ g N' J b S S₁ S₂ A _ L act Q c s₁ t₁ ψ₁ y s₂ hL ⟨h₁, h₂, h₃⟩ hI hs
  obtain ⟨u, φ, k₁, k₂, k₃, k₄⟩ := GlobalTheory.tObj_pull o g (N' ^ 2) J b S₁ S₂ s₁ s₂ y t₁ hs
  refine ⟨u, φ ≫ ψ₁, ⟨φ, k₁, k₂, k₃, k₄⟩, ⟨k₁.comp h₁, fun i => ?_, fun i => ?_⟩, ?_, fun i => ?_⟩
  · rw [← Category.assoc, k₄, Category.assoc, h₂, Category.assoc]
  · rw [← Category.assoc, pow_left_comp_of_grpPullback k₁ _ _ (k₃ i), Category.assoc, h₃, Category.assoc]
  · exact LBIso.trans u.isLB (pull_isLB t₁.isLB _) (pull_isLB hL _) k₂ (lbIso_pull_comp hI φ)
  · rw [← Category.assoc, k₃, Category.assoc]

end GlobalTheory.ZM.NearBuild
end
