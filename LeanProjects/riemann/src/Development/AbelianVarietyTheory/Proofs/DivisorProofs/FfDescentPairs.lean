import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FfDescentElem
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ff_descent_pairs : ∀ (R : Type) [CommRing R] (D D' : Type) [CommRing D] [Algebra R D]
    [CommRing D'] [Algebra R D'] (ψ : D →ₐ[R] D'), (ψ : D →+* D').FaithfullyFlat → ∀ a : D',
    (∀ (E : Type) [CommRing E] [Algebra R E] (α β : D' →ₐ[R] E), α.comp ψ = β.comp ψ → α a = β a) →
      ∃! e : D, ψ e = a := by
  intro R _ D D' _ _ _ _ ψ hψ a h
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  haveI : IsScalarTower R D D' := IsScalarTower.of_algebraMap_eq (fun r => (ψ.commutes r).symm)
  have hinj : Function.Injective (algebraMap D D') := FaithfulSMul.algebraMap_injective D D'
  let α : D' →ₐ[R] D' ⊗[D] D' := Algebra.TensorProduct.includeLeft
  let β : D' →ₐ[R] D' ⊗[D] D' := (Algebra.TensorProduct.includeRight).restrictScalars R
  have hαβ : α.comp ψ = β.comp ψ := by
    ext x
    show ψ x ⊗ₜ[D] (1 : D') = (1 : D') ⊗ₜ[D] ψ x
    have : ψ x = algebraMap D D' x := rfl
    rw [this, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hab : a ⊗ₜ[D] (1 : D') = (1 : D') ⊗ₜ[D] a := h _ α β hαβ
  obtain ⟨e, he⟩ := GlobalTheory.ff_descent_elem D D' a hab
  exact ⟨e, he, fun e' he' => hinj (he'.trans he.symm)⟩

end GlobalTheory
