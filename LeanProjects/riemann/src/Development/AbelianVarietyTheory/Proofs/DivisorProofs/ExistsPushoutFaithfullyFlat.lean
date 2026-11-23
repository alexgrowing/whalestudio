import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_pushout_faithfullyFlat : ∀ (R : Type) [CommRing R] (D D' E : Type) [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing E] [Algebra R E] (ψ : D →ₐ[R] D') (φ : D →ₐ[R] E), (ψ : D →+* D').FaithfullyFlat → ∃ (E' : Type) (_ : CommRing E') (_ : Algebra R E') (ψ' : E →ₐ[R] E') (φ' : D' →ₐ[R] E'), (ψ' : E →+* E').FaithfullyFlat ∧ ψ'.comp φ = φ'.comp ψ := by
  intro R _ D D' E _ _ _ _ _ _ ψ φ hψ
  letI : Algebra D E := φ.toRingHom.toAlgebra
  letI : Algebra D D' := ψ.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  let f : E →+* TensorProduct D E D' := Algebra.TensorProduct.includeLeftRingHom
  let g : D' →+* TensorProduct D E D' := (Algebra.TensorProduct.includeRight : D' →ₐ[D] _).toRingHom
  have hfg : f.comp (algebraMap D E) = g.comp (algebraMap D D') :=
    RingHom.ext fun d => by
      change (algebraMap D E d) ⊗ₜ[D] (1 : D') = (1 : E) ⊗ₜ[D] algebraMap D D' d
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  letI iR : Algebra R (TensorProduct D E D') := (f.comp (algebraMap R E)).toAlgebra
  have hf : f.FaithfullyFlat := by
    have : Module.FaithfullyFlat E (TensorProduct D E D') := inferInstance
    exact (RingHom.faithfullyFlat_algebraMap_iff).2 this
  refine ⟨TensorProduct D E D', inferInstance, iR,
    { f with commutes' := fun r => rfl },
    { g with commutes' := fun r => ?_ }, hf, ?_⟩
  · change g (algebraMap R D' r) = f (algebraMap R E r)
    rw [← ψ.commutes r, ← φ.commutes r]
    exact (congrArg (fun h => h (algebraMap R D r)) hfg).symm
  · ext d
    exact congrArg (fun h => h d) hfg

end GlobalTheory
