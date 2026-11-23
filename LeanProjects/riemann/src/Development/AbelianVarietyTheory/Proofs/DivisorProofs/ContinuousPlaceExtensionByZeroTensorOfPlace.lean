import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneStrongApproxGeneratorImports
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.ExtZero

open GlobalTheory.CompanionTheory.SaGen

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

theorem iB_tmul (P : PlaceMap F K) (x : K) (e : E) :
    iB (E := E) P (x ⊗ₜ[F] e) = P.inj x ⊗ₜ[F] e := rfl

theorem iB_eq_sum [FiniteDimensional F E] (P : PlaceMap F K) (y : K ⊗[F] E) :
    iB (E := E) P y = ∑ k, P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k) •
      ((1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) := by
  set B := Algebra.TensorProduct.basis K (Module.finBasis F E)
  conv_lhs => rw [← B.sum_repr y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [B, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, iB_tmul]

theorem continuous_iB [FiniteDimensional F E] [IsTopologicalRing K] (P : PlaceMap F K) :
    Continuous (iB (E := E) P) := by
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) (AF F ⊗[F] E)
  have hc : ∀ k, Continuous fun y : K ⊗[F] E =>
      (Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k := fun k =>
    IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis K (Module.finBasis F E)).coord k)
  have h : (iB (E := E) P : K ⊗[F] E → AF F ⊗[F] E) = fun y => ∑ k,
      P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k) •
        ((1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) := funext (iB_eq_sum P)
  rw [h]
  exact continuous_finset_sum _ fun k _ =>
    Continuous.smul (f := fun y => P.inj ((Algebra.TensorProduct.basis K (Module.finBasis F E)).repr y k))
      (g := fun _ => (1 : AF F) ⊗ₜ[F] (Module.finBasis F E) k) (P.cont_inj.comp (hc k)) continuous_const

end GlobalTheory.CompanionTheory.SaGen.ExtZero

theorem GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB_place : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] [TopologicalSpace K] [IsTopologicalRing K] (P : GlobalTheory.CompanionTheory.SaGen.PlaceMap F K), Continuous (GlobalTheory.CompanionTheory.SaGen.iB (E := E) P) :=
  fun P => GlobalTheory.CompanionTheory.SaGen.ExtZero.continuous_iB P
