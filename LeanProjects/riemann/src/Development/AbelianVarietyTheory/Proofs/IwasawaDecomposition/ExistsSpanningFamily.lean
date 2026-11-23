import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section
namespace GlobalTheory.PhtSpan

open GlobalTheory.DRFil

section Ev
variable {Q F LL : Type} [Field Q] [CharZero Q] [Field F] [Algebra Q F] [FiniteDimensional Q F]
  [Field LL] [Algebra Q LL]

def ev (τ : F →ₐ[Q] LL) : LL ⊗[Q] F →ₗ[LL] LL :=
  (Algebra.TensorProduct.lift (AlgHom.id LL LL) τ (fun _ _ => Commute.all _ _)).toLinearMap

@[simp] theorem ev_tmul (τ : F →ₐ[Q] LL) (a : LL) (c : F) : ev τ (a ⊗ₜ[Q] c) = a * τ c := by
  simp [ev]

def e (τ : F →ₐ[Q] LL) : LL ⊗[Q] F := (exists_idem τ).choose

end Ev
end GlobalTheory.PhtSpan

namespace GlobalTheory.PhtSpan
open GlobalTheory.DRFil

section Mod
variable {Q F LL : Type} [Field Q] [CharZero Q] [Field F] [Algebra Q F] [FiniteDimensional Q F]
  [Field LL] [Algebra Q LL] {B : Type} [CommRing B] [Algebra Q B] [Algebra F B] [IsScalarTower Q F B]
  {V : Type} [AddCommGroup V] [Module LL V] [Module Q V] [IsScalarTower Q LL V]

end Mod
end GlobalTheory.PhtSpan

namespace GlobalTheory.PhtSpan
open GlobalTheory.DRFil

end GlobalTheory.PhtSpan
