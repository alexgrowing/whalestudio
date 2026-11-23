import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.OrderOKOneInert
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.IsLatticeOfCompactOpen
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.IdxAd

section Single

variable {F : Type} [Field F] [NumberField F]

open Classical in

def sgl (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F →+ FiniteAdeleRing (𝓞 F) F where
  toFun x := RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v x
  map_zero' := RestrictedProduct.single_zero _ v
  map_add' := RestrictedProduct.single_add _ v

theorem sgl_same (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : sgl v x v = x := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v x

theorem sgl_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : v.adicCompletion F) : sgl v x w = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) x h

end Single

def swapC (k : Type) [CommRing k] : (k × k) →ₐ[k] k × k := (GlobalTheory.CompanionTheory.SplitIdx.swapAlg k).toAlgHom

theorem swapC_apply {k : Type} [CommRing k] (z : k × k) : swapC k z = z.swap := rfl

end GlobalTheory.CompanionTheory.IdxAd
