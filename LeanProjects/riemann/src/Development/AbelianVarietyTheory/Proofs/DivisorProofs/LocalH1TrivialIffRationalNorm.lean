import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromKSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraMapMemMaximalRealSubfieldIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSqrtTotallyNegative
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSquareOneAddFourMul
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationComplexConjOfNotSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsUnramifiedAtOfIsSplitAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedAdjoinSqrtOfNotMem
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.LKTorus.KerOneLoc
open GlobalTheory.LKTorus.KerOne

section Basis

variable {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L]

theorem linearIndependent_one_theta (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x)
    (θ : L) (hθ : c θ = -θ) (hθ0 : θ ≠ 0) : LinearIndependent K ![(1 : L), θ] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
  have h' := congrArg c h
  rw [map_add, map_mul, hcK, hcK, hθ, map_zero] at h'
  have h2 : algebraMap K L (2 * s) = 0 := by rw [map_mul, map_ofNat]; linear_combination h + h'
  have hs : s = 0 := by
    have := (algebraMap K L).injective (h2.trans (map_zero _).symm)
    simpa using this
  subst hs
  rw [map_zero, zero_add] at h
  refine ⟨rfl, ?_⟩
  rcases mul_eq_zero.1 h with h | h
  · exact (algebraMap K L).injective (h.trans (map_zero _).symm)
  · exact absurd h hθ0

def basisTheta (c : L →ₐ[ℚ] L) (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x)
    (θ : L) (hθ : c θ = -θ) (hθ0 : θ ≠ 0) : Module.Basis (Fin 2) K L :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_theta c hcK θ hθ hθ0)
    (by rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two K L])

end Basis
end GlobalTheory.LKTorus.KerOneLoc

namespace GlobalTheory.LKTorus.KerOneLoc
open GlobalTheory.LKTorus.KerOne

section NormFormula

variable {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L]

def sigmaA (A : Type) [CommRing A] [Algebra K A] (c : L →ₐ[ℚ] L)
    (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) : A ⊗[K] L →ₐ[A] A ⊗[K] L :=
  Algebra.TensorProduct.map (AlgHom.id A A) (cK c hcK)

@[simp] theorem sigmaA_tmul (A : Type) [CommRing A] [Algebra K A] (c : L →ₐ[ℚ] L)
    (hcK : ∀ x : K, c (algebraMap K L x) = algebraMap K L x) (s : A) (y : L) :
    sigmaA A c hcK (s ⊗ₜ y) = s ⊗ₜ c y := rfl

end NormFormula
end GlobalTheory.LKTorus.KerOneLoc

namespace GlobalTheory.LKTorus.KerOneLoc

section Places

abbrev vP (p : ℕ) [hp : Fact p.Prime] : HeightOneSpectrum (𝓞 ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp.out⟩

variable {K : Type} [Field K] [NumberField K]

end Places
end GlobalTheory.LKTorus.KerOneLoc

namespace GlobalTheory.LKTorus.KerOneLoc
open GroundTheory.Global.SemiLocal

section Decomp

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion

variable {K : Type} [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]

def iotaW (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver (vP p).asIdeal] :
    ℚ_[p] →+* w.adicCompletion K :=
  (algebraMap ((vP p).adicCompletion ℚ) (w.adicCompletion K)).comp
    ((Padic.adicCompletionEquiv (𝓞 ℚ) ⟨p, hp.out⟩).toRingEquiv.toRingHom)

def phiW (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver (vP p).asIdeal] :
    ℚ_[p] ⊗[ℚ] K →ₐ[ℚ] w.adicCompletion K :=
  Algebra.TensorProduct.lift (iotaW p w).toRatAlgHom (algebraMap K (w.adicCompletion K)).toRatAlgHom
    (fun _ _ => Commute.all _ _)

@[simp] theorem phiW_tmul (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver (vP p).asIdeal]
    (s : ℚ_[p]) (x : K) : phiW p w (s ⊗ₜ x) = iotaW p w s * algebraMap K (w.adicCompletion K) x := by
  simp [phiW]

end Decomp
end GlobalTheory.LKTorus.KerOneLoc

namespace GlobalTheory.LKTorus.KerOneLoc
open GlobalTheory.LKTorus.KerOne GroundTheory.Global.SemiLocal

section Main

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L]

end Main
end GlobalTheory.LKTorus.KerOneLoc

namespace GlobalTheory.LKTorus.KerOneLoc
open GlobalTheory.LKTorus.KerOne GroundTheory.Global.SemiLocal

section Forward

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L]

variable (K) in

def psiW (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver (vP p).asIdeal] :
    ℚ_[p] ⊗[ℚ] L →ₐ[ℚ] w.adicCompletion K ⊗[K] L :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : w.adicCompletion K →ₐ[w.adicCompletion K]
      w.adicCompletion K ⊗[K] L).toRingHom.comp (iotaW p w)).toRatAlgHom)
    ((Algebra.TensorProduct.includeRight : L →ₐ[K] w.adicCompletion K ⊗[K] L).toRingHom.toRatAlgHom)
    (fun _ _ => Commute.all _ _)

end Forward
end GlobalTheory.LKTorus.KerOneLoc

namespace GlobalTheory.LKTorus.KerOneLoc
open GlobalTheory.LKTorus.KerOne GroundTheory.Global.SemiLocal

section Backward

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L]

end Backward
end GlobalTheory.LKTorus.KerOneLoc

namespace GlobalTheory.LKTorus.KerOneLoc

end GlobalTheory.LKTorus.KerOneLoc
