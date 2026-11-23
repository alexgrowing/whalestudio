import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantGLOfEquivariantUnitaryCoefficientSpacStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulBrStdOfEquivariantStatement

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.BrUnique

variable {ι : Type} [Fintype ι] {N n : ℕ}

def uGL (u : ι → Matrix.unitaryGroup (Fin n) ℂ) : ι → GL (Fin n) ℂ := fun τ => GlobalTheory.Branching.unitaryIncl n (u τ)

def diagU (hN : N = n + 1) (u : ι → Matrix.unitaryGroup (Fin n) ℂ) : ι → GL (Fin N) ℂ :=
  fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (GlobalTheory.Branching.unitaryIncl n (u τ))

theorem invTrK_invTrK {K : Type} [Field K] (g : ι → GL (Fin n) K) : invTrK (invTrK g) = g := by
  funext τ
  apply Units.ext
  have hu : IsUnit ((g τ : Matrix (Fin n) (Fin n) K)).det := (Matrix.isUnit_iff_isUnit_det _).1 (g τ).isUnit
  simp [invTrK, inside₂, Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hu]

theorem pairBK_rhoK (σ : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (x y : VV ℂ σ) :
    pairBK σ (rhoK σ g x) (rhoK σ (invTrK g) y) = pairBK σ x y := by
  rw [pairBK_apply, pairBK_apply, rhoK_coe, rhoK_coe]
  have h := pairingBInvariantK_holds ℂ ι n σ (invTrK g) x.1 y.1
  rwa [invTrK_invTrK] at h

theorem unitaryEquiv_eq_smul (hN : N = n + 1) (hn : 1 ≤ n) {Λ : ι → DomWeight N} {σ : ι → DomWeight n}
    (hI : ∀ τ, Br.Interlace hN (Λ τ) (σ τ)) (hS : ∀ τ, Br.SameShift (Λ τ) (σ τ)) (φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ)
    (hφ : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (diagU hN u) v) = rhoK σ (uGL u) (φ v)) :
    ∃ c : ℂ, φ = c • Br.brStd hN Λ σ :=
  GlobalTheory.T.exists_eq_smul_brStd_of_equivariant hN hn Λ σ hI hS φ (GlobalTheory.T.equivariant_GL_of_equivariant_unitary_coefficientSpace hN Λ σ φ hφ)

theorem brPair_unique (hN : N = n + 1) (hn : 1 ≤ n) {Λ : ι → DomWeight N} {σ : ι → DomWeight n}
    (hI : ∀ τ, Br.Interlace hN (Λ τ) (σ τ)) (hS : ∀ τ, Br.SameShift (Λ τ) (σ τ))
    (B : VV ℂ Λ →ₗ[ℂ] (VV ℂ fun τ => (σ τ).dual) →ₗ[ℂ] ℂ)
    (hB : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ) (f : VV ℂ fun τ => (σ τ).dual),
      B (rhoK Λ (diagU hN u) v) (rhoK (fun τ => (σ τ).dual) (uGL u) f) = B v f) :
    ∃ c : ℂ, B = c • GlobalTheory.FunObj.brPair σ hN Λ := by
  haveI : FiniteDimensional ℂ (VV ℂ σ) := Module.Finite.of_basis (bVV ℂ σ)
  have hnd := pairingBNondegenerate_holds ℂ ι n σ
  let φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ :=
    (LinearMap.BilinForm.toDual (pairBK σ) hnd).symm.toLinearMap ∘ₗ B.compl₂ (GlobalTheory.FunObj.funEquiv σ).toLinearMap
  have hp : ∀ v y, pairBK σ (φ v) y = B v (GlobalTheory.FunObj.funEquiv σ y) := fun v y => by
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.BilinForm.apply_toDual_symm_apply,
      LinearMap.compl₂_apply]
  have hinv : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) v F,
      B (rhoK Λ (diagU hN u) v) F = B v (rhoK (fun τ => (σ τ).dual) (uGL u)⁻¹ F) := fun u v F => by
    have h := hB u v (rhoK (fun τ => (σ τ).dual) (uGL u)⁻¹ F)
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  have hφ : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ),
      φ (rhoK Λ (diagU hN u) v) = rhoK σ (uGL u) (φ v) := fun u v => by
    refine sub_eq_zero.1 (hnd.1 _ fun y => ?_)
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero, hp, hinv]
    obtain ⟨y', rfl⟩ : ∃ y', y = rhoK σ (invTrK (uGL u)) y' :=
      ⟨rhoK σ (invTrK (uGL u))⁻¹ y, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]⟩
    rw [pairBK_rhoK, hp, GlobalTheory.FunObj.funEquiv_rhoK, ← Module.End.mul_apply, ← map_mul, invTrK_invTrK, inv_mul_cancel,
      map_one, Module.End.one_apply]
  obtain ⟨c, hc⟩ := unitaryEquiv_eq_smul hN hn hI hS φ hφ
  refine ⟨c, LinearMap.ext₂ fun v f => ?_⟩
  have e : f = GlobalTheory.FunObj.funEquiv σ (GlobalTheory.FunObj.covOf σ f) := by rw [GlobalTheory.BrRat.covOf_eq, LinearEquiv.apply_symm_apply]
  rw [e, ← hp, hc, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
    ← e]
  simp only [GlobalTheory.FunObj.brPair, LinearMap.compl₁₂_apply]

end GlobalTheory.BrUnique
