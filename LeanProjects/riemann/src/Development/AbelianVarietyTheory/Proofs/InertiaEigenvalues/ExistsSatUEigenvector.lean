import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeSatakeEigen

theorem exists_satU_eigenvector : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : (Formalism.UG.GU σ n → ℂ) → Module.End ℂ V), (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (h₁ + h₂) = T h₁ + T h₂) → (∀ (c : ℂ), ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (c • h) = c • T h) → T (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) 1) = 1 → (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (Formalism.UG.conv (Formalism.UG.KU σ n) h₁ h₂) = T h₁ * T h₂) → ∀ x₀ : V, x₀ ≠ 0 → ∃ α : Fin (n / 2) → ℂ, ∃ x : V, x ≠ 0 ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T h x = Formalism.UG.SatU ϖ q h α • x := by
  intro K _ _ _ ϖ σ q n hU V _ _ _ T hadd hsmul h1 hmul x₀ hx₀
  haveI : Nontrivial V := ⟨⟨x₀, 0, hx₀⟩⟩
  have hcomm : ∀ a b : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T a.1 * T b.1 = T b.1 * T a.1 := by
    intro a b
    rw [← hmul _ a.2 _ b.2, ← hmul _ b.2 _ a.2, GlobalTheory.UnitarySwap.heckeCommU K ϖ σ q n ℂ hU _ a.2 _ b.2]
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.exists_common_eigenvector_of_commute
    (fun b : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) => T b.1) hcomm
  choose c hc using hx
  have hinj : Function.Injective fun a : ℂ => a • x := smul_left_injective ℂ hx0
  let l : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) →ₗ[ℂ] ℂ :=
    { toFun := c
      map_add' := fun a b => hinj (by
        show c (a + b) • x = (c a + c b) • x
        rw [← hc, add_smul, ← hc, ← hc]
        show T (a.1 + b.1) x = _
        rw [hadd _ a.2 _ b.2]; rfl)
      map_smul' := fun r a => hinj (by
        show c (r • a) • x = (r * c a) • x
        rw [← hc, mul_smul, ← hc]
        show T (r • a.1) x = _
        rw [hsmul r _ a.2]; rfl) }
  have hl1 : l ⟨_, Formalism.UG.Final.DosetIndMem _ _ ℂ 1⟩ = 1 := hinj (by
    show c _ • x = (1 : ℂ) • x
    rw [← hc, one_smul]
    show T (Formalism.UG.dosetInd ℂ _ 1) x = x
    rw [h1]; rfl)
  have hlm : ∀ f f' : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n),
      l ⟨_, Formalism.UG.Final.HeckeConvMem _ _ ℂ (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n) _ f.2 _ f'.2⟩ = l f * l f' :=
    fun f f' => hinj (by
      show c _ • x = (c f * c f') • x
      rw [← hc]
      show T (Formalism.UG.conv _ f.1 f'.1) x = _
      rw [hmul _ f.2 _ f'.2, Module.End.mul_apply, hc f', map_smul, hc f, smul_smul, mul_comm])
  obtain ⟨α, hα⟩ := GlobalTheory.LFun.SatCompare.exists_satU_eq hU l hl1 hlm
  refine ⟨fun i => (α i : ℂ), x, hx0, fun h hh => ?_⟩
  rw [hc ⟨h, hh⟩]
  congr 1
  exact hα ⟨h, hh⟩

end GlobalTheory.HeckeSatakeEigen
