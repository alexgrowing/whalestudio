import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.LocInteg

theorem kappa_mem_int {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (F : FinIso L n)
    (w : HeightOneSpectrum (𝓞 L)) {z : AL L} (hz : z ∈ ALint L) : F.κ z w ∈ w.adicCompletionIntegers L := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨y, rfl⟩ | ⟨a, ha, rfl⟩
    · rw [F.left]
      exact GlobalTheory.AdeleBaseChange.algebraMap_int_mem y w
    · have h := GlobalTheory.UnramDict.kappa_tmul F 1 a
      rw [map_one, one_mul] at h
      change F.κ.toRingHom _ w ∈ _
      rw [h]
      exact GlobalTheory.AdeleBaseChange.adMap_int ha w
  | one => rw [map_one]; exact one_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem cLoc_mem_KGL_iff : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (w : HeightOneSpectrum (𝓞 L)) (y : GAf L n), F.j y ∈ locU n w → (cLoc w (F.j y) ∈ GlobalTheory.LFun.KGL w n ↔ y ∈ Umax L n) := by
  intro L _ _ _ n F w y hy
  constructor
  · intro hK i j
    exact GlobalTheory.UnramDict.mem_ALint F _ fun u => by
      rw [← F.loc]
      exact GlobalTheory.UnramDict.cLoc_entry_mem hy hK u i j
  · intro hyU
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [F.loc]
      exact kappa_mem_int F w (hyU i j)
    · rw [← map_inv, ← map_inv, F.loc]
      exact kappa_mem_int F w ((inv_mem hyU : y⁻¹ ∈ Umax L n) i j)

end GlobalTheory.LocInteg

end
