import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix

namespace GlobalTheory.RatPtsBridge

theorem exists_ratGL : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γQ : GQ L n), ∃ (γ : UA L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ ∧ (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
  intro L _ _ _ n γQ
  obtain ⟨γ₀, hγ₀, he⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γQ.2)
  have h0 : (γ₀ : Matrix (Fin n) (Fin n) L) * conjT (IsCMField.complexConj L : L →+* L) γ₀ = 1 := hγ₀
  have h1 : conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L) *
      (γ₀ : Matrix (Fin n) (Fin n) L) = 1 := mul_eq_one_comm.1 h0
  have hmem : ratGL L n γ₀ ∈ UA L n := by
    show Formalism.UG.cT (conjAd L) ((ratGL L n γ₀ : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) * 1 *
      ((ratGL L n γ₀ : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) = 1
    have e : Formalism.UG.cT (conjAd L) ((γ₀ : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L))) =
        (conjT (IsCMField.complexConj L : L →+* L) (γ₀ : Matrix (Fin n) (Fin n) L)).map (algebraMap L (Ad L)) := by
      ext i j
      simp [Formalism.UG.cT, conjT, conjAd_algebraMap]
    change Formalism.UG.cT (conjAd L) ((γ₀ : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L))) * 1 *
      (γ₀ : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L)) = 1
    rw [mul_one, e, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨ratGL L n γ₀, hmem⟩, γ₀, rfl, ?_⟩
  rw [← he]
  rfl

end GlobalTheory.RatPtsBridge
