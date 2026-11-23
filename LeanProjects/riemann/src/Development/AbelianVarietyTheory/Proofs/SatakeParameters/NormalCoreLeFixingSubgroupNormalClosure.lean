import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.NormalClosureSolv

open Pointwise

variable {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω]

theorem algebraMap_mem_smul_iff (γ : Ω ≃ₐ[F] Ω) (A : ValuationSubring Ω) (c : F) :
    algebraMap F Ω c ∈ γ • A ↔ algebraMap F Ω c ∈ A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.commutes]

theorem isPlaceOver_smul' [NumberField F] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) (γ : Ω ≃ₐ[F] Ω) : IsPlaceOver (γ • A) v := by
  intro x
  rw [← h x, valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, algebraMap_mem_smul_iff,
    algebraMap_mem_smul_iff, map_inv₀]

end GlobalTheory.NormalClosureSolv
