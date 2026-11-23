import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormEmbeddingIntegerLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousExtensionAdicCompletion
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

namespace GlobalTheory.LadicInf

theorem exists_place (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (τ : E →+* Qbar l) :
    ∃ (u : HeightOneSpectrum (𝓞 E)) (j : u.adicCompletion E →+* Qbar l),
      ((l : ℕ) : 𝓞 E) ∈ u.asIdeal ∧ Continuous j ∧ j.comp (algebraMap E (u.adicCompletion E)) = τ := by
  obtain ⟨u, hu⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l τ
  obtain ⟨j, hj, hjE⟩ := GlobalTheory.exists_continuous_extension_adicCompletion E l τ u hu
  refine ⟨u, j, ?_, hj, hjE⟩
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
  have h1 : ‖τ ((((l : ℕ) : 𝓞 E)) : E)‖ < 1 := by
    have : τ ((((l : ℕ) : 𝓞 E)) : E) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this]
    have := PadicAlgCl.norm_extends (p := l) (l : ℚ_[l])
    rw [this]
    first | exact Padic.norm_p_lt_one | exact padicNormE.norm_p_lt_one
  have := (hu (((l : ℕ) : 𝓞 E) : E)).2 h1
  simpa using this

end GlobalTheory.LadicInf

namespace GlobalTheory.LadicInf

end GlobalTheory.LadicInf
