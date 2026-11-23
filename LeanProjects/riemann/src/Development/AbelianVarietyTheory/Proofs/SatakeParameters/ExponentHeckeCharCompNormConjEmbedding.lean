import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.PolarizedGaloisRepPublished
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyIdeleMapInfIdeleNegOne
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

namespace GlobalTheory.NormExpo

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem adeleMap_real_injective :
    Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap (maximalRealSubfield E) E) := by
  intro x y h
  rw [← GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap, ← GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap] at h
  have h2 := (GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (isCMExt_real E)).injective (a₁ := algebraMap _ _ x) (a₂ := algebraMap _ _ y) h
  exact Algebra.TensorProduct.includeLeft_injective (S := maximalRealSubfield E)
    (algebraMap (maximalRealSubfield E) E).injective h2

theorem conjAd_infId (u : (Cinf E)ˣ) :
    Units.map (GlobalTheory.UnitaryBC.conjAd E).toMonoidHom (infId E u) = infId E (Units.map (starRingEnd (Cinf E)).toMonoidHom u) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change infEq E (starRingEnd (Cinf E) ((infEq E).symm (1 - infEq E 1 + infEq E u))) =
      1 - infEq E 1 + infEq E (starRingEnd (Cinf E) u)
    simp
  · change conjFin _ ((1 : Af E) - 0 + 0) = (1 : Af E) - 0 + 0
    simp

theorem ideleNorm_infId_star (u : (Cinf E)ˣ) :
    ideleNorm E (infId E (Units.map (starRingEnd (Cinf E)).toMonoidHom u)) = ideleNorm E (infId E u) := by
  refine Units.ext (adeleMap_real_injective E ?_)
  refine congrArg Units.val (a₁ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E _) (a₂ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E _) ?_
  rw [ideleMap_ideleNorm, ideleMap_ideleNorm, GlobalTheory.PolChar.ideleConj_eq, GlobalTheory.PolChar.ideleConj_eq, conjAd_infId,
    conjAd_infId, mul_comm]
  congr 2
  exact Units.ext (star_star _)

theorem star_expU_atEmb (τ : E →+* ℂ) (z : ℂ) :
    Units.map (starRingEnd (Cinf E)).toMonoidHom (expU (atEmb τ z)) = expU (atEmb τ (starRingEnd ℂ z)) := by
  classical
  refine Units.ext (funext fun w => ?_)
  change starRingEnd ℂ (Complex.exp (atEmb τ z w)) = Complex.exp (atEmb τ (starRingEnd ℂ z) w)
  rw [← Complex.exp_conj]
  congr 1
  unfold atEmb
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw; split_ifs <;> simp
  · simp [Pi.single_eq_of_ne hw]

theorem expo_compNorm_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (χ : HChar (maximalRealSubfield E)) (τ : E →+* ℂ),
    expo (compNorm E χ) (ComplexEmbedding.conjugate τ) = expo (compNorm E χ) τ := by
  intro E _ _ _ χ τ
  refine (GlobalTheory.CuspRep.expo_eq_of_exp _ τ _ (expo (compNorm E χ) τ) fun z => ?_).symm
  have h : chiInf (compNorm E χ) (expU (atEmb τ z)) = chiInf (compNorm E χ) (expU (atEmb τ (starRingEnd ℂ z))) := by
    rw [← star_expU_atEmb]
    exact congrArg χ.1 (ideleNorm_infId_star E _).symm
  rw [h, chiInf_expU_atEmb, Complex.conj_conj, add_comm]

end GlobalTheory.NormExpo
