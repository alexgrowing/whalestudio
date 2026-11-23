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

namespace GlobalTheory.GalReal

theorem ideleMap_ideleNorm_infId (E : Type) [Field E] [NumberField E] [IsCMField E] (u : (Cinf E)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (ideleNorm E (infId E u)) =
      infId E (u * Units.map (starRingEnd (Cinf E)).toMonoidHom u) := by
  have h1 : ∀ t : (Cinf E)ˣ, pInf E (infId E t).val = t.val := fun t => by
    change (infEq E).symm (1 - infEq E 1 + infEq E t.val) = _
    simp
  have h2 : ∀ t : (Cinf E)ˣ, pFin E (infId E t).val = 1 := fun t => by
    change (1 : Af E) - 0 + 0 = 1
    simp
  rw [GlobalTheory.GalOfCusp.ideleMap_ideleNorm, GlobalTheory.PolChar.ideleConj_eq, map_mul]
  congr 1
  refine Units.ext (ad_ext ?_ ?_)
  · change pInf E (GlobalTheory.UnitaryBC.conjAd E (infId E u).val) = _
    rw [GlobalTheory.ThetaPull.pInf_conjAd, h1, h1]
    rfl
  · change pFin E (GlobalTheory.UnitaryBC.conjAd E (infId E u).val) = _
    rw [GlobalTheory.ThetaPull.pFin_conjAd, h2, h2, map_one]

end GlobalTheory.GalReal
