import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUMulInfU
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSpaceDefiniteUnitaryInfinitePoints
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOfFinOrderOfCompactConjMemUnitaryRationalPointStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantLiftOfTrivial
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

open Matrix

namespace GlobalTheory.EllU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def finPart : UA E n →* UA E n where
  toFun g := ⟨finGL E n (GeneralLinearGroup.map (pFin E) g.1),
    GlobalTheory.DefU.ClassFin.finGL_mem_UA _ (GlobalTheory.DefU.ClassFin.cT_pFin g)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem finPart_mem (g : UA E n) : finPart g ∈ finU E n := pInf_finGL _

theorem finPart_of_finU {k : UA E n} (hk : k ∈ finU E n) : finPart k = k :=
  Subtype.ext (GlobalTheory.DefU.ClassFin.finGL_pFin ⟨k, hk⟩)

theorem finPart_of_infU {x : UA E n} (hx : x ∈ infU E n) : finPart x = 1 := by
  have h : GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
  refine Subtype.ext ?_
  change finGL E n (GeneralLinearGroup.map (pFin E) x.1) = 1
  rw [h, map_one]

theorem inv_finPart_mul_mem (g : UA E n) : (finPart g)⁻¹ * g ∈ infU E n := by
  change GeneralLinearGroup.map (pFin E) ((finPart g)⁻¹ * g).1 = 1
  have h : GeneralLinearGroup.map (pFin E) (finPart g).1 = GeneralLinearGroup.map (pFin E) g.1 := pFin_finGL _
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h, inv_mul_cancel]

theorem continuous_finPart : Continuous (finPart (E := E) (n := n)) := by
  have h1 : Continuous (GeneralLinearGroup.map (pFin E) : GA E n → GL (Fin n) (Af E)) :=
    Continuous.units_map _ (continuous_id.matrix_map continuous_snd)
  exact Continuous.subtype_mk (GlobalTheory.DefU.ClassFin.continuous_finGL.comp (h1.comp continuous_subtype_val)) _

end GlobalTheory.EllU
