import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompactSpaceMaximalCompactUnitaryInfinite

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open GlobalTheory.CuspRep

namespace CompanionTheory.D.gk.Br.LIC

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem continuous_infGL [IsTotallyComplex E] : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) := ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map (corner (matN a (sInf E))) (continuous_const.add (continuous_id.matrix_map hs))

theorem continuous_finGL : Continuous (finGL E a) := by
  have hs : Continuous (sFin E) := (continuous_const.prodMk continuous_id :
    Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map (corner (matN a (sFin E))) (continuous_const.add (continuous_id.matrix_map hs))

omit [NumberField E] in

theorem continuous_toUnits_Kinf : Continuous fun k : Kinf E a => (Unitary.toUnits k : GL (Fin a) (Cinf E)) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩

theorem continuous_infGL_toUnits [IsTotallyComplex E] :
    Continuous fun k : Kinf E a => infGL E a (Unitary.toUnits k) :=
  continuous_infGL.comp continuous_toUnits_Kinf

end CompanionTheory.D.gk.Br.LIC
