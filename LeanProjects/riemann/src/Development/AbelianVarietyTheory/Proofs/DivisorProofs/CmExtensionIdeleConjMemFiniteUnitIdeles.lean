import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupDivEqMulDivMulInvDiv
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjUnit

theorem ideleConj_mem_unitIdl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (y : Neutral.B1.Ideles E), y ∈ GlobalTheory.Mem.Chr.unitIdl E →
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y ∈ GlobalTheory.Mem.Chr.unitIdl E := by
  intro E _ _ _ y hy
  letI : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  have key : ∀ z : Neutral.B1.Ideles E, z ∈ GlobalTheory.Mem.Chr.unitIdl E → ∀ w : HeightOneSpectrum (𝓞 E),
      Valued.v (((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E z : AdeleRing (𝓞 E) E)).2 w) ≤ 1 := by
    intro z hz w
    have hz' : ∀ v : HeightOneSpectrum (𝓞 E), ((z : AdeleRing (𝓞 E) E)).2 v ∈ v.adicCompletionIntegers E :=
      fun v => (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := v)).mpr (hz v).le
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_mapsTo E E w (hz' _)
  intro w
  have h1 := key y hy w
  have h2 := key y⁻¹ (inv_mem hy) w
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y : AdeleRing (𝓞 E) E)).2 w *
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y⁻¹ : AdeleRing (𝓞 E) E)).2 w = 1 := by
    rw [map_inv]
    exact congrArg (fun a : AdeleRing (𝓞 E) E => a.2 w) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y).mul_inv
  have e' := congrArg Valued.v e
  rw [map_mul, map_one] at e'
  exact eq_one_of_one_le_mul_left h1 h2 e'.ge

end GlobalTheory.ConjUnit
