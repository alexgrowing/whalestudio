import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterNorm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_hecke_character_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∃ (U : Subgroup (Neutral.B1.Ideles E)) (ψ : Neutral.B1.Ideles E →* ℂˣ), IsOpen (U : Set (Neutral.B1.Ideles E)) ∧
      Continuous ψ ∧ (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ (k : Eˣ) (b : Neutral.B1.Ideles (maximalRealSubfield E)) (u : Neutral.B1.Ideles E), u ∈ GlobalTheory.MuExist.nsUnits E →
        Neutral.B1.diagUnits E k * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b * u ∈ U →
        (GlobalTheory.GalOfCusp.quadChar E).1 b =
          ψ (Neutral.B1.diagUnits E k * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b * u) := by
  first | exact @GlobalTheory.ConsEta.exists_open_subgroup_eta_consistent | exact GlobalTheory.ConsEta.exists_open_subgroup_eta_consistent | (intros; apply GlobalTheory.ConsEta.exists_open_subgroup_eta_consistent <;> assumption)
