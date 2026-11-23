import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedCompW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open GlobalTheory.TateUnr

noncomputable section

namespace GlobalTheory.TateUnr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem chr_eq_prod_val_zpow (ν : Chr F E) (v : Pl F)
    (hν : ∀ w ∈ aboveF (L := E) F v, UnrAt ν w) (l : idelesAt E (evFin F v)) :
    ((ν l.1 : Circle) : ℂ) = ∏ w : aboveF (L := E) F v, ((val ν w.1 ^ ordV v l w : ℂˣ) : ℂ) := by
  have hl : l.1 = GlobalTheory.Doubling.ideleAt F E v (GlobalTheory.Doubling.unitFin F E v l.1) := (ideleAt_unitFin l.2).symm
  have key : ∀ z : Circle, (z : ℂ) = ((Circle.toUnits z : ℂˣ) : ℂ) := fun _ => rfl
  rw [hl, GlobalTheory.LFun.ideleAt_eq_prod_locIdele, map_prod, key, map_prod, Units.coe_prod]
  rw [← Finset.univ_eq_attach]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : w.1.under (𝓞 F) = v := mem_aboveF.1 w.2
  have hb := valued_compW hw l
  have h := locChar_eq_val_zpow (hν w.1 w.2) hb
  have h2 : ((ν (locIdele F w.1 (Units.map (toCompl hw).toMonoidHom (GlobalTheory.Doubling.unitFin F E v l.1))) : Circle) : ℂ)
      = ((locChar ν w.1 (compW hw l) : ℂˣ) : ℂ) := rfl
  exact h2.trans (congrArg Units.val h)

end GlobalTheory.TateUnr

end
