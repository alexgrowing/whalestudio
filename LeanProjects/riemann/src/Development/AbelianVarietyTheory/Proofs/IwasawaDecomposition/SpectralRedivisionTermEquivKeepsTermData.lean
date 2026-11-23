import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ECure
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.FourParts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SRe

variable (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : RT Y u u')

set_option maxHeartbeats 4000000 in
theorem re_termIsId : Formalism.L2.SG.FourParts.termIsId t ↔ Formalism.L2.SG.FourParts.termIsId (eRT Z Y u u' t) := (by with_unfolding_all exact (Iff.rfl (a := Formalism.L2.SG.FourParts.termIsId t) :))

set_option maxHeartbeats 4000000 in
theorem re_termInS : Formalism.L2.SG.FourParts.termInS t ↔ Formalism.L2.SG.FourParts.termInS (eRT Z Y u u' t) := (by with_unfolding_all exact (Iff.rfl (a := Formalism.L2.SG.FourParts.termInS t) :))

set_option maxHeartbeats 4000000 in
theorem re_relevant : t.relevant ↔ (eRT Z Y u u' t).relevant := (by with_unfolding_all exact (Iff.rfl (a := t.relevant) :))

set_option maxHeartbeats 4000000 in
theorem re_FeqF : t.FeqF ↔ (eRT Z Y u u' t).FeqF := (by with_unfolding_all exact (Iff.rfl (a := t.FeqF) :))

set_option maxHeartbeats 4000000 in
theorem re_generic : t.generic ↔ (eRT Z Y u u' t).generic := (by with_unfolding_all exact (Iff.rfl (a := t.generic) :))

set_option maxHeartbeats 4000000 in
theorem re_G : t.G = (eRT Z Y u u' t).G := (by with_unfolding_all exact (Eq.refl t.G :))

set_option maxHeartbeats 4000000 in
theorem re_termBBne : ∀ p, Formalism.L2.SG.Saturated.termBBne t p ↔ Formalism.L2.SG.Saturated.termBBne (eRT Z Y u u' t) p := (by with_unfolding_all exact (fun p => Iff.rfl (a := Formalism.L2.SG.Saturated.termBBne t p) :))

set_option maxHeartbeats 4000000 in
theorem re_ptOf : Formalism.L2.SG.PairVal.ptOf t = Formalism.L2.SG.PairVal.ptOf (eRT Z Y u u' t) := (by with_unfolding_all exact (Eq.refl (Formalism.L2.SG.PairVal.ptOf t) :))

set_option maxHeartbeats 4000000 in
theorem re_massTerm : Formalism.L2.SG.PairVal.massTerm t = Formalism.L2.SG.PairVal.massTerm (eRT Z Y u u' t) := (by with_unfolding_all exact (Eq.refl (Formalism.L2.SG.PairVal.massTerm t) :))

set_option maxHeartbeats 4000000 in
theorem re_cTerm : Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t = Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) (reY Z Y).δ (reY Z Y).M) (eRT Z Y u u' t) := by
  kexactB Eq.refl (Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t)

omit t in
set_option maxHeartbeats 4000000 in
theorem re_meanCount : ∀ w, Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w = Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w := (by with_unfolding_all exact (fun w => Eq.refl (Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w) :))

omit t in
set_option maxHeartbeats 4000000 in

theorem eRT_keeps_term_data : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t : RT Y u u', (Formalism.L2.SG.FourParts.termIsId t ↔ Formalism.L2.SG.FourParts.termIsId (eRT Z Y u u' t)) ∧ (Formalism.L2.SG.FourParts.termInS t ↔ Formalism.L2.SG.FourParts.termInS (eRT Z Y u u' t)) ∧ (t.relevant ↔ (eRT Z Y u u' t).relevant) ∧ (t.FeqF ↔ (eRT Z Y u u' t).FeqF) ∧ (t.generic ↔ (eRT Z Y u u' t).generic) ∧ t.G = (eRT Z Y u u' t).G ∧ (∀ p, Formalism.L2.SG.Saturated.termBBne t p ↔ Formalism.L2.SG.Saturated.termBBne (eRT Z Y u u' t) p) ∧ Formalism.L2.SG.PairVal.ptOf t = Formalism.L2.SG.PairVal.ptOf (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.massTerm t = Formalism.L2.SG.PairVal.massTerm (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t = Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) (reY Z Y).δ (reY Z Y).M) (eRT Z Y u u' t)) ∧ ∀ w, Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w = Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w :=
  fun D Z X Y u u' => ⟨fun t => ⟨re_termIsId D Z X Y u u' t, re_termInS D Z X Y u u' t,
    re_relevant D Z X Y u u' t, re_FeqF D Z X Y u u' t, re_generic D Z X Y u u' t, re_G D Z X Y u u' t,
    re_termBBne D Z X Y u u' t, re_ptOf D Z X Y u u' t, re_massTerm D Z X Y u u' t,
    re_cTerm D Z X Y u u' t⟩, re_meanCount D Z X Y u u'⟩

end GlobalTheory.Mem.SRe
