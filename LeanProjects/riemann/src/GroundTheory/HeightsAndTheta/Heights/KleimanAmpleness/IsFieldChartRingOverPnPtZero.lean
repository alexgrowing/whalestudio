import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver cechHc quotPart)

def CechPointVanish.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω),
    (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → IsField (chartRingOver F y c)) →
    ∀ β : K → ℤ, Subsingleton (cechHc ι (quotPart F (mIdealOver F y)) β 1)

theorem isField_chartRingOver_pnPt_zero (F : Type) [Field F] (c : ∀ k, IndefiniteRowSideFullHecke.Kleiman2.pnIdx 0 k) :
    IsField (chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 0) c) := by
  have hbot : chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 0) c = ⊥ := by
    refine eq_bot_iff.mpr (Algebra.adjoin_le ?_)
    rintro _ ⟨⟨u, i⟩, rfl⟩
    have hi : c u = i := Fin.ext (by omega)
    simp only [hi]
    rw [div_self (IndefiniteRowSideFullHecke.Kleiman2.pnPt_ne_zero F 0 _)]
    exact one_mem _
  rw [hbot]
  exact (Algebra.botEquiv F (IndefiniteRowSideFullHecke.Kleiman2.pnField F 0)).toMulEquiv.isField (Field.toIsField F)

example (F : Type) [Field F] (h : CechPointVanish.Statement) :=
  h F Unit (IndefiniteRowSideFullHecke.Kleiman2.pnIdx 0) (IndefiniteRowSideFullHecke.Kleiman2.pnField F 0) (IndefiniteRowSideFullHecke.Kleiman2.pnPt F 0)
    (fun c _ => isField_chartRingOver_pnPt_zero F c) 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
