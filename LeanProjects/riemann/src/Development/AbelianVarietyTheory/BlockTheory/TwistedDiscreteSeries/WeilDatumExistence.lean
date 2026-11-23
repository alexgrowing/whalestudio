import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def WeilDatumExists (D : D7) : Prop :=
  ∀ (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle),
    IsStdChar D ψ (-1) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank →
      ∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om

theorem weilDatumExists_iff (D : D7) :
    WeilDatumExists D ↔ ∀ (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle),
      ((∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om) ↔
        IsStdChar D ψ (-1) ∧ IsHeckeChar D χS ∧ IsHeckeChar D χT ∧ ResEta D χS S.rank ∧ ResEta D χT T.rank) := by
  constructor
  · intro h S T ψ χS χT
    constructor
    · rintro ⟨om, H⟩
      exact ⟨H.std, H.hecS, H.hecT, H.resS, H.resT⟩
    · rintro ⟨hψ, h1, h2, h3, h4⟩
      exact h S T ψ χS χT hψ h1 h2 h3 h4
  · intro h S T ψ χS χT hψ h1 h2 h3 h4
    exact (h S T ψ χS χT).2 ⟨hψ, h1, h2, h3, h4⟩

example (D : D7) : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := D.sp.cm.cmUnram

example (D : D7) : IsHeckeChar D (1 : (AE D)ˣ →* Circle) := ⟨continuous_const, fun _ => rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion

end
