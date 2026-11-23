import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u u' : D.what₂.Word)

variable (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def VolIdxRep : Prop :=
  ∀ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
      (F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L₁ U₁ L₂ U₂ : MatR D),
      t.relevant → t.generic → NormRep t w F₁ L₁ U₁ → NormRep t w F₂ L₂ U₂ →
        volIdx D u u' F0 what₂ δ M t w F₁ L₁ = volIdx D u u' F0 what₂ δ M t w F₂ L₂

def VolumeIndexRepresentationNonzero : Prop :=
  ∀ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
      (F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L₁ U₁ L₂ U₂ : MatR D),
      t.relevant → t.generic → NormRep t w F₁ L₁ U₁ → Formalism.MainNotions.S.Lat.Gval (lf D F0) F₁ ≠ 0 → NormRep t w F₂ L₂ U₂ → Formalism.MainNotions.S.Lat.Gval (lf D F0) F₂ ≠ 0 →
        volIdx D u u' F0 what₂ δ M t w F₁ L₁ = volIdx D u u' F0 what₂ δ M t w F₂ L₂

end Formalism.L2.SG.Pf.RelativeIndexFlags
