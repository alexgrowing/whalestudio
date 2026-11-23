import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.VIOS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7) (u u' : D.what₂.Word)

variable (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def VolOrbit : Prop :=
  ∀ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → ∃ wt : MatR D → ℝ, ∀ (t : Term D u u' F0 what₂)
      (w : Point D.host.E (D.R.rS + 1)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D),
      t.relevant → t.generic → NormRep t w F' L U →
        vRdef D u u' F0 what₂ δ M t = ((orbT D u u' F0 what₂ t (ZhatL (lf D F0) F')).ncard : ℝ) * wt (ZhatL (lf D F0) F')

def VolumeOrbitNonzero : Prop :=
  ∀ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → ∃ wt : MatR D → ℝ, ∀ (t : Term D u u' F0 what₂)
      (w : Point D.host.E (D.R.rS + 1)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D),
      t.relevant → t.generic → NormRep t w F' L U → Formalism.MainNotions.S.Lat.Gval (lf D F0) F' ≠ 0 →
        vRdef D u u' F0 what₂ δ M t = ((orbT D u u' F0 what₂ t (ZhatL (lf D F0) F')).ncard : ℝ) * wt (ZhatL (lf D F0) F')

end Formalism.L2.SG.Pf.VIOS
