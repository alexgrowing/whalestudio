import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.VolPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def VolPinGC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PrimeHyp D u (Tu D u') → ∀ (t : TT Y u u'),
    t.relevant → t.toTerm.generic → t.G ≠ 0 →
    ∀ w : Point D.host.E (D.R.rS + 1), t.toTerm.atPt w → ∀ μR : Measure X.B.I.Ginf, IsPinnedR t w μR →
    ∀ K : Set X.B.I.Ginf, MeasurableSet K →
      (∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ Formalism.L2.SG.TermOp.ROinf t ∧ s * r ∈ K) →
    ∀ (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D),
      Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U →
      (μR K).toReal = Formalism.L2.SG.PairVal.volIdx D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M t.toTerm w F' L

def VolumeOddGeneric : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ i, 3 ≤ D.host.g i) → PrimeHyp D u (Tu D u') →
    ∀ (t : TT Y u u'), t.relevant → t.toTerm.generic → t.G ≠ 0 →
    ∀ w : Point D.host.E (D.R.rS + 1), t.toTerm.atPt w → ∀ μR : Measure X.B.I.Ginf, IsPinnedR t w μR →
    ∀ K : Set X.B.I.Ginf, MeasurableSet K →
      (∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, ∃! s, s ∈ Formalism.L2.SG.TermOp.ROinf t ∧ s * r ∈ K) →
    ∀ (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D),
      Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U →
      (μR K).toReal = Formalism.L2.SG.PairVal.volIdx D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M t.toTerm w F' L

end Formalism.L2.SG.VolPin
