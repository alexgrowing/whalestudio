import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def ColsDimStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized →
    (Module.finrank ℂ (Formalism.L2.SG.PoincareInHH.PoincareSetting.Cu X u hK) : ℝ) =
      (Module.finrank ℂ (X.Vpi u) : ℝ) * (covol (X.measW u).μH /
        ((X.muH u Set.univ).toReal * ((X.measW u).μHf (Subtype.val ⁻¹' K2u X hb u)).toReal))

def ColsIdxStep : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized →
    ((X.measW u).μHf (Subtype.val ⁻¹'
        (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
          Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal /
      ((X.measW u).μHf (Subtype.val ⁻¹' K2u X hb u)).toReal =
    ∏ p : TypX X, ((glkC D.R.k (gOf p) : ℝ) / (ukC D.R.k (gOf p) : ℝ))

theorem massDataColumns_of (h1 : ColsDimStep) (h2 : ColsIdxStep) :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X))
      (A : AnIn), InColumnsAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hH
  exact And.intro (h1 X hb hK u hH.1 hH.2.1)
    (And.intro (h2 X hb hK u hH.1 hH.2.1)
      (And.intro (h1 X hb hK u' hH.1 hH.2.1) (h2 X hb hK u' hH.1 hH.2.1)))

end PIW.MassDataColumns
