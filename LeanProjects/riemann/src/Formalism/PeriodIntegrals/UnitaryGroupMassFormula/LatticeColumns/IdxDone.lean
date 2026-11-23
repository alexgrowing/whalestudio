import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.PrincipalCongruenceLeLevel

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

theorem global_index_eq_prod_local : IdxProdH := idxProdH_of level_components_surjective level_membership_local

def LocRedRest : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ p : TypX X,
      MassDataIdxSteps.StResZ X p ∧ HLatGL X u p ∧ HImU X hb u p

theorem locRedH_of_rest (h : LocRedRest) : LocRedH :=
  locRedH_of fun X hb hK u hT hL p =>
    ⟨(h X hb hK u hT hL p).1, (h X hb hK u hT hL p).2.1, hKerIn_of_levelSubgroupCharacter_of_normalized X hb hK hL u p, (h X hb hK u hT hL p).2.2⟩

theorem idxCountStep_of_rest (h : LocRedRest) : IdxCountStep :=
  idxCountStep_of global_index_eq_prod_local (locRedH_of_rest h)

end PIW.MassDataColumns
