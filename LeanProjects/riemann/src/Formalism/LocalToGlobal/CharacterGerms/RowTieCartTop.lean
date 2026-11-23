import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd

namespace Formalism.L2.FormalSeriesBounds

def GermIAllSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd), GermISt Y

theorem cartesian_of_germs (hPT : PTFBSt) (hG : GermIAllSt) (hStab : HStabFBSt) : CartFBSt :=
  cartFB_of hPT (addCvFB_of hG) hStab

end Formalism.L2.FormalSeriesBounds
