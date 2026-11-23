import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SymmetricCubeUnits.Sym3AutKOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcAtt0
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.WeakEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.NormQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SelfIso

namespace UpperTheory.V.Z.Bc

open UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

class Wide : Prop where
  up : UpAll

theorem wide_of_cyclic (hP : Hypotheses₂) (cyc : CyclicBaseChange) : Wide := ⟨by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hE n hn r hr ⟨π, hreg, hatt⟩ hirr
  obtain ⟨P, hBC⟩ := (Br.weakEx cyc F E hE n hn π).resolve_left fun ⟨η, hη, ht⟩ =>
    Bc.noTwist hP F E Ω l ι hE n r π hr hatt hirr η (Br.normQuad hP.litN.aut.art F E hE η hη)
      (Br.selfIso hP.smoR F n hn π η (hE ▸ hη.2.1) ht)
  have h := Br.bcAtt0 F E Ω l ι n r π P hBC
  exact ⟨P, h.1 hreg, h.2 hatt ((Bc.irrBasic.1 _ Unit _ n _).2.1 hirr)⟩⟩

theorem wide_of_quad (hP : Hypotheses₂) (hQ : QuadBaseChange) : Wide := ⟨by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hE n hn r hr ⟨π, hreg, hatt⟩ hirr
  obtain ⟨P, hBC⟩ := (hQ F E hE n hn π).resolve_left
    fun ⟨η, hη, ht⟩ => Bc.noTwist hP F E Ω l ι hE n r π hr hatt hirr η hη ht
  have h := Bc.bcAtt F E Ω l ι n r π P hBC
  exact ⟨P, h.1 hreg, h.2 hatt ((Bc.irrBasic.1 _ Unit _ n _).2.1 hirr)⟩⟩

theorem upQuadW [h : Wide] (_ : Hypotheses₂) : UpAll := h.up

end UpperTheory.V.Z.Bc
