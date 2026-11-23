import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SqChar
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.UCharOf
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SpBlkSurj
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.BlockP

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS.S7

theorem weyl : WeylStatement :=
  weyl_of (kCharGT_of (uChar_of sqChar)) blockComb

end ReciprocityTheory.ChartRestriction.TR.Weyl
