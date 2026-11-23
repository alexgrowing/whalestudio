import Formalism.SharpRestriction.Divisibility.WeightFamilies

namespace Formalism.L2.Geo.Rec

open Formalism.BasicNotions

def IntersectionBoundStatement : Prop :=
  ∀ (D : D7) (X : Formalism.MainNotions.WeightFamilies.Prov D) (CR : ℝ), Formalism.MainNotions.WeightFamilies.TransferenceBound X CR

def SecondBoundForAllData : Prop :=
  ∀ (D : D7) (X : Formalism.MainNotions.WeightFamilies.Prov D) (CR : ℝ), Formalism.MainNotions.WeightFamilies.Conclusion2 X CR

def TransferenceGivesSecondBound : Prop := IntersectionBoundStatement → SecondBoundForAllData

end Formalism.L2.Geo.Rec
