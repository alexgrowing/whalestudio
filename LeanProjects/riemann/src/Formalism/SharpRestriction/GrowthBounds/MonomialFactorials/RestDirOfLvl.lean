import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SumFinrankLeOfIndep

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

variable {C0 CE1 CE2 : ℝ} {X : Formalism.MainNotions.flipOneThree.Inst}

theorem restDir_of_lvl (h : RestLvlDim C0 CE1 CE2 X) : RestDir C0 CE1 CE2 X :=
  restDir_of (restDirQ_of h (restSumSpan_proved C0 CE1 CE2 X)) (restDimBC_proved C0 CE1 CE2 X)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
