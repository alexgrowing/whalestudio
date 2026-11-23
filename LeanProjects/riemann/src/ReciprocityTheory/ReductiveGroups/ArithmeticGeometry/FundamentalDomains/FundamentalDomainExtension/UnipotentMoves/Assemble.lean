import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.TopOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.KatoNormRelationTamePrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.AprojEqZeroOfUz
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.HermLinApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.SDual
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.HermSmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.BotMulVecExt

namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem fd_unip_move_of (hm : SMajXZ E) : ShortVectorBound (E := E) → UnitaryComplementMove (E := E) →
    ReducedFrameDomainCovering (E := E) → IsotropicCoefficientSplitting (E := E) → NoShortVectorLowerBound (E := E) →
    UnitaryUnipotentMove (E := E) := fun h4 h2i h2ii h5 h6 =>
  top_of sEmb radius_pos_le_tenth kato_norm_relation_tame_prime final_numerical_inequalities epsilonZero_pos (sCmp_of hm) sMajFlag sFlagMap sGraph sSplit
    (sDelta_of sEmb sExt sDual h5 h6) h4 h2i h2ii

end UnipMove
