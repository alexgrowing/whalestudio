import Formalism.SmithDeterminants.StatementDVR

namespace Formalism.A

def L3of : Prop := RangePowGenerators → LengthQuotientBound

def FinalOf : Prop := SmithGen → LengthQuotientBound → TruncDet → TruncFinal

def HornOf : Prop := SatChain → GradedHorn

end Formalism.A
