import Formalism.FockGram.FockGramProofs.FockHerm
import Formalism.FockGram.FockGramProofs.FockSesq
import Formalism.FockGram.FockGramProofs.FockPerm
import Formalism.FockGram.FockGramProofs.DetSymPow
import Formalism.FockGram.FockGramProofs.SubIndexNorm
import Mathlib
import Formalism.FockGram.FockGramProofs.CovolGram
import Formalism.FockGram.FockGramProofs.HermDualOf
import Formalism.FockGram.FockGramProofs.HermitianTensorMulHermitian
import Formalism.FockGram.StatementSymPos
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Positive

namespace Formalism.E

theorem fockHerm : FockHerm := fischerInnerConjSymm_holds

theorem subIndexNorm : SubIndexNorm := indexEqNormDet

theorem hermDual : HermDual := hermDual_of subIndexNorm

end Formalism.E
