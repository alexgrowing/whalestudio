import Formalism.LocalToGlobal.Columns.TwQRec

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl)

section QTop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}
  {H : Subgroup (GLG E n SG)}

def recClsFOf (hS : DecoPtSurj hc n ST SG) (hQ : QOff (F := F) ST SG Q) (q : QLoc hc n Q Θ) (hF : FrLat ST SG q)
    (hE : FrExists (n := n) ST SG Q) (s : DecoFCl (K := K) n ST SG Q H Θ → DecoF E n ST SG Q)
    (hs : ∀ c, (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q H Θ) = c) : RecClsF hc n ST SG Q H q s :=
  recClsF q (decoPtSurjF_of hS hQ q hF (qdf_lift q)) hF hE s hs

end QTop

end Formalism.L2.Col
