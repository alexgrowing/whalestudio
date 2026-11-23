import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

variable {D : D7}

def FixRed (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd)
    (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E) : Prop :=
  ∀ kv : (Σ k : Fin 2, D.nd.PlG k), IsRedBasis X (D.naut.plGw kv.1 kv.2) (b kv) ∧ ∀ k ∈ X.B.I.Kset, ∀ i,
    X.B.I.fmat k *ᵥ incl X.B.I (b kv i) -
      ∑ j, (((((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) •
        incl X.B.I (b kv j) ∈ wLf X (D.naut.plGw kv.1 kv.2)

theorem goodAt_of_fixRed {X : HidaSetting D} {red : X.B.I.Gf → G0g D.nd}
    {b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E} (hf : FixRed X red b) :
    ∀ k ∈ X.B.I.Kset, GoodAt X k (red k) :=
  fun k hk kv => ⟨b kv, (hf kv).1, (hf kv).2 k hk⟩

end GlobalTheory.Mem.SRe

end
