import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.IdCell

noncomputable section

namespace PI.FRS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.IdCell

def DualExists : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (m : ℕ) (u : Fin m → S.V),
    LinearIndependent E u → ∀ t : Fin m → E, ∃ v : S.V, ∀ k : Fin m, S.hT (u k) v = t k

def CoefAdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (F : FlagG S r T) (x y : S.V) (k : Fin r), x ∈ F.X → y ∈ F.X →
    F.coefX (x + y) k = F.coefX x k + F.coefX y k

def CoefSmul : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (F : FlagG S r T) (a : E) (x : S.V) (k : Fin r), x ∈ F.X →
    F.coefX (a • x) k = a * F.coefX x k

def CoefE : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (F : FlagG S r T) (j k : Fin r), F.coefX (F.e j) k = if j = k then 1 else 0

def CoefLow : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T : E)
    (F : FlagG S r T) (a : ℕ) (x : S.V) (k : Fin r), x ∈ F.Xa a → a ≤ k.val → F.coefX x k = 0

end PI.FRS
