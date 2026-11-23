import Mathlib
import CompanionTheory.EightfoldTheory.VariationTheory.PublishedTheorems.ImportsAlt
import CompanionTheory.EightfoldTheory.VariationTheory.SelfDualForms.SelfDualWeylChambers.Imports

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace GlobalTheory.TfJl

def JacquetLanglandsQuaternion : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Q : DefQuat F) (lam : InfinitePlace F → DomWeight 2)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (InfinitePlace F → GL (Fin 2) ℂ) V), IsOuter lam ρ →
    (∀ v, (lam v).w 1 < (lam v).w 0) → ∀ τ : SmIrr (GL (Fin 2) (Af F)),
      (Q.Occurs ρ τ ↔ ∃ π : TR.CuspSub F 2, π.IsFinComp τ ∧ ∀ v, π.HasInfChar v ((GlobalTheory.UnitaryBC.infOfWeight (lam v)).map Neg.neg))

def TransferToDefiniteQuaternion : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (D : LDat F ι) (Q : DefQuat F), D.Cmp Q →
    ∀ (n : InfinitePlace F → ℕ) (e : InfinitePlace F → ℤ), (∀ v, n v ≠ 0) → ∀ (π : TR.CuspSub F 2), π.IsRegAlg →
    (∀ v, π.HasInfChar v (infOf ![-e v, -e v - n v - 1])) → ∀ (c : Pl F → ℕ) (ω : (Af F)ˣ →* ℂˣ) (x : π.V) (mu : Pl F → ℂ), x ≠ 0 →
    (∀ w, x ∈ Hi.fixd (π.locRep w) (K1 w (c w)) ∧ Uop w (π.locRep w) (c w) x = mu w • x) → (∀ z, π.finPart (zc F z) x = (ω z : ℂ) • x) →
    ∃ f ∈ Sp Q (D.R n e) c ω, f ≠ 0 ∧ ∀ w, Hk (Wt n) w (c w) f = mu w • f

def NarrowJL3 : Prop := TransferToDefiniteQuaternion ∧ FromD

end GlobalTheory.TfJl
