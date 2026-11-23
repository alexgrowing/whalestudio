import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

namespace UpperTheory.Lit.Red

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def FirstIn (x : IrrGL k) (P : Set (IrrGL k)) : Prop :=
  ∀ (q : Fin 2 → IrrGL k) (hq : ∑ a, (q a).1 = x.1), (q 0).IsCusp → jm q hq x.rep ≠ 0 → q 0 ∈ P

def LastIn (x : IrrGL k) (P : Set (IrrGL k)) : Prop :=
  ∀ (q : Fin 2 → IrrGL k) (hq : ∑ a, (q a).1 = x.1), (q 1).IsCusp → jm q hq x.rep ≠ 0 → q 1 ∈ P

def SuppIn (x : IrrGL k) (P : Set (IrrGL k)) : Prop :=
  ∃ A : Multiset (IrrGL k), HasSupport x.rep A ∧ ∀ y ∈ A, y ∈ P

def Emb (x y z : IrrGL k) : Prop :=
  ∃ (hd : ∑ a, (![y, z] a).1 = x.1) (f : x.rep.IntertwiningMap (prodIrr ![y, z] hd)), Function.Injective f

def Occ (x y z : IrrGL k) : Prop :=
  ∃ hd : ∑ a, (![y, z] a).1 = x.1, jhMult x.rep (prodIrr ![y, z] hd) ≠ 0

def up (ρ : IrrGL k) : Set (IrrGL k) := {y | ∃ n : ℕ, y = ρ.nu (n : ℂ)}

end UpperTheory.Lit.Red

end
