import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExtremeSph

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.Pse

open PositivityTheory.Rg.BcB.N3

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def KInj {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} (T : π.IntertwiningMap σ) : Prop :=
  ∀ v ∈ fixed π (KO k (Fin n)), T v = 0 → v = 0

def GL2SphericalSwap : Prop := ∀ a b : ℂˣ, ‖(a : ℂ)‖ ≤ ‖(b : ℂ)‖ →
  ∃ T : (iP (k := k) ![a, b]).IntertwiningMap (iP (k := k) ![b, a]), KInj k T

def StageLift : Prop := ∀ (n : ℕ) (η : Fin n → ℂˣ) (i j : Fin n), j.val = i.val + 1 →
  (∃ T : (iP (k := k) ![η i, η j]).IntertwiningMap (iP (k := k) ![η j, η i]), KInj k T) →
  ∃ T : (iP (k := k) η).IntertwiningMap (iP (k := k) (η ∘ Equiv.swap i j)), KInj k T

def ExpSph : Prop := ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
  IsSmooth π → π.IsIrreducible → IsSpherical π → ∃ (η : Fin n → ℂˣ) (f : π.IntertwiningMap (iP (k := k) η)), f ≠ 0

def SatPerm : Prop := ∀ (n : ℕ) (ξ η : Fin n → ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible → IsSpherical π → IsSubquotient π (iP (k := k) ξ) →
  (∃ f : π.IntertwiningMap (iP (k := k) η), f ≠ 0) → ∃ σ : Equiv.Perm (Fin n), η = ξ ∘ σ

def Bubble : Prop := StageLift k → GL2SphericalSwap k → ∀ (n : ℕ) (ξ : Fin n → ℂˣ), Mono ξ → ∀ (σ : Equiv.Perm (Fin n)) (V : Type)
  [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), π.IsIrreducible → IsSpherical π →
  (∃ f : π.IntertwiningMap (iP (k := k) (ξ ∘ σ)), Function.Injective f) →
  ∃ f : π.IntertwiningMap (iP (k := k) ξ), Function.Injective f

end PositivityTheory.Rg.BcB.N3.Pse

end
