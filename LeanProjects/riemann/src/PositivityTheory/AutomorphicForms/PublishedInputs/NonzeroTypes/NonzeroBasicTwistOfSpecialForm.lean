import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CJDefs
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def SpecialLatticeProp : Prop :=
  ∀ (Γ V : Type) [Group Γ] [AddCommGroup V] [Module ℂ V] (I : Representation ℂ Γ V) (d : Subrepresentation I → ℕ),
    Monotone d → (∀ X Y, d (X ⊔ Y) + d (X ⊓ Y) = d X + d Y) → d ⊤ ≤ 1 →
    ∀ (A B : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
      (α : Representation ℂ Γ A) (β : Representation ℂ Γ B), α.IsIrreducible → β.IsIrreducible →
      (∃ X Y : Subrepresentation I, X ≤ Y ∧ d X < d Y ∧ Nonempty ((subQuot Y X).Equiv α)) →
      (∃ X Y : Subrepresentation I, X ≤ Y ∧ d X < d Y ∧ Nonempty ((subQuot Y X).Equiv β)) →
      Nonempty (α.Equiv β)

namespace Grp

variable {n : ℕ} (G : Grp k n)

def etaSp {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) W) :
    Submodule ℂ W :=
  ⨅ (m : Levi k fun a : Fin G.s => Fin (G.d a)) (_ : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))),
    LinearMap.ker (ρ m - G.eta m • LinearMap.id)

def SphericalVectorUniqueness : Prop :=
  SpecialLatticeProp →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (I : Representation ℂ (GL (Fin n) k) V), IsSmooth I →
    FiniteDimensional ℂ ↥(G.etaSp (jacU G.e I)) → Module.finrank ℂ ↥(G.etaSp (jacU G.e I)) ≤ 1 →
    ∀ (A B : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
      (α : Representation ℂ (GL (Fin n) k) A) (β : Representation ℂ (GL (Fin n) k) B),
      α.IsIrreducible → β.IsIrreducible → IsSubquotient α I → IsSubquotient β I →
      G.HasEtaVec (jacU G.e α) → G.HasEtaVec (jacU G.e β) → Nonempty (α.Equiv β)

def SpecialLiftProp : Prop :=
  ∀ (W X : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) W)
    (σ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) X),
    IsSmooth ρ → IsSubquotient σ ρ → G.HasEtaVec σ → G.HasEtaVec ρ

def SpecialCountProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ c : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (c i)) → (∀ i, res (c i) = res (G.chi i)) →
    FiniteDimensional ℂ ↥(G.etaSp (jacU G.e (prinSeries c))) ∧
      Module.finrank ℂ ↥(G.etaSp (jacU G.e (prinSeries c))) ≤ 1

def twD {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) (a : Fin G.s) :
    Representation ℂ (GL (Fin (G.d a)) k) (Y a) :=
  twist (τ a) (detChar (Fin (G.d a)) (absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))))

def cOf (ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ) (i : Fin n) : kˣ →* ℂˣ :=
  ν (G.e.symm i).1 (G.e.symm i).2 * absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) (G.e.symm i).1 : ℂ) / 2))

def NonzeroBasicTwistOfSpecialForm : Prop :=
  ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a))
    (a : Fin G.s), IsSmooth (τ a) → (τ a).IsIrreducible → HasDetVec (τ a) (G.μ a) →
    IsSmooth (G.twD τ a) ∧ (G.twD τ a).IsIrreducible ∧ HasDetVec (G.twD τ a) (G.μ a)

def SpecialRestrictionProp : Prop :=
  ∀ ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ, (∀ a j, res (ν a j) = res (G.μ a)) → ∀ i, res (G.cOf ν i) = res (G.chi i)

def SpecialRepresentationEtaProp : Prop :=
  G.SpecialLiftProp →
  ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
    (∀ a, IsSmooth (τ a)) → (∀ a, HasDetVec (τ a) (G.μ a)) →
    G.HasEtaVec (jacU G.e (multiProd G.e (G.twD τ)))

def SpecialOrderProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → ∀ c : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (c i)) →
    ∀ σ : Equiv.Perm (Fin n), IsSubquotient π (prinSeries (fun i => c (σ i))) → IsSubquotient π (prinSeries c)

def SpecialRepresentationSubProp : Prop :=
  SpecialOrderProp (k := k) (n := n) → GlobalTheory.Mem.LiteralAutomorphy.LitN →
  ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
    (∀ a, IsSmooth (τ a)) → (∀ a, (τ a).IsIrreducible) →
    ∀ ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ, (∀ a j, IsSmoothChar (ν a j)) →
    (∀ a, IsCuspSupport (τ a) (fun _ : Fin (G.d a) => 1) (fun j => detRep (Fin 1) (ν a j))) →
    (multiProd G.e (G.twD τ)).IsIrreducible →
    IsSubquotient (multiProd G.e (G.twD τ)) (prinSeries (G.cOf ν))

def SpecialSupportProp : Prop :=
  SpecialOrderProp (k := k) (n := n) → GlobalTheory.Mem.LiteralAutomorphy.LitN →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
    ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
      (∀ a, IsSmooth (τ a)) → (∀ a, (τ a).IsIrreducible) →
      ∀ ν : ∀ a, Fin (G.d a) → kˣ →* ℂˣ, (∀ a j, IsSmoothChar (ν a j)) →
      (∀ a, IsCuspSupport (τ a) (fun _ : Fin (G.d a) => 1) (fun j => detRep (Fin 1) (ν a j))) →
      IsSubquotient (piTensor τ) (jacU G.e π) → IsSubquotient π (prinSeries (G.cOf ν))

def NonzeroTopOfSpecialForm : Prop :=
  SpecialLatticeProp → G.SphericalVectorUniqueness → G.SpecialCountProp → G.SpecialLiftProp → G.NonzeroBasicTwistOfSpecialForm → G.SpecialRestrictionProp → G.SpecialRepresentationEtaProp →
    SpecialOrderProp (k := k) (n := n) → G.SpecialRepresentationSubProp → G.SpecialSupportProp → CuspidalSupportProp → ProductIrreducibleProp → TensorProductVectors →
    G.SupportOfProductProp

end Grp

end UpperTheory.TNZ
