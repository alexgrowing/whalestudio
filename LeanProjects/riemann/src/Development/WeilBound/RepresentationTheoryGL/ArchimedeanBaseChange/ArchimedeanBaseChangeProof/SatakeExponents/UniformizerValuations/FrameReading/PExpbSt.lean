import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail.BS

def hkS {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (f : G → ℂ) (v : V) : V :=
  ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v

def SplitT : Prop :=
  ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (K : Subgroup G) (L : Subgroup H)
    (X Y : Type) (f : X → G → ℂ) (g : Y → H → ℂ) (α : X → ℂ) (β : Y → ℂ) (v : V ⊗[ℂ] W),
    Nonempty X → Nonempty Y → (∀ x, α x ≠ 0) → (∀ y, β y ≠ 0) →
    (∀ x, {q : G ⧸ K | f x q.out ≠ 0}.Finite) → (∀ y, {q : H ⧸ L | g y q.out ≠ 0}.Finite) →
    (∀ x a k, k ∈ K → f x (a * k) = f x a) → (∀ y b l, l ∈ L → g y (b * l) = g y b) →
    v ∈ fixed (extTensor ρ σ) (K.prod L) → v ≠ 0 →
    (∀ x y, hkS (extTensor ρ σ) (K.prod L) (fun m => f x m.1 * g y m.2) v = (α x * β y) • v) →
    (∃ u ∈ fixed ρ K, u ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ ∀ x, hkS ρ K (f x) u = (c * α x) • u) ∧
    (∃ u ∈ fixed σ L, u ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ ∀ y, hkS σ L (g y) u = (c * β y) • u)

def DcosFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (t : GLw n w),
    {q : GLw n w ⧸ iwGL n w | dcos n w t q.out ≠ 0}.Finite ∧
      ∀ a k, k ∈ iwGL n w → dcos n w t (a * k) = dcos n w t a

def SubqEig : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    IsSmooth ρ → HasFiniteLength ρ → ∀ (K : Subgroup G) (X : Type) (f : X → G → ℂ) (γ : X → ℂ) (u : V),
    u ∈ fixed ρ K → u ≠ 0 → (∀ x, {q : G ⧸ K | f x q.out ≠ 0}.Finite) → (∀ x, hkS ρ K (f x) u = γ x • u) →
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ G W), IsSmooth τ ∧ τ.IsIrreducible ∧
      IsSubquotient τ ρ ∧ ∃ u' ∈ fixed τ K, u' ≠ 0 ∧ ∀ x, hkS τ K (f x) u' = γ x • u'

def JacHk : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π →
    ∀ (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x → ∀ u ∈ fixed π (iwahori k (Fin n)),
      (Submodule.Quotient.mk (hkS π (iwahori k (Fin n))
          (fun g => if ∃ a ∈ iwahori k (Fin n), ∃ b ∈ iwahori k (Fin n),
            g = a * diagT k (Fin n) (fun i => ϖ ^ x i) * b then (1 : ℂ) else 0) u) :
        Jacquet π (unipB k (Fin n))) =
      ((Nat.card 𝓀[k] : ℂ) ^ (∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i)) •
        jacBU π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u)

def JacEig : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GLw n w) V), IsSmooth π →
    ∀ (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 → ∀ (ξ : Fin n → ℂˣ) (c : ℂ) (x : Fin n → ℤ),
    StrictAnti x → ∀ u ∈ fixed π (iwGL n w),
      hkS π (iwGL n w) (dcos n w (tdiag ϖ x)) u =
        (c * (qh w ^ (∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i) * pw ξ x)) • u →
      jacB π (fun i => ϖ ^ x i) (Submodule.Quotient.mk u) =
        (c * pw ξ x) • (Submodule.Quotient.mk u : Jacquet π (unipB (w.adicCompletion E) (Fin n)))

def JacquetIwahoriTorusFixed : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    ∀ u ∈ fixed π (iwahori k (Fin n)), ∀ t ∈ torusO k (Fin n),
      jacB π t (Submodule.Quotient.mk u) = (Submodule.Quotient.mk u : Jacquet π (unipB k (Fin n)))

def ExtChar : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (M : Type) [AddCommGroup M] [Module ℂ M] (R : Representation ℂ (Fin n → kˣ) M) (z : M) (ϖ : kˣ)
    (ξ : Fin n → ℂˣ) (c : ℂ), z ≠ 0 → ord k ϖ = 1 → (∀ t ∈ torusO k (Fin n), R t z = z) →
    (∀ x : Fin n → ℤ, StrictAnti x → R (fun i => ϖ ^ x i) z = (c * pw ξ x) • z) →
    ∀ t, R t z = (torusChar (fun i => unrChar k (ξ i)) t : ℂ) • z

def JacFG : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → π.IsIrreducible →
    ∃ Z : Finset (Jacquet π (unipB k (Fin n))), Submodule.span ℂ {m | ∃ t, ∃ z ∈ Z, m = jacB π t z} = ⊤

def QuotChar : Prop :=
  ∀ (A : Type) [CommGroup A] (M : Type) [AddCommGroup M] [Module ℂ M] (R : Representation ℂ A M) (Z : Finset M),
    Submodule.span ℂ {m | ∃ a, ∃ z ∈ Z, m = R a z} = ⊤ → ∀ (χ : A →* ℂˣ) (z : M), z ≠ 0 →
    (∀ a, R a z = (χ a : ℂ) • z) → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ ≠ 0 ∧ ∀ a m, ℓ (R a m) = (χ a : ℂ) * ℓ m

end PositivityTheory.Rg.BcB.F.Tail.BS

end
