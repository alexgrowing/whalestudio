import Formalism.CharacterColumnKernels.StatementN

open Finset Classical Polynomial

noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

universe u v w

open Formalism.NG

section Det

variable {O K X G : Type*} [CommRing O] [CommRing K] [Algebra O K] [Monoid G]
  {n : Type} [Fintype n] [DecidableEq n]

def tSpan (T : Subalgebra O (X → O)) (r : G →* (X → Matrix n n K)) : Set (X → Matrix n n K) :=
  {F | ∃ (s : Finset G) (c : G → X → O), (∀ g, c g ∈ T) ∧
    F = ∑ g ∈ s, fun x => algebraMap O K (c g x) • r g x}

def FromT (T : Subalgebra O (X → O)) (f : X → K) : Prop :=
  ∃ t ∈ T, ∀ x, algebraMap O K (t x) = f x

end Det

def LemmaDetPoly : Prop :=
  ∀ (O K X G : Type*) [CommRing O] [CommRing K] [Algebra O K] [Monoid G]
    (n : Type) [Fintype n] [DecidableEq n] (T : Subalgebra O (X → O))
    (r : G →* (X → Matrix n n K)),
    (∀ (g : G) (k : ℕ), FromT T (fun x => (Matrix.charpolyRev (r g x)).coeff k)) →
    ∀ (m : ℕ) (a : Fin m → X → Matrix n n K), (∀ i, a i ∈ tSpan T r) →
    ∀ s : Fin m →₀ ℕ, FromT T (fun x => MvPolynomial.coeff s
      (Matrix.det (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) K) • (a i x).map MvPolynomial.C)))

def LemmaDetSub : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] (X' G : Type*) [Monoid G] (T' : Subalgebra O (X' → O))
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (r : G →* (X' → Matrix d d (FractionRing O))),
    (∀ (g : G) (k : ℕ), FromT T' (fun x => (Matrix.charpolyRev (r g x)).coeff k)) →
    (∀ a ∈ R', a ∈ tSpan T' r) →
    ∀ (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R'), ∃ f ∈ T', ∀ x',
      algebraMap O (FractionRing O) (f x') =
        (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det

def BridgeDet : Prop :=
  LemmaDetPoly.{u, u, v, w} → StatBlockDet.{u, v} → LemmaDetSub.{u, v, w}

def DelSum : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (s₀ t : ℕ),
    ∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat l i) ≤ t * s₀ + padicValNat l t.factorial

def PropEta : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type*) [Finite X]
    (T : Subalgebra O (X → O)) [IsLocalRing T], (∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) →
    ∀ (V : Type*) [AddCommGroup V] [Module (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
      [Module O V] [IsScalarTower O (FractionRing O) V]
      (act : T →+* Module.End (FractionRing O) V), (⨆ x, Vx T act x) = ⊤ →
    ∀ L : Submodule O V, L.FG → Submodule.span (FractionRing O) (L : Set V) = ⊤ →
      (∀ f : T, ∀ v ∈ L, act f v ∈ L) →
    ∀ (Z Zg : Finset X), Zg ⊆ Z → ∀ (a : Module.End (FractionRing O) V) (A : ℤ),
      (∀ v ∈ L, a v ∈ L) → (∀ f : T, a * act f = act f * a) →
      (∀ x ∈ Zg, ∀ v ∈ Vx T act x, a v = (A : FractionRing O) • v) →
      (∀ x ∈ Z, x ∉ Zg → ∀ v ∈ Vx T act x, a v = 0) →
      ∃ h : IsCompl (VS T act (Zg : Set X)) (VS T act (Zg : Set X)ᶜ),
        let p : V →ₗ[O] V :=
          (((VS T act (Zg : Set X)).subtype).comp
            (Submodule.projectionOnto _ _ h)).restrictScalars O
        let up : Submodule O V := L.map p
        let low : Submodule O V := (VS T act (Zg : Set X)).restrictScalars O ⊓ L
        low ≤ up ∧
        Module.length O (up ⧸ low.comap up.subtype) ≤
          ∑ x ∈ Zg, (Module.finrank (FractionRing O) (Vx T act x) : ℕ∞) *
            (vcc T (Z : Set X) x + IsDiscreteValuationRing.addVal O (A : O))

def BridgeEta : Prop := StatCongBoundGood.{u, v, w} → PropEta.{u, v, w}

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
