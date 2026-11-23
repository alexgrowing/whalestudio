import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrame

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

def FTrace : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (x : G.F), ((Algebra.trace ℚ G.F x : ℚ) : ℚ_[p]) = ∑ w, Algebra.trace ℚ_[p] (G.Fw w) (G.embW w x) +
    ∑ w, Algebra.trace ℚ_[p] (G.Fw w) (G.embW w (IsCMField.complexConj G.F x))

def FInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (x : G.F), (∀ w, ‖(G.embW w x : PadicAlgCl p)‖ ≤ 1 ∧ ‖(G.embW w (IsCMField.complexConj G.F x) : PadicAlgCl p)‖ ≤ 1) →
    ∃ (m : ℕ) (c : 𝓞 G.F), m.Coprime p ∧ (c : G.F) = m * x

def EmbAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (τ : G.F →+* PadicAlgCl p), ∃ (w : Fin G.m) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
    (∀ x, τ x = σ (G.emb w x)) ∨ ∀ x, τ x = σ (G.emb w (IsCMField.complexConj G.F x))

def FApprox : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (a b : ∀ w : Fin G.m, G.Fw w) (e : ℝ), 0 < e → ∃ x : G.F, ∀ w, ‖((G.embW w x - a w : G.Fw w) : PadicAlgCl p)‖ < e ∧
    ‖((G.embW w (IsCMField.complexConj G.F x) - b w : G.Fw w) : PadicAlgCl p)‖ < e

def TrDual : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (w : Fin G.m), ∃ d : G.Fw w, d ≠ 0 ∧ ∀ a : G.Fw w,
    (∀ z : G.Fw w, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] (G.Fw w) (a * z)‖ ≤ 1) ↔ ‖((a * d : G.Fw w) : PadicAlgCl p)‖ ≤ 1

def KpMem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g : Gp G), inclG G 1 g ∈ KHT p G.m G.n 1 G.Fw ↔ IntPt g

def LocLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (w : Fin G.m) (s : Finset (Fin G.n → G.Fw w)), Submodule.span (G.Fw w) (s : Set (Fin G.n → G.Fw w)) = ⊤ →
    ∃ g : GL (Fin G.n) (G.Fw w), ∀ z : Fin G.n → G.Fw w,
      (∀ i, ‖(((((g⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z) i : G.Fw w) : PadicAlgCl p)‖ ≤ 1) ↔
        ∃ a : (Fin G.n → G.Fw w) → G.Fw w, (∀ y, ‖(a y : PadicAlgCl p)‖ ≤ 1) ∧ z = ∑ y ∈ s, a y • y

def PFrameEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → ∀ β : G.Cˣ, sh G β = β → Nonempty (PFrame L β)

def PLatOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (M : AddSubgroup (VQ D)) (s : Finset (VQ D)) (k : ℕ), Submodule.span ℚ (s : Set (VQ D)) = ⊤ →
    (∀ c : D.O, ∀ x ∈ M, actQ D c x ∈ M) → (∀ (m : ℕ) x, m.Coprime p → m • x ∈ M → x ∈ M) → (∀ x ∈ s, p ^ k • x ∈ M) →
    (∀ x ∈ M, ∃ m : ℕ, m.Coprime p ∧ (m * p ^ k) • x ∈ AddSubgroup.closure (s : Set (VQ D))) → IsPLat D M

def MemDual : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∃ d : ∀ w : Fin G.m, G.Fw w, (∀ w, d w ≠ 0) ∧ ∀ a : Loc G,
    ((∀ z : Loc G, IntL z → ‖pairL a z‖ ≤ 1) ↔ IntL (fun w => d w • a w))

def PkLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β), D.m = 1 → ∀ g : Gp G, ∃ M : AddSubgroup (VQ D), (∀ x, x ∈ M ↔ A.Mem g x) ∧ IsPLat D M

def PkEquiv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β) (y : GlobalTheory.LKCx.grp G β) (g : Gp G) (x : VQ D), A.Mem (locC G (y : G.Cˣ × ℚˣ) * g) (actY L y x) ↔ A.Mem g x

def PkPerf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β) (g : Gp G) (s : ℚ), ‖(s : ℚ_[p]) * (g.1 : ℚ_[p])‖ = 1 → ∀ M : AddSubgroup (VQ D), (∀ x, x ∈ M ↔ A.Mem g x) → PerfAt L β s M

def PkInj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β) (g g' : Gp G), (∀ x, A.Mem g x ↔ A.Mem g' x) ↔ IntPt (g⁻¹ * g')

def PkOnto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β), D.m = 1 → ∀ (M : AddSubgroup (VQ D)) (s : ℚ), IsPLat D M → 0 < s → PerfAt L β s M → ∃ g : Gp G, ∀ x, x ∈ M ↔ A.Mem g x

def OOnto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → Function.Surjective (algebraMap (𝓞 D.F) D.O)

end UpperTheory.Gal.W2
