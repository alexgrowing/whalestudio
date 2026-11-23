import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Heights₂.Heights.LowerBoundFree

section Free

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W} (Hd : HodgeData D)

def corrW (U : ((Σ k, J k) → ℂ) → ℝ) (z : (Σ k, J k) → ℂ) : ℝ := phMu Hd z + U z / 2

variable {Hd} {M : XModel D} {w : ((Σ k, J k) → ℂ) → ℝ} (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w)

def PosU : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsSemipositiveH (mCoordIdeal D.y) (MUc Hd S' B p q t') ∧ NefOnFibres (mCoordIdeal D.y) (MUc Hd S' B p q t').a ∧
      AmpleOnGenericFibre (mCoordIdeal D.y) (MUc Hd S' B p q t')

def ConjU : Prop :=
  ∀ B p q : ℕ, 4 * D.f + 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    IsConjInvariantH (MUc Hd S' B p q t')

def HtU (Ch rd Lval : ℝ) : Prop :=
  ∀ B p q : ℕ, 4 * D.f * D.N ^ 2 ≤ B → 1 ≤ p → p ≤ q → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t' : ℝ, 0 < t' → t' ≤ t₀ →
    ∀ P : Ideal (MRing J), IsArithVar P 1 → mCoordIdeal D.y ≤ P →
      -(Ch * D.f * D.j' * abelian₂ B rd Lval) - (p : ℝ) / q * D.KA ≤ htMUc Hd S' B p q t' P

variable (Hd)

def meanOf (U : ((Σ k, J k) → ℂ) → ℝ) : ℝ :=
  ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu Hd) U / degMu Hd

def MeanU (U : ((Σ k, J k) → ℂ) → ℝ) (Cu rd Lval : ℝ) : Prop :=
  1 ≤ D.j' → 3 * D.j' + 1 ≤ D.N → ∀ B : ℕ, 4 * D.f * D.N ^ 2 ≤ B → meanOf Hd U ≤ Cu * D.f * D.j' * abelian₂ B rd Lval

def twW (B : ℕ) (x : ((Σ k, J k) → ℂ) → ℝ) (z : (Σ k, J k) → ℂ) : ℝ := x z + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z)

end Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {II : IntersectionSystem} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

def admitted (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} (Or : CptOrigin Y S₀ Dc Hd)
    (B₁ : ℕ) : Prop :=
  Top.IsGlobal Xo l c Y ∧ Or.Good ∧ (∀ r : ℕ, r ∈ S₀ ↔ r.Prime ∧ (r : ℤ) ∣ 2 * discr E * l.M') ∧
    S₀.card ≤ 4 * Dc.f * Dc.N ^ 2 ∧ 4 * Dc.f + 2 ≤ B₁ ∧ (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ S₀) ∧ Dc.j' ≤ Dc.j

def NineGeoU (Ch Cu : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
    (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
    (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ)
    (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)),
    IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → Or.𝔐.IsCuspWeight Or.sm U → S'.IsTied →
      PosU S' ∧ HtU S' Ch (hostRd E) (hostLval H) ∧ MeanU Hd U Cu (hostRd E) (hostLval H)

end GlobalTheory.CompanionTheory.Ar.Cusp
