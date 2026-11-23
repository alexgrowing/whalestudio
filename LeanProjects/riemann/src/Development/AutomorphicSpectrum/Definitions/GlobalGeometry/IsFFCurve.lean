import Mathlib
import GroundTheory.FunctionField.DivisorDegree
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Top

def IsFFCurve (k : Type) {K : Type} [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K]
    (C : ACurve K) : Prop :=
  ∃ e : C.I ≃ GroundTheory.FunctionField.Place k K, ∀ i, C.v i = (e i).valuation ∧ C.w i = (e i).deg

def segre {B Ω : Type} [Fintype B] [CommRing Ω] {J : B → Type} (y : (Σ k, J k) → Ω) : ((k : B) → J k) → Ω :=
  fun c => ∏ k, y ⟨k, c k⟩

structure DRTie {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (j p : ℕ) {E : Type} [Field E] [NumberField E]
    [IsCMField E] (H : Host E) where

  X : Scheme.{0}

  ξ : Spec (CommRingCat.of M.Ω) ⟶ X
  tie : CoordTie ℤ ξ (segre M.y)

  t : SAB H X
  pow : PowFns t
  fib : ∀ q : Cpt ξ, InFibre ξ p q → FibPF t q.1

  V : Type
  [acg : AddCommGroup V]
  [mod : Module M.Ω V]

  L : LieModel t.G ξ V

  r : 𝓞 E →+* Module.End M.Ω V
  act : L.IsActOf t.act.act r

  σ : Ψ ⊕ Ψ → (𝓞 E →+* M.Ω)
  σ_inj : Function.Injective σ
  card : 2 * Fintype.card Ψ = Module.finrank ℚ E
  conj : ∀ τ a, σ (Sum.inr τ) a = σ (Sum.inl τ) (H.bar a)
  reg : ∀ q : Cpt ξ, InFibre ξ p q → ∀ s a, σ s a ∈ regAt ξ q
  unram : ¬ (p : ℤ) ∣ NumberField.discr E

  b₁ : Ψ → Fin j → V

  b₂ : Ψ → Fin (N - j) → V
  ind₁ : ∀ τ, LinearIndependent M.Ω (b₁ τ) ∧ Submodule.span M.Ω (Set.range (b₁ τ)) = eigSp r (σ (Sum.inl τ))
  ind₂ : ∀ τ, LinearIndependent M.Ω (b₂ τ) ∧ Submodule.span M.Ω (Set.range (b₂ τ)) = eigSp r (σ (Sum.inr τ))
  flag₁ : ∀ τ, (L.eigLat r (σ (Sum.inl τ))).IsFlagVBOn {q | InFibre ξ p q} (b₁ τ)
  flag₂ : ∀ τ, (L.eigLat r (σ (Sum.inr τ))).IsFlagVBOn {q | InFibre ξ p q} (b₂ τ)
  deg₁ : ∀ τ (i : Fin N) (h : (i : ℕ) < j), ∃ e₀ : M.Ω,
    ((L.eigLat r (σ (Sum.inl τ))).gr (b₁ τ) ⟨i, h⟩).IsDegOn {q | InFibre ξ p q} M.y (M.xdeg (τ, i)) e₀
  deg₂ : ∀ τ (i : Fin N) (h : N - 1 - (i : ℕ) < N - j), j ≤ (i : ℕ) → ∃ e₀ : M.Ω,
    ((L.eigLat r (σ (Sum.inr τ))).gr (b₂ τ) ⟨N - 1 - i, h⟩).IsDegOn {q | InFibre ξ p q} M.y (-M.xdeg (τ, i)) e₀

attribute [instance] DRTie.acg DRTie.mod

end GlobalTheory.CompanionTheory.Ar.Conj
