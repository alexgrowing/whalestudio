import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFFCurve
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Crv

def CurveSemiAbelianConjecture : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), PowFns t →
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (p : ℕ) [Fact p.Prime] [CharP K p], 2 < p →
    ∀ (C : ACurve K) (z : Sp K ⟶ X0) (Y : CurveIn C z), Nonempty C.I →
      (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → (∀ i, FibPF t (centre (Y.x i))) →
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (M : LieModel t.G z V)
      (r : 𝓞 E →+* Module.End K V), M.IsActOf t.act.act r →
    ∀ (T : Type) [Fintype T] (χ : T ⊕ T → (𝓞 E →+* k)), IsSplit χ →
      (∀ τ a, χ (Sum.inr τ) a = χ (Sum.inl τ) (H.bar a)) →
    ∀ (j q : ℕ) (w : T → ℕ → ℝ) (W L : T → ℕ → Submodule K V), 1 ≤ j → 1 ≤ q →
      (∀ τ, W τ 0 = ⊥) → (∀ τ, L τ 0 = ⊥) →
      (∀ τ, W τ j = eigSp r ((algebraMap k K).comp (χ (Sum.inl τ)))) →
      (∀ τ, L τ q = eigSp r ((algebraMap k K).comp (χ (Sum.inr τ)))) → GapCond p j q w →
      0 ≤ lmuNum j q w (fun τ i => (subDeg C (Y.lieLat M) (W τ i) : ℝ))
        (fun τ i => (subDeg C (Y.lieLat M) (L τ i) : ℝ))

end GlobalTheory.CompanionTheory.Ar.Conj
