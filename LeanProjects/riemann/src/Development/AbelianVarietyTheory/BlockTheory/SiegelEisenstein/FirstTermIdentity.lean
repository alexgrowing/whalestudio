import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup

noncomputable section

open scoped Matrix NNReal TensorProduct
open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.FirstTermIdentities

def FirstTermIdentity : Prop :=
  ∀ (D : D7) (n : ℕ) (T T' T₀ : HSp D) (t r' : ℕ) (d : HypDec T T' t) (d' : HypDec T' T₀ r'),
  Formalism.MainNotions.SchurIrreducible.wittIdx T₀ = 0 → T.rank + T'.rank = 2 * n → T'.rank < T.rank → 0 < T'.rank →
  ∀ (l : Lvl T) (l' : Lvl T') (l₀ : Lvl T₀), l.Good → l'.Good → l₀.Good → Compat d l l' → Compat d' l' l₀ →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ T.rank →
  ∀ θ : InfFam D, IsInfFam θ →
  ∀ (μ : Measure (Mx D T.rank n)) (𝓕 : Set (Mx D T.rank n)), IsCovolOne (ratMx D T.rank n) μ 𝓕 →
  ∀ (μ' : Measure (Mx D T'.rank n)) (𝓕' : Set (Mx D T'.rank n)), IsCovolOne (ratMx D T'.rank n) μ' 𝓕' →
  ∀ (μX : Measure (Mx D t n)) (𝓕X : Set (Mx D t n)), IsCovolOne (ratMx D t n) μX 𝓕X →
  ∀ ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ T.rank n), StdUnn.IsWeilSch ψ χ θ T μ ω →
  ∀ ω' : StdUnn.G D n →* Module.End ℂ (schwartzA θ T'.rank n), StdUnn.IsWeilSch ψ χ θ T' μ' ω' →
  ∀ H : StdUnn.G D n → ℝ≥0, StdUnn.IsHeight H →
  ∀ ν : Measure l.K, ν.IsHaarMeasure → IsProbabilityMeasure ν →
  ∀ m' : Measure (GA D T'), m'.IsHaarMeasure →
  ∃ κ : ℂ, κ ≠ 0 ∧
    (r' = 0 → ∀ Φ : schwartzA θ T.rank n, KFin ω Φ →
      ∃ Φ' : schwartzA θ T'.rank n, Φ'.1 = ikS d μX (projS ν Φ.1) ∧
        ∀ g, ResidueAt (eisS ω H Φ g) (StdUnn.s0 T n) (κ * StdUnn.thetaInt ω' m' Φ' g)) ∧
    (0 < r' → ∃ (τ : D.what₂.Tau) (zG zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), IsRegS τ ω' d' l'.K zG zH P ∧
      ∀ Φ : schwartzA θ T.rank n, KFin ω Φ →
        ∃ Φ' Ψ : schwartzA θ T'.rank n, Φ'.1 = ikS d μX (projS ν Φ.1) ∧ Ψ.1 = cenH θ τ T' zH Φ'.1 ∧
          ∀ g, ∃ b : ℂ, ResidueAt (regIntS ω' d' l'.K m' P Ψ g) (RegSW.rhoH T' r') b ∧
            ResidueAt (eisS ω H Φ g) (StdUnn.s0 T n) (κ * b))

example {D : D7} {n t : ℕ} {T T' : HSp D} (d : HypDec T T' t) (h : T.rank + T'.rank = 2 * n) (h' : T'.rank < T.rank) :
    T'.rank < n ∧ 0 < t ∧ StdUnn.s0 T n = (t : ℂ) / 2 := by
  have e := d.rank_add
  refine ⟨by omega, by omega, ?_⟩
  have : T.rank = n + t := by omega
  rw [StdUnn.s0, this]; push_cast; ring

example {D : D7} {t : ℕ} {T T' : HSp D} (d : HypDec T T' t) : T.rank % 2 = T'.rank % 2 := by
  have e := d.rank_add
  omega

end GlobalTheory.IndefiniteRowSideFullHecke.FirstTermIdentities

end
