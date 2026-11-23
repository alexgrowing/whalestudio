import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentityResidues

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FirstTermSplit

open GlobalTheory.RegSch

def AnisoClause : Prop :=
  ∀ (D : D7) (n : ℕ) (T T' : HSp D) (t : ℕ) (d : HypDec T T' t),
    T.rank + T'.rank = 2 * n → T'.rank < T.rank → 0 < T'.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ T.rank →
  ∀ (μ : Measure (Mx D T.rank n)) (𝓕 : Set (Mx D T.rank n)), IsCovolOne (ratMx D T.rank n) μ 𝓕 →
  ∀ (μ' : Measure (Mx D T'.rank n)) (𝓕' : Set (Mx D T'.rank n)), IsCovolOne (ratMx D T'.rank n) μ' 𝓕' →
  ∀ (μ₁ : Measure (Mx D t n)) (𝓕₁ : Set (Mx D t n)), IsCovolOne (ratMx D t n) μ₁ 𝓕₁ →
  ∀ (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ T.rank n)) (ω' : StdUnn.G D n →* Module.End ℂ (schwartzA θ T'.rank n)),
    StdUnn.IsWeilSch ψ χ θ T μ ω → StdUnn.IsWeilSch ψ χ θ T' μ' ω' →
  ∀ H : StdUnn.G D n → ℝ≥0, StdUnn.IsHeight H →
  ∀ (l : Lvl T) (l' : Lvl T'), l.Good → l'.Good → Compat d l l' → HasIw d l.K →
  ∀ ν : Measure l.K, ν.IsHaarMeasure → IsProbabilityMeasure ν →
  ∀ m : Measure (GA D T'), m.IsHaarMeasure →
  ∀ lr : D.what₂.Tau → ℝ, StdUnn.HasRealPar ψ θ lr →
  ∀ s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ τ, IsCartanInv (gramAt D T τ) (s τ)) →
    (∀ k ∈ l.K, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T k) * s τ = s τ * compAt θ τ (Formalism.L2.Theta.mt T k)) →
    IsAniso T' → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Φ : schwartzA θ T.rank n, Φ.1 ∈ StdUnn.fockA θ T n lr s → KFin ω Φ →
      ∀ Φ' : schwartzA θ T'.rank n, Φ'.1 = ikS d μ₁ (projS ν Φ.1) → ∀ g (A : ℂ),
        ResidueAt (eisS ω H Φ g) (StdUnn.s0 T n) A → A = κ * StdUnn.thetaInt ω' m Φ' g

def IsoClause : Prop :=
  ∀ (D : D7) (n : ℕ) (T T' : HSp D) (t : ℕ) (d : HypDec T T' t),
    T.rank + T'.rank = 2 * n → T'.rank < T.rank → 0 < T'.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ T.rank →
  ∀ (μ : Measure (Mx D T.rank n)) (𝓕 : Set (Mx D T.rank n)), IsCovolOne (ratMx D T.rank n) μ 𝓕 →
  ∀ (μ' : Measure (Mx D T'.rank n)) (𝓕' : Set (Mx D T'.rank n)), IsCovolOne (ratMx D T'.rank n) μ' 𝓕' →
  ∀ (μ₁ : Measure (Mx D t n)) (𝓕₁ : Set (Mx D t n)), IsCovolOne (ratMx D t n) μ₁ 𝓕₁ →
  ∀ (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ T.rank n)) (ω' : StdUnn.G D n →* Module.End ℂ (schwartzA θ T'.rank n)),
    StdUnn.IsWeilSch ψ χ θ T μ ω → StdUnn.IsWeilSch ψ χ θ T' μ' ω' →
  ∀ H : StdUnn.G D n → ℝ≥0, StdUnn.IsHeight H →
  ∀ (l : Lvl T) (l' : Lvl T'), l.Good → l'.Good → Compat d l l' → HasIw d l.K →
  ∀ ν : Measure l.K, ν.IsHaarMeasure → IsProbabilityMeasure ν →
  ∀ m : Measure (GA D T'), m.IsHaarMeasure →
  ∀ lr : D.what₂.Tau → ℝ, StdUnn.HasRealPar ψ θ lr →
  ∀ s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ τ, IsCartanInv (gramAt D T τ) (s τ)) →
    (∀ k ∈ l.K, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T k) * s τ = s τ * compAt θ τ (Formalism.L2.Theta.mt T k)) →
    ∀ (T₀ : HSp D) (r' : ℕ) (d₀ : HypDec T' T₀ r'), IsAniso T₀ → 0 < r' →
    ∀ l₀ : Lvl T₀, l₀.Good → Compat d₀ l' l₀ → HasIw d₀ l'.K →
    ∀ (τ : D.what₂.Tau) (zG zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), IsRegS τ ω' d₀ l'.K zG zH P →
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Φ : schwartzA θ T.rank n, Φ.1 ∈ StdUnn.fockA θ T n lr s → KFin ω Φ →
        ∀ Φ' Ψ : schwartzA θ T'.rank n, Φ'.1 = ikS d μ₁ (projS ν Φ.1) → Ψ.1 = cenH θ τ T' zH Φ'.1 → ∀ g (A B : ℂ),
          ResidueAt (eisS ω H Φ g) (StdUnn.s0 T n) A → ResidueAt (regIntS ω' d₀ l'.K m P Ψ g) (rhoH T' r') B → A = κ * B

theorem firstTerm_iff : GlobalTheory.Published.FirstTermIdentityResidues ↔ AnisoClause ∧ IsoClause := by
  constructor
  · intro h
    constructor
    · intro D n T T' t d h₁ h₂ h₃ ψ hψ θ hθ χ hχ hη μ 𝓕 hμ μ' 𝓕' hμ' μ₁ 𝓕₁ hμ₁ ω ω' hω hω' H hH l l' hl hl' hc hI ν hν hν' m hm lr hlr s hs hk
      exact (h D n T T' t d h₁ h₂ h₃ ψ hψ θ hθ χ hχ hη μ 𝓕 hμ μ' 𝓕' hμ' μ₁ 𝓕₁ hμ₁ ω ω' hω hω' H hH l l' hl hl' hc hI ν hν hν' m hm lr hlr s hs hk).1
    · intro D n T T' t d h₁ h₂ h₃ ψ hψ θ hθ χ hχ hη μ 𝓕 hμ μ' 𝓕' hμ' μ₁ 𝓕₁ hμ₁ ω ω' hω hω' H hH l l' hl hl' hc hI ν hν hν' m hm lr hlr s hs hk
      exact (h D n T T' t d h₁ h₂ h₃ ψ hψ θ hθ χ hχ hη μ 𝓕 hμ μ' 𝓕' hμ' μ₁ 𝓕₁ hμ₁ ω ω' hω hω' H hH l l' hl hl' hc hI ν hν hν' m hm lr hlr s hs hk).2
  · rintro ⟨ha, hi⟩ D n T T' t d h₁ h₂ h₃ ψ hψ θ hθ χ hχ hη μ 𝓕 hμ μ' 𝓕' hμ' μ₁ 𝓕₁ hμ₁ ω ω' hω hω' H hH l l' hl hl' hc hI ν hν hν' m hm lr hlr s hs hk
    exact ⟨ha D n T T' t d h₁ h₂ h₃ ψ hψ θ hθ χ hχ hη μ 𝓕 hμ μ' 𝓕' hμ' μ₁ 𝓕₁ hμ₁ ω ω' hω hω' H hH l l' hl hl' hc hI ν hν hν' m hm lr hlr s hs hk,
      hi D n T T' t d h₁ h₂ h₃ ψ hψ θ hθ χ hχ hη μ 𝓕 hμ μ' 𝓕' hμ' μ₁ 𝓕₁ hμ₁ ω ω' hω hω' H hH l l' hl hl' hc hI ν hν hν' m hm lr hlr s hs hk⟩

theorem anisoClause_of_firstTerm (h : GlobalTheory.Published.FirstTermIdentityResidues) : AnisoClause :=
  (firstTerm_iff.1 h).1

theorem isoClause_of_firstTerm (h : GlobalTheory.Published.FirstTermIdentityResidues) : IsoClause :=
  (firstTerm_iff.1 h).2

theorem firstTerm_of_clauses (ha : AnisoClause) (hi : IsoClause) : GlobalTheory.Published.FirstTermIdentityResidues :=
  firstTerm_iff.2 ⟨ha, hi⟩

example (ha : AnisoClause) : GlobalTheory.Published.FirstTermIdentityResidues ↔ IsoClause :=
  ⟨isoClause_of_firstTerm, firstTerm_of_clauses ha⟩

example (hi : IsoClause) : GlobalTheory.Published.FirstTermIdentityResidues ↔ AnisoClause :=
  ⟨anisoClause_of_firstTerm, fun ha => firstTerm_of_clauses ha hi⟩

end GlobalTheory.FirstTermSplit

end
