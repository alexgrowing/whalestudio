import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.SphericalEisensteinContinuation
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstTermExistenceOfUniversal

noncomputable section

open scoped Matrix NNReal TensorProduct Classical Topology
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont
open GlobalTheory.Core.Rk.SWLaw (zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.RegularEisensteinLemmas

variable {D : D7} {T T₀ T' : HSp D} {r : ℕ}

structure IsSum (jT : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (j₀ : Matrix (Fin T'.rank) (Fin T₀.rank) D.host.E) : Prop where
  tt : jTᴴ * T'.gram * jT = T.gram
  oo : j₀ᴴ * T'.gram * j₀ = -T₀.gram
  ot : j₀ᴴ * T'.gram * jT = 0
  rank_add : T.rank + T₀.rank = T'.rank

def IsEmb (jT : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (j₀ : Matrix (Fin T'.rank) (Fin T₀.rank) D.host.E)
    (ι : GA D T × GA D T₀ →* GA D T') : Prop :=
  ∀ g h, mt T' (ι (g, h)) ⬝ rat jT = rat jT ⬝ mt T g ∧ mt T' (ι (g, h)) ⬝ rat j₀ = rat j₀ ⬝ mt T₀ h

def IsLag (d : HypDec T T₀ r) (jT : Matrix (Fin T'.rank) (Fin T.rank) D.host.E)
    (j₀ : Matrix (Fin T'.rank) (Fin T₀.rank) D.host.E) (d' : HypDec T' (zeroSp D) (r + T₀.rank)) : Prop :=
  d'.e = (Matrix.fromCols (jT * d.e) (jT * d.i₀ + j₀)).submatrix id finSumFinEquiv.symm

def IsLevi0 (d : HypDec T T₀ r) (m : stab d →* GA D T₀) : Prop :=
  ∀ p : stab d, mt T₀ (m p) = d.p0 ⬝ (mt T p ⬝ d.j0)

def ForCfg (Q : ∀ {D : D7} {T T₀ T' : HSp D} {r : ℕ} (d : HypDec T T₀ r), HypDec T' (zeroSp D) (r + T₀.rank) →
    (GA D T × GA D T₀ →* GA D T') → (stab d →* GA D T₀) → Prop) : Prop :=
  ∀ (D : D7) (T T₀ T' : HSp D) (r : ℕ) (d : HypDec T T₀ r) (jT : Matrix (Fin T'.rank) (Fin T.rank) D.host.E)
    (j₀ : Matrix (Fin T'.rank) (Fin T₀.rank) D.host.E) (d' : HypDec T' (zeroSp D) (r + T₀.rank))
    (ι : GA D T × GA D T₀ →* GA D T') (m : stab d →* GA D T₀),
    IsSum jT j₀ → IsEmb jT j₀ ι → IsLag d jT j₀ d' → IsLevi0 d m → Q d d' ι m

def SumLevel : Prop :=
  ∀ (D : D7) (T T₀ : HSp D) (b : GL (Fin T.rank) (AE D)), IsMaj T b →
    ∃ (T' : HSp D) (jT : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (j₀ : Matrix (Fin T'.rank) (Fin T₀.rank) D.host.E)
      (b' : GL (Fin T'.rank) (AE D)), IsSum jT j₀ ∧ IsMaj T' b' ∧
      ∀ ι : GA D T × GA D T₀ →* GA D T', IsEmb jT j₀ ι → ∀ k ∈ Kmax T b, ι (k, 1) ∈ Kmax T' b'

def EmbEx : Prop :=
  ∀ (D : D7) (T T₀ T' : HSp D) (jT : Matrix (Fin T'.rank) (Fin T.rank) D.host.E)
    (j₀ : Matrix (Fin T'.rank) (Fin T₀.rank) D.host.E), IsSum jT j₀ →
    ∃ ι : GA D T × GA D T₀ →* GA D T', IsEmb jT j₀ ι ∧ Continuous ι ∧ ∀ γ ∈ GQ T, ∀ l ∈ GQ T₀, ι (γ, l) ∈ GQ T'

def EmbHt : Prop :=
  ∀ (D : D7) (T T₀ T' : HSp D) (jT : Matrix (Fin T'.rank) (Fin T.rank) D.host.E)
    (j₀ : Matrix (Fin T'.rank) (Fin T₀.rank) D.host.E) (ι : GA D T × GA D T₀ →* GA D T'), IsSum jT j₀ → IsEmb jT j₀ ι →
    ∃ (c : ℝ) (N : ℕ), ∀ g, GlobalTheory.Grow.height T' (ι (g, 1)) ≤ c * GlobalTheory.Grow.height T g ^ N

def LagEx : Prop :=
  ∀ (D : D7) (T T₀ T' : HSp D) (r : ℕ) (d : HypDec T T₀ r) (jT : Matrix (Fin T'.rank) (Fin T.rank) D.host.E)
    (j₀ : Matrix (Fin T'.rank) (Fin T₀.rank) D.host.E), IsSum jT j₀ →
    ∃ d' : HypDec T' (zeroSp D) (r + T₀.rank), IsLag d jT j₀ d'

def LeviEx : Prop :=
  ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r),
    ∃ m : stab d →* GA D T₀, IsLevi0 d m ∧ ∀ p : stab d, (p : GA D T) ∈ GQ T → m p ∈ GQ T₀

def Law : Prop := ForCfg fun d d' ι m =>
  ∀ p : stab d, ∃ h : ι (p, m p) ∈ stab d', absDet d' ⟨_, h⟩ = absDet d p

def StabOf : Prop := ForCfg fun d d' ι m =>
  ∀ g h, ι (g, h) ∈ stab d' → ∃ hg : g ∈ stab d, h = m ⟨g, hg⟩

def Orbit : Prop := ForCfg fun {_} {T} {T₀} {T'} _ _ d' ι _ =>
  IsAniso T₀ → ∀ γ' ∈ GQ T', ∃ γ ∈ GQ T, γ' * (ι (γ, 1))⁻¹ ∈ stab d'

def Unfold : Prop :=
  ∀ (G H G' : Type) [Group G] [Group H] [Group G'] [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace G']
    [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (Γ P : Subgroup G) (Λ : Subgroup H) (Γ' P' : Subgroup G') (ι : G × H →* G') (m : P →* H) (μ : Measure H) (C : Set H)
    (F : G' → ℂ) (g : G), Countable Γ → Countable Λ → μ.IsMulLeftInvariant → IsFundamentalDomain Λ C μ →
    Continuous ι → Continuous F → (∀ γ ∈ Γ, ∀ l ∈ Λ, ι (γ, l) ∈ Γ') → (∀ p : P, (p : G) ∈ Γ → m p ∈ Λ) →
    (∀ p : P, ι (p, m p) ∈ P') → (∀ x y, ι (x, y) ∈ P' → ∃ hx : x ∈ P, y = m ⟨x, hx⟩) →
    (∀ γ' ∈ Γ', ∃ γ ∈ Γ, γ' * (ι (γ, 1))⁻¹ ∈ P') → LeftInv (P' ⊓ Γ') F → (∀ x, CosetConv P' Γ' F x) →
    IntegrableOn (fun h => ∑' q, ‖term P' Γ' F (ι (g, h)) q‖) C μ →
    ∫ h in C, cosetSum P' Γ' F (ι (g, h)) ∂μ = cosetSum P Γ (fun x => ∫ h, F (ι (x, h)) ∂μ) g

def FundDom : Prop :=
  ∀ (D : D7) (T₀ : HSp D), IsAniso T₀ → ∃ (μ : Measure (GA D T₀)) (C C₀ : Set (GA D T₀)), μ.IsHaarMeasure ∧
    IsFundamentalDomain (GQ T₀) C μ ∧ MeasurableSet C ∧ IsCompact C₀ ∧ C ⊆ C₀ ∧ μ C ≠ 0

def SphRight : Prop :=
  ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), IsMaj T b → HasIw d (Kmax T b) →
    IsAniso T₀ → (∀ s, Continuous (sphericalSection d b s)) ∧
    (∀ g, DifferentiableOn ℂ (sphericalEisenstein d b g) {s | rhoH T r < s.re}) ∧
    (∀ s : ℂ, rhoH T r < s.re → (Continuous fun g => sphericalEisenstein d b g s) ∧
      Continuous fun g => ∑' q, ‖term (stab d) (GQ T) (sphericalSection d b s) g q‖) ∧
    ∀ y : ℝ, rhoH T r < y → ∀ g, 0 < (sphericalEisenstein d b g y).re

def SphSplit : Prop :=
  PositivityTheory.RgEis.ContSplit → ∀ (D : D7) (T : HSp D) (r : ℕ) (d : HypDec T (zeroSp D) r) (b : GL (Fin T.rank) (AE D)),
    IsMaj T b → HasIw d (Kmax T b) → ContMod T fun s g => sphericalEisenstein d b g s

def IntCont : Prop :=
  ∀ (D : D7) (T T₀ T' : HSp D) (ι : GA D T × GA D T₀ →* GA D T') (μ : Measure (GA D T₀)) (C C₀ : Set (GA D T₀))
    (e : ℂ → GA D T' → ℂ) (t : ℝ), Continuous ι → μ.IsHaarMeasure → MeasurableSet C → IsCompact C₀ → C ⊆ C₀ →
    (∃ (c : ℝ) (N : ℕ), ∀ g, GlobalTheory.Grow.height T' (ι (g, 1)) ≤ c * GlobalTheory.Grow.height T g ^ N) →
    (∀ x, DifferentiableOn ℂ (e · x) {s | t < s.re}) → (∀ s : ℂ, t < s.re → Continuous (e s)) → ContMod T' e →
    ContMod T fun s g => ∫ h in C, e s (ι (g, h)) ∂μ

def DivCont : Prop :=
  ∀ (D : D7) (T : HSp D) (I e : ℂ → GA D T → ℂ) (t : ℝ), ContMod T I → Continues (fun s => e s 1) →
    (∀ y : ℝ, t < y → I y 1 ≠ 0) → (∀ g, DifferentiableOn ℂ (e · g) {s | t < s.re}) →
    (∀ s : ℂ, t < s.re → ∀ g, e s g * I s 1 = I s g * e s 1) → ContMod T e

def SecInt : Prop :=
  ∀ (D : D7) (T T₀ T' : HSp D) (r r' : ℕ) (d : HypDec T T₀ r) (d' : HypDec T' (zeroSp D) r') (b : GL (Fin T.rank) (AE D))
    (b' : GL (Fin T'.rank) (AE D)) (ι : GA D T × GA D T₀ →* GA D T') (m : stab d →* GA D T₀) (μ : Measure (GA D T₀)),
    μ.IsHaarMeasure → HasIw d (Kmax T b) → HasIw d' (Kmax T' b') → rhoH T' r' = rhoH T r →
    (∀ k ∈ Kmax T b, ι (k, 1) ∈ Kmax T' b') → (∀ p : stab d, ∃ h : ι (p, m p) ∈ stab d', absDet d' ⟨_, h⟩ = absDet d p) →
    ∀ (s : ℂ) (x : GA D T), ∫ h, sphericalSection d' b' s (ι (x, h)) ∂μ = (∫ h, sphericalSection d' b' s (ι (1, h)) ∂μ) * sphericalSection d b s x

def SlopeTestChoicesGrowth : Prop :=
  ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r), IsAniso T₀ → ∀ b : GL (Fin T.rank) (AE D), IsMaj T b →
    HasIw d (Kmax T b) → Continues (sphericalEisenstein d b 1) → ∀ s₀, ∃ k, EisensteinRegularAt d b s₀ k

def Asm : Prop :=
  SumLevel → EmbEx → EmbHt → LagEx → LeviEx → Law → StabOf → Orbit → Unfold → FundDom → SphRight → SphSplit → IntCont →
    DivCont → SecInt → PositivityTheory.RgEis.ContSplit → SlopeTestChoicesGrowth

end PositivityTheory.RegularEisensteinLemmas
