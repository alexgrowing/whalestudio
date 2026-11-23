import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolLeadHol
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

structure HD (m n : ℕ) (e : ℤ) (G : Type) [Group G] [TopologicalSpace G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ)
    (Ht : G → ℝ≥0) (f : G → ℂ) (U : Set ℂ) (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ) : Prop where
  ιc : Continuous ι
  split : ∀ g, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g = x * ι y ∧
    ∀ y' : GR n, (Ht (x * ι y') : ℝ) = r * hLoc y' ∧ f (x * ι y') = S * F0 m 0 e y'
  hU : IsOpen U
  hR : GlobalTheory.Cont.IsRightDomain U
  hs : s₀ ∈ U
  hol : ∀ g, DifferentiableOn ℂ (Ê · g) U
  cont : ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ)
  far : ∀ z : ℂ, t < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ c,
      ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) g c‖ ≤ u c) ∧
    ∀ g, Ê z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) g

def ιK (n : ℕ) : KR n →* M2 n := (Units.coeHom (M2 n)).comp ((GR n).subtype.comp (KR n).subtype)

def resG {G : Type} [Group G] (ι : GR n →* G) (F : G → ℂ) (g : G) : M2 n → ℂ := lift fun y => F (g * ι y)

def FarId : Prop :=
  ∀ (m n : ℕ) (e : ℤ), 1 ≤ m → m < n →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0) (f : G → ℂ) (U : Set ℂ)
      (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ), HD m n e G Pp Γ ι s₀ Ht f U d Ê t → SecFz →
    ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
      (Q : Matrix (Fin n) (Fin n) ℂ) (N : ℕ) (ρ : Fin N → KR n → ℂ) (ψ : Fin N → (Fin n → Fin n → ℝ) → ℂ)
      (a b : Fin N → M2 n) (D : ℂ → ℂ) (M : Fin N → ℂ → ℂ), (∀ l, Continuous (ρ l)) → (∀ l, IsSingTest (ψ l)) →
      (∀ l, InG (a l) ∧ InG (b l)) → Differentiable ℂ D → (∀ l, Differentiable ℂ (M l)) →
      (∀ (z : ℂ) (x : M2 n), InG x →
        D z * rC (lowQ Q) (fz m e z) x = ∑ l, M l z * tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (fz m e z) x) →
      (∃ t' : ℝ, ∀ z : ℂ, t' < z.re → ∀ (g : G) (y : GR n),
        D (z - s₀) * rC (lowQ Q) (resG ι (Ê z) g) (mR y) =
          ∑ l, M l (z - s₀) * tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (Ê z) g) (mR y)) ∧
      ∀ z ∈ U, ∀ (g : G) (y k : GR n), k ∈ KR n → Ê z (g * ι (y * k)) = Ê z (g * ι y) * F0 m 0 e k

def SmoothX : Prop :=
  ∀ (m n : ℕ) (e : ℤ), 1 ≤ m → m < n →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0) (f : G → ℂ) (U : Set ℂ)
      (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ), HD m n e G Pp Γ ι s₀ Ht f U d Ê t → ∀ g : G,
    ∃ (Φ : ℂ → M2 n → ℂ) (Ω : Set (M2 n)) (c : ℂ → ℂ), IsOpen Ω ∧ GSet n ⊆ Ω ∧ DifferentiableOn ℂ c U ∧ c s₀ ≠ 0 ∧
      (∀ z ∈ U, ∀ y : GR n, Φ z (mR y) = c z * Ê z (g * ι y)) ∧
      (∀ z ∈ U, ContDiffOn ℝ ∞ (Φ z) Ω) ∧
      (∀ r : ℕ, ContDiffOn ℝ ∞ (fun x => iteratedDeriv r (Φ · x) s₀) Ω) ∧
      (∀ x ∈ Ω, DifferentiableOn ℂ (Φ · x) U) ∧
      ∀ (Q : Matrix (Fin n) (Fin n) ℂ) (y : GR n),
        DifferentiableOn ℂ (fun z => rC (lowQ Q) (Φ z) (mR y)) U ∧
        ∀ r : ℕ, iteratedDeriv r (fun z => rC (lowQ Q) (Φ z) (mR y)) s₀ =
          rC (lowQ Q) (fun x => iteratedDeriv r (Φ · x) s₀) (mR y)

def TopHol : Prop :=
  ∀ (m n : ℕ) (e : ℤ), 1 ≤ m → m < n →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0) (f : G → ℂ) (U : Set ℂ)
      (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ), HD m n e G Pp Γ ι s₀ Ht f U d Ê t →
    ∀ [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
      (ρ : KR n → ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n), Continuous ρ → Continuous ψ → HasCompactSupport ψ →
      InG a → InG b → ∀ (g : G) (y : GR n),
      DifferentiableOn ℂ (fun z => tOp μ (ιK n) ρ ψ a b (resG ι (Ê z) g) (mR y)) U ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => tOp μ (ιK n) ρ ψ a b (resG ι (Ê z) g) (mR y)) s₀ =
        tOp μ (ιK n) ρ ψ a b (resG ι (fun x => iteratedDeriv r (Ê · x) s₀) g) (mR y)

def RcCongr : Prop :=
  ∀ (n : ℕ) (F F' : M2 n → ℂ) (Z : M2 n) (x : M2 n), InG x → (∀ x', InG x' → F x' = F' x') →
    (∀ t : ℝ, InG (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z))))) →
    (∀ t : ℝ, InG (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))) → rC Z F x = rC Z F' x

end PositivityTheory.Rg.Sw.HSt
