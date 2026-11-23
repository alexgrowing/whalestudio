import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocTauAlt
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def HolLeadHol : Prop :=
  ∀ (m n : ℕ) (e : ℤ), 1 ≤ m → m < n →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (Pp Γ : Subgroup G) (ι : GR n →* G) (s₀ : ℂ) (Ht : G → ℝ≥0) (f : G → ℂ), Continuous ι →
      (∀ g, ∃ (x : G) (y : GR n) (S : ℂ) (r : ℝ), 0 < r ∧ g = x * ι y ∧
        ∀ y' : GR n, (Ht (x * ι y') : ℝ) = r * hLoc y' ∧ f (x * ι y') = S * F0 m 0 e y') →
      ∀ (U : Set ℂ) (d : Polynomial ℂ) (Ê : ℂ → G → ℂ) (t : ℝ), IsOpen U → GlobalTheory.Cont.IsRightDomain U → s₀ ∈ U →
        (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) →
        (∀ z : ℂ, t < z.re → (∀ C : Set G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets Pp Γ → ℝ, Summable u ∧ ∀ g ∈ C, ∀ c,
            ‖GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) g c‖ ≤ u c) ∧
          ∀ g, Ê z g = d.eval z * GlobalTheory.Eis.cosetSum Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x) g) →
        ∀ j : ℕ, (∀ i < j, ∀ g, iteratedDeriv i (Ê · g) s₀ = 0) →
          (∀ ψ, IsSingTest ψ → ∀ nb : (Fin n → Fin n → ℝ) → GR n, (∀ x, mR (nb x) = nU (herm x)) →
            ∀ (g : G) (a b : GR n), ∫ x, iteratedDeriv j (Ê · (g * ι (a * nb x * b))) s₀ * ψ x = 0) →
          ∀ g, IsHolW m 0 e fun y => iteratedDeriv j (Ê · (g * ι y)) s₀

def Conj : Prop := HolLeadHol → HolLead

def SecFz : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (w : ℂ) (y : GR n), fz m e w (mR y) = F0 m 0 e y * ((hLoc y : ℝ) : ℂ) ^ w

open Classical in

def lift (φ : GR n → ℂ) (x : M2 n) : ℂ := if h : IsUnit x ∧ InG x then φ ⟨h.1.unit, h.2⟩ else 0

def CRLem : Prop :=
  ∀ (n m : ℕ) (e : ℤ) (φ : GR n → ℂ) (Φ : M2 n → ℂ) (Ω : Set (M2 n)), IsOpen Ω → GSet n ⊆ Ω → ContDiffOn ℝ ∞ Φ Ω →
    (∀ y, Φ (mR y) = φ y) → (∀ y k : GR n, InK (mR k) → φ (y * k) = φ y * F0 m 0 e k) →
    (∀ (y : GR n) (Q : Matrix (Fin n) (Fin n) ℂ), rC (lowQ Q) Φ (mR y) = 0) → IsHolW m 0 e φ

def AsmH : Prop := LocTau → SecFz → CRLem → HolLeadHol

end PositivityTheory.Rg.Sw.HSt
