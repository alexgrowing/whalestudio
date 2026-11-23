import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.L2Embedding
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InConeRefl

noncomputable section

open Finset

namespace CompanionTheory.RgExh.Fin

open CompanionTheory.RgExh
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.D.LK (IsKMod LocFin IsMin)

variable {n : ℕ}

def arr (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ) : Fin n → ℝ := mu ∘ s.symm

def ConeDS (ε : Fin n → Bool) (X : GMod n) (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ) : Prop :=
  ∀ (ν : Fin n → ℝ) (x : X.V), x ≠ 0 → KHighest (ε ∘ s) (fun a b => X.E (s a) (s b)) ν x →
    CompanionTheory.RgDs.InCone (PI.UpqRep.lowK (ε ∘ s) mu) ν

def StartMod : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ →
    Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ → Nontrivial H → ∀ (D : Submodule ℂ H)
    (E : Fin n → Fin n → Module.End ℂ D) (hK : IsKMod ε σ D E), IsSimple ⟨D, E, hK.gl⟩ ∧ (∃ χ, ScalChar ⟨D, E, hK.gl⟩ χ) ∧ IntWt ⟨D, E, hK.gl⟩

def PathFin : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : GMod n) (χ : Fin n → ℂ) (ss : List (Fin n)),
    (LocFin ε X.E → LocFin ε (path X χ ss).E) ∧ (IntWt X → IntWt (path X χ ss))

def PathExists : Prop :=
  ∀ (n : ℕ) (χ : Fin n → ℂ) (B : ℝ), ∃ C δ : ℝ, 0 < δ ∧ ∀ N₀ : ℝ, ∃ (ss : List (Fin n)) (N : ℝ), N₀ ≤ N ∧
    GoodPath χ ss ∧ FarLabels χ (pathEnd χ ss) B ∧ (∀ s, s ∈ ss) ∧
    (∀ a b, a ≠ b → δ * N ≤ |(pathEnd χ ss a).re - (pathEnd χ ss b).re|) ∧
    ∀ a, |(pathEnd χ ss a).re| ≤ C * N ∧ |(pathEnd χ ss a).im| ≤ C

def PathEndNat : Prop :=
  ∀ (n : ℕ) (χ : Fin n → ℂ) (ss : List (Fin n)), ∃ m : Fin n → ℕ, pathEnd χ ss = χ + (fun a => (m a : ℂ)) ∧
    ∀ a, a ∈ ss → 1 ≤ m a

def SimpleDistinct : Prop :=
  ∀ (n : ℕ) (χ : Fin n → ℂ) (ss : List (Fin n)), SimplePath χ ss → (∀ s, s ∈ ss) → Function.Injective χ

def ScalarCharacterOfL2Embedding : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : GMod n) (χ : Fin n → ℂ), L2Embedding ε X → HasChar X χ → ScalChar X χ

def UnitarizableOfL2Embedding : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : GMod n), L2Embedding ε X → IsSimple X →
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (E : Fin n → Fin n → Module.End ℂ V)
      (hE : GlRel E), IsUnitary ε E ∧ Iso X ⟨V, E, hE⟩

def IsoFacts : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X Y Z : GMod n),
    Iso X X ∧ (Iso X Y → Iso Y X) ∧ (Iso X Y → Iso Y Z → Iso X Z) ∧
    (Iso X Y → (IsSimple X ↔ IsSimple Y)) ∧ (Iso X Y → ∀ χ, (ScalChar X χ ↔ ScalChar Y χ)) ∧
    (Iso X Y → ∀ χ, (HasChar X χ ↔ HasChar Y χ)) ∧ (Iso X Y → (LocFin ε X.E ↔ LocFin ε Y.E)) ∧
    (Iso X Y → (IntWt X ↔ IntWt Y)) ∧ (Iso X Y → ∀ s mu, (AlgDS ε X s mu ↔ AlgDS ε Y s mu)) ∧
    (Iso X Y → ∀ s mu, (ConeDS ε X s mu ↔ ConeDS ε Y s mu))

def CharOfAlgDS : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (χ : Fin n → ℂ) (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ),
    IsUnitary ε E → LocFin ε E → ScalChar ⟨V, E, hE⟩ χ → AlgDS ε ⟨V, E, hE⟩ s mu →
      ∃ τ : Equiv.Perm (Fin n), ∀ a, ((mu a : ℝ) : ℂ) = χ (τ a)

def AlgUniq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (E : Fin n → Fin n → Module.End ℂ V)
    (E' : Fin n → Fin n → Module.End ℂ V') (hE : GlRel E) (hE' : GlRel E') (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ),
    IsUnitary ε E → IsUnitary ε E' → LocFin ε E → LocFin ε E' → IsSimple ⟨V, E, hE⟩ → IsSimple ⟨V', E', hE'⟩ →
    AlgDS ε ⟨V, E, hE⟩ s mu → AlgDS ε ⟨V', E', hE'⟩ s mu → Iso ⟨V, E, hE⟩ ⟨V', E', hE'⟩

def DataUniq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : GMod n) (s s' : Equiv.Perm (Fin n)) (mu mu' : Fin n → ℝ),
    AlgDS ε X s mu → ConeDS ε X s mu → AlgDS ε X s' mu' → s = s' ∧ mu = mu'

def DSOfArr : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam mu →
    (∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), GlobalTheory.Dec.IsSqIntIrr ε σ ∧
      ∀ (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (hK : IsKMod ε σ D E),
        AlgDS ε ⟨D, E, hK.gl⟩ s mu ∧ ConeDS ε ⟨D, E, hK.gl⟩ s mu

def DSOfData : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D)
    (hK : IsKMod ε σ D E) (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ), GlobalTheory.Dec.IsSqIntIrr ε σ →
    AlgDS ε ⟨D, E, hK.gl⟩ s mu → Formalism.MainNotions.S.IsDS (ε ∘ s) mu (fun g => σ (g.submatrix s.symm s.symm))

def KModOf : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ →
    Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ → ∃ (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D), IsKMod ε σ D E

def ArrCount : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (χ χ' : Fin n → ℂ), Function.Injective χ → Function.Injective χ' →
    (∀ a, (χ a).im = 0 ∧ ∃ m : ℤ, (χ a).re - ((n : ℝ) - 1) / 2 = m) →
    (∀ a, (χ' a).im = 0 ∧ ∃ m : ℤ, (χ' a).re - ((n : ℝ) - 1) / 2 = m) →
    ∃ (A : Finset (Equiv.Perm (Fin n) × (Fin n → ℝ))) (A' : Finset (Equiv.Perm (Fin n) × (Fin n → ℝ))),
      A.card = A'.card ∧
      (∀ d, d ∈ A ↔ (Formalism.QuantumDeterminants.IsHCParam d.2 ∧ (∀ a b, a < b → ε (d.1 a) = ε (d.1 b) → d.1 a < d.1 b) ∧
        ∃ τ : Equiv.Perm (Fin n), ∀ a, ((d.2 a : ℝ) : ℂ) = χ (τ a))) ∧
      (∀ d, d ∈ A' ↔ (Formalism.QuantumDeterminants.IsHCParam d.2 ∧ (∀ a b, a < b → ε (d.1 a) = ε (d.1 b) → d.1 a < d.1 b) ∧
        ∃ τ : Equiv.Perm (Fin n), ∀ a, ((d.2 a : ℝ) : ℂ) = χ' (τ a)))

end CompanionTheory.RgExh.Fin
