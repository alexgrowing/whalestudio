import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped ENNReal

def HaarIdx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (K A : Subgroup G), A ≤ K → IsOpen (A : Set G) →
    A.relIndex K ≠ 0 → μ (K : Set G) = (A.relIndex K : ℝ≥0∞) * μ (A : Set G)

def RedIdx : Prop :=
  ∀ (K Q : Type) [Group K] [Group Q] [Finite Q] (ρ : K →* Q), Function.Surjective ρ →
    ∀ A : Subgroup K, ρ.ker ≤ A → A.index * Nat.card (A.map ρ) = Nat.card Q

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

abbrev HAp (p : TypX X) : Type := HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J

def KvX (p : TypX X) : Set (HAp X p) :=
  Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1

def KgX (p : TypX X) : Set (HAp X p) :=
  Kgv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (gOf p) p.1

def KppX (p : TypX X) : Set (HAp X p) :=
  compSet X.B.I.cm.sig X.B.I.J (levelUnitary X hb) p.1

def KnatX (u : D.what₂.Word) (p : TypX X) : Set (HAp X p) :=
  Knatv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X u) (gOf p) p.1

abbrev muP (p : TypX X) : Measure (HAp X p) := X.measG.μGv p.1

def StTop (p : TypX X) : Prop := ContinuousMul (HAp X p) ∧ BorelSpace (HAp X p)

def StK (p : TypX X) : Prop :=
  ∃ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p ∧ IsOpen (K : Set (HAp X p)) ∧
    IsCompact (K : Set (HAp X p)) ∧ IsOpen (KgX X p)

def StRed (p : TypX X) : Prop :=
  ∀ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p →
    ∃ ρ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)), Function.Surjective ρ ∧
      ∀ x : K, ρ x = 1 ↔ (x : HAp X p) ∈ KgX X p

def StImA (p : TypX X) : Prop :=
  ∀ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p →
    ∀ ρ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)), Function.Surjective ρ →
      (∀ x : K, ρ x = 1 ↔ (x : HAp X p) ∈ KgX X p) →
      ∃ A : Subgroup K, Subtype.val '' (A : Set K) = KppX X hb p ∧ ρ.ker ≤ A ∧
        Nat.card (A.map ρ) = nnC D.R.rS D.R.k (gOf p) * ukC D.R.k (gOf p)

def StImB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∀ K : Subgroup (HAp X p), (K : Set (HAp X p)) = KvX X p →
    ∀ ρ : K →* GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)), Function.Surjective ρ →
      (∀ x : K, ρ x = 1 ↔ (x : HAp X p) ∈ KgX X p) →
      ∃ B : Subgroup K, Subtype.val '' (B : Set K) = KnatX X u p ∧ ρ.ker ≤ B ∧
        Nat.card (B.map ρ) = glkC D.R.k (gOf p) * nnC D.R.rS D.R.k (gOf p)

def StMeasA (p : TypX X) : Prop :=
  ∃ i : ℕ, (i : ℝ) * ((nnC D.R.rS D.R.k (gOf p) : ℝ) * (ukC D.R.k (gOf p) : ℝ)) = (ggC D.R.rS D.R.k (gOf p) : ℝ) ∧
    ((nnC D.R.rS D.R.k (gOf p) : ℝ) * (ukC D.R.k (gOf p) : ℝ)) ≠ 0 ∧
    muP X p (KvX X p) = (i : ℝ≥0∞) * muP X p (KppX X hb p)

def StMeasB (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ j : ℕ, (j : ℝ) * ((glkC D.R.k (gOf p) : ℝ) * (nnC D.R.rS D.R.k (gOf p) : ℝ)) = (ggC D.R.rS D.R.k (gOf p) : ℝ) ∧
    ((glkC D.R.k (gOf p) : ℝ) * (nnC D.R.rS D.R.k (gOf p) : ℝ)) ≠ 0 ∧
    muP X p (KvX X p) = (j : ℝ≥0∞) * muP X p (KnatX X u p) ∧
    muP X p (KnatX X u p) ≠ 0 ∧ muP X p (KnatX X u p) ≠ ⊤

end Loc

def MeasAAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word), HypX X hb FdN FdN' u u' → ∀ p : TypX X, StMeasA X hb p

def MeasBAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word), HypX X hb FdN FdN' u u' → ∀ p : TypX X, StMeasB X u p

end MassDataIdxSteps
