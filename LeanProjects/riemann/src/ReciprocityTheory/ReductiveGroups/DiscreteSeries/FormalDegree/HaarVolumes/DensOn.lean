import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

abbrev KPair (ε : Fin n → Bool) : Type := {ab : Fin n × Fin n // ab.2 < ab.1 ∧ ε ab.1 = ε ab.2}

abbrev KCo (ε : Fin n → Bool) : Type := (Fin n → ℝ) × (KPair ε → ℂ)

def kMat {ε : Fin n → Bool} (w : KCo ε) : Matrix (Fin n) (Fin n) ℂ := fun a b =>
  if a = b then Complex.I * ((w.1 a : ℝ) : ℂ)
  else if h : b < a ∧ ε a = ε b then w.2 ⟨(a, b), h⟩
  else if h' : a < b ∧ ε b = ε a then -star (w.2 ⟨(b, a), h'⟩) else 0

abbrev GCo (ε : Fin n → Bool) : Type := KCo ε × (PCoord ε → ℂ)

def gMat {ε : Fin n → Bool} (s : GCo ε) : Matrix (Fin n) (Fin n) ℂ := kMat s.1 + pmat s.2

def expSet {ε : Fin n → Bool} (S : Set (GCo ε)) : Set (UJ ε) :=
  {g | ∃ s ∈ S, toM g = NormedSpace.exp (gMat s)}

def polSet {ε : Fin n → Bool} (S : Set (GCo ε)) : Set (UJ ε) :=
  {g | ∃ s ∈ S, toM g = NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)}

def DensOn {ε : Fin n → Bool} (ν : Set (GCo ε) → ENNReal) (d : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
    ν S ≤ ENNReal.ofReal ((1 + η) * d) * volume S ∧ ENNReal.ofReal ((1 - η) * d) * volume S ≤ ν S

end ReciprocityTheory.ChartRestriction.DS
