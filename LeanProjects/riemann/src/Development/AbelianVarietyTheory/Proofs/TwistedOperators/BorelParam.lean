import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling

namespace GlobalTheory.ZonalCellDecomposition

def blkEquiv (l t : ℕ) : Fin (l * t) ≃ GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t :=
  finProdFinEquiv.symm.trans (Equiv.sigmaEquivProd (Fin l) (Fin t)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def mtor {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    GL (A ⊕ D) k :=
  torusElt k (A ⊕ D) ϖ (Sum.elim 0 e)

def dcell {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    Set (GL (A ⊕ D) k) :=
  DoubleCoset.doubleCoset (mtor ϖ e) (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D : Set (GL (A ⊕ D) k))
    (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D)

def IsBiType {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ)
    (φ : GL (A ⊕ D) k → ℂ) : Prop :=
  ∀ j ∈ GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D, ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
    ∀ g, φ (j * g) = (ξ d : ℂ) * φ g ∧ φ (g * j) = (ξ d : ℂ) * φ g

def sumAbs {D : Type} [Fintype D] (e : D → ℤ) : ℤ := ∑ i, |e i|

def zonalInt {N : ℕ} [MeasurableSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) (ψ : GL (Fin N) k → ℂ)
    (g : GL (Fin N) k) : ℂ :=
  ∫ κ in (KO k (Fin N) : Set (GL (Fin N) k)), ψ (κ * g) ∂μK

def borelParam {N : ℕ} (q : ℕ) (α : Fin N → ℂˣ) (x : Fin N) : ℂ :=
  (α x : ℂ) * (q : ℂ) ^ (((x : ℕ) : ℂ) - ((N : ℂ) - 1) / 2)

end GlobalTheory.ZonalCellDecomposition
