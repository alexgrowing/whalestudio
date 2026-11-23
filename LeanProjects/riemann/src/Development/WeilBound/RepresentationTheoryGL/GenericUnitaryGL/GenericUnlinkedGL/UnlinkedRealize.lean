import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.RgGu

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def GenericUnique : Prop :=
  ∀ (N : ℕ) (s : Multiset (IrrGL k)) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W),
    HasSupport π s → HasSupport σ s → IsGeneric π → IsGeneric σ → Nonempty (π.Equiv σ)

def SuppExists : Prop :=
  ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → ∃ s : Multiset (IrrGL k), HasSupport π s

def UnlinkedRealize : Prop :=
  ∀ (N : ℕ) (s : Multiset (IrrGL k)), (∀ y ∈ s, y.IsCusp) → (s.map Sigma.fst).sum = N →
    ∃ (h : ℕ) (Δ : Fin h → Segment k) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N),
      (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) ∧ (∀ i, IsLSeg (Δ i) (x i).rep) ∧ HasSupport (prodIrr x hd) s ∧
        IsGeneric (prodIrr x hd)

def UnlinkedLayers : Prop :=
  ∀ s : Multiset (IrrGL k), (∀ y ∈ s, y.IsCusp) →
    ∃ (h : ℕ) (Δ : Fin h → Segment k), (∀ i j, i ≠ j → ¬ (Δ i).Linked (Δ j)) ∧
      (Finset.univ.val.bind fun i => (Δ i).ms) = s

end GlobalTheory.RgGu

end
