import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicProductEquivProductOfPartition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos GlobalTheory.SplitRead GlobalTheory.ProdReorder

noncomputable section

namespace GlobalTheory.CompanionTheory.SegReorder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def PairComm (x y : IrrGL k) : Prop :=
  ∀ (N : ℕ) (h₁ : x.1 + y.1 = N) (h₂ : y.1 + x.1 = N),
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.rep y.rep)).Equiv (ind₂ (stdSum h₂) (extTensor y.rep x.rep)))

theorem famCongr {u : ℕ} {f g : Fin u → IrrGL k} (hfg : ∀ i, f i = g i) {T : ℕ}
    (e : (Σ i, Fin (f i).1) ≃ Fin T) (e' : (Σ i, Fin (g i).1) ≃ Fin T) :
    Nonempty ((multiProd e fun i => (f i).rep).Equiv (multiProd e' fun i => (g i).rep)) := by
  obtain rfl : f = g := funext hfg
  exact multiProd_placing e e' _

def MFClaim (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) : Prop :=
  ∀ (y : Fin (s + 1) → IrrGL k) (a : Fin (s + 1)), (∀ i, i < a → PairComm (y i) (y a)) →
    ∀ {T N : ℕ} (e : (Σ i, Fin (y i).1) ≃ Fin N) (h : (y a).1 + T = N)
      (e' : (Σ j : Fin s, Fin (y (a.succAbove j)).1) ≃ Fin T),
    Nonempty ((multiProd e fun i => (y i).rep).Equiv (ind₂ (stdSum h)
      (extTensor (y a).rep (multiProd e' fun j => (y (a.succAbove j)).rep))))

def RGClaim (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) : Prop :=
  ∀ (Γ : Fin n → Segment k) (y : Fin n → IrrGL k) (g : Fin n → Fin n), Function.Injective g →
    (∀ i j, i < j → ¬ (Γ i).Precedes (Γ j)) → (∀ i j, i < j → ¬ (Γ (g i)).Precedes (Γ (g j))) →
    (∀ i, IsLSeg (Γ i) (y i).rep) → ∀ (z : Fin n → IrrGL k), (∀ i, z i = y (g i)) →
    ∀ {N : ℕ} (e : (Σ i, Fin (y i).1) ≃ Fin N) (e' : (Σ i, Fin (z i).1) ≃ Fin N),
    Nonempty ((multiProd e fun i => (y i).rep).Equiv (multiProd e' fun i => (z i).rep))

end GlobalTheory.CompanionTheory.SegReorder
