import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial

noncomputable section

namespace PositivityTheory.LowerBoundConstant

open GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

abbrev Gx (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) : Subgroup (GL (Fin n) k) :=
  KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))

def lowC (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) : Set (GL (Fin n) k) :=
  {c | c ∈ KOne k (Fin n) ∧
    ∀ i j : Fin n, ¬ (e.symm j).1 < (e.symm i).1 → ((c : Matrix (Fin n) (Fin n) k) - 1) i j = 0}

end PositivityTheory.LowerBoundConstant

end
