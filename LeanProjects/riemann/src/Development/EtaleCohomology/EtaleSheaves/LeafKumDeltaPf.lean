import Development.EtaleCohomology.EtaleSheaves.LeafKillCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKumDeltaPf

open LateralTheory.E.E4

def LeafKumSeq : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∃ (δ : H ℤ (sch.obj C) Gm 1 →+ Ht q (sch.obj C) 2 1) (ι : Ht q (sch.obj C) 2 1 →+ H ℤ (sch.obj C) Gm 2),
    (∀ y, δ y = 0 ↔ ∃ z, y = q • z) ∧ ∀ x, ι x = 0 ↔ ∃ y, δ y = x

def LeafBrCurve : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → ∀ w : H ℤ (sch.obj C) Gm 2, q • w = 0 → w = 0

end LateralTheory.E.LeafKumDeltaPf

end
