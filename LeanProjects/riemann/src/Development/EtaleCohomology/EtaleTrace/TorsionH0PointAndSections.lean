import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def TorsionH0PointAndSections : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ j : ℕ,
  ((∀ z : Ht (l ^ j) (sch.obj (S k)) 0 0, ∃ a : ℕ, z = a • one (l ^ j) (sch.obj (S k))) ∧
    ∀ a : ℕ, a • one (l ^ j) (sch.obj (S k)) = 0 → l ^ j ∣ a) ∧
  ∀ {X : Scheme.{0}} (p : X ⟶ S k), IsProper p → ∀ z : Ht (l ^ j) (sch.obj X) 0 0,
    ((∀ y : Pt p, pull (ZMod (l ^ j)) (sch.map y.1) (tw (l ^ j) 0) 0 z = 0) → z = 0) ∧
    (ConnectedSpace X → ∀ y y' : Pt p,
      pull (ZMod (l ^ j)) (sch.map y.1) (tw (l ^ j) 0) 0 z = pull (ZMod (l ^ j)) (sch.map y'.1) (tw (l ^ j) 0) 0 z)

def LadicH0FromTorsion : Prop := LRing → TorsionH0PointAndSections → LadicH0LocallyConstant

end LateralTheory.EtaleTrace
