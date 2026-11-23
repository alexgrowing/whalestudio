import Development.EtaleCohomology.EtaleTrace.TorsionH0PointAndSections

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def TorsionH0PointGenerated : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ j : ℕ,
  (∀ z : Ht (l ^ j) (sch.obj (S k)) 0 0, ∃ a : ℕ, z = a • one (l ^ j) (sch.obj (S k))) ∧
    ∀ a : ℕ, a • one (l ^ j) (sch.obj (S k)) = 0 → l ^ j ∣ a

def EtaleTateTwistSectionsDeterminedByPointsOfProper : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ j : ℕ,
  ∀ {X : Scheme.{0}} (p : X ⟶ S k), IsProper p → ∀ s : Sec (tw (l ^ j) 0) X,
    ((∀ y : Pt p, Sec.res y.1 s = 0) → s = 0) ∧
    (ConnectedSpace X → ∀ y y' : Pt p, Sec.res y.1 s = Sec.res y'.1 s)

theorem base_gives_h0_locally_constant (hB : Base) : A9 := hB.1.2.2.2.2.2.2.2.2.2.2.2.1

end LateralTheory.EtaleTrace
