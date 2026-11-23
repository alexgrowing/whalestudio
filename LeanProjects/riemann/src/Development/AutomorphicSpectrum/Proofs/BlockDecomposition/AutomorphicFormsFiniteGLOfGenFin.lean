import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.HCFin

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem mul_mem_span_zalg_mul {J : Set (Module.End ℂ (Sm E a))} {x : Module.End ℂ (Sm E a)} (hx : x ∈ Zalg E a)
    {s : Module.End ℂ (Sm E a)} (hs : s ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j}) :
    x * s ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j} := by
  induction hs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x', hx', j, hj, rfl⟩ := hy
    exact Submodule.subset_span ⟨x * x', Subalgebra.mul_mem _ hx hx', j, hj, (mul_assoc _ _ _).symm⟩
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy

end GlobalTheory.CompanionTheory.HCFin
