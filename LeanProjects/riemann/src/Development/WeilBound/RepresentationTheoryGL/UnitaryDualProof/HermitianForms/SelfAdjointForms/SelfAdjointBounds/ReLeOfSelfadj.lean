import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.FixK

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.LeviSmoothness.asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem re_le_of_selfadj {V : Type} [AddCommGroup V] [Module ℂ V] {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hB : IsPsd B) (u v : V)
    (h : B u v = B u u) : (B u u).re ≤ (B v v).re := by
  have h1 := hB.2 (v - u)
  have h2 := hB.1 u v
  rw [h] at h2
  simp only [map_sub, LinearMap.sub_apply, Complex.sub_re] at h1
  rw [h2, h, Complex.conj_re] at h1
  linarith

end PositivityTheory.RgUd.Form.LeviSmoothness.asm
