import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.TransversalSums.SumTranslateTransversal
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.StepForm

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.LeviSmoothness

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure Lv (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (s : ℝ) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop where
  cont : Continuous ψ
  ne : ψ ≠ 1
  smooth : IsSmooth π
  psd : IsPsd B
  kills : Kills ψ π (m + 2) B
  mir : MirEq π (m + 1) h s B

def FixK {m N : ℕ} (h : m + 1 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (K : Subgroup (GL (Fin (m + 1)) k)) (v : V) : Prop :=
  ∀ g ∈ K, π (blkAt k (m + 1) N h g) v = v

end PositivityTheory.RgUd.Form.LeviSmoothness
