import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.GlCongr

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def StepForm : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m N : ℕ) (hN : m + 2 ≤ N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (s : ℝ) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), IsPsd B →
    Kills ψ π (m + 2) B → MirEq π (m + 1) hN s B →
    ∃ B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, IsPsd B' ∧ Kills ψ π (m + 1) B' ∧
      (∀ v, B' v v = 0 → v ∈ twKer π (derUnip k N (m + 1)) (lvlChar k ψ N (m + 1)) ⊔ LinearMap.ker B) ∧
      MirEq π m (by omega) (s + 1) B' ∧
      (∀ K : Subgroup (GL (Fin (m + 1)) k), IsOpen (K : Set (GL (Fin (m + 1)) k)) → ∃ C : ℝ, ∀ v,
        (∀ g ∈ K, π (blkAt k (m + 1) N (by omega) g) v = v) → (B' v v).re ≤ C * (B v v).re) ∧
      ∀ z : kˣ, nabs k z < 1 → ∀ v, Summable fun i : ℕ =>
        nabs k z ^ (-((i : ℝ) * (m + 1) * s)) *
          (B' (π (scalAt k (m + 1) N (by omega) (z ^ i)) v) (π (scalAt k (m + 1) N (by omega) (z ^ i)) v)).re

def AsmForm : Prop := StepForm k → PositivityTheory.RgUd.BesselSum k

end PositivityTheory.RgUd.Form
