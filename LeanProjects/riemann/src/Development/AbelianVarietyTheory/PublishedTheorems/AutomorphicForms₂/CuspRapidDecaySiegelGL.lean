import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import GroundTheory.AutomorphicForms.ReductionSiegel

noncomputable section

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.Published

def CuspRapidDecaySiegelGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsCuspForm φ →
    ∀ ω : Set (AdelicGLn.AdelicGL E a), IsCompact ω →
      ω ⊆ (adelicBorel (K := E) (n := a) : Set (AdelicGLn.AdelicGL E a)) →
      (∀ b ∈ ω, (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det b) : ℝ) = 1) →
      ∀ t : ℝ, 0 < t → ∀ lam : Fin a → ℝ, ∃ C : ℝ,
        ∀ b ∈ ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
          ∏ i, r i = 1 → ∀ k ∈ maxCompact (K := E) (n := a),
            ‖φ.1 (b * diagUnits a (fun i => posIdele (r i) (hr i)) * k)‖ ≤ C * ∏ i, r i ^ lam i

end GlobalTheory.Published

end
