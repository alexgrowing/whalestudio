import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.GKModules.RightRegular

noncomputable section

open NormedSpace Set Filter Topology
open scoped Manifold ContDiff

namespace Ad3.GA.SmoothLie

open GroundTheory.Automorphic

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

def tailProd {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) (i : Fin d) : G :=
  (List.ofFn fun k => if i < k then h.expG (t k • X k) else 1).prod

def coef {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (t : Fin d → ℝ) (i j : Fin d) : ℝ :=
  b.repr (h.Ad (tailProd h b t i)⁻¹ (b i)) j

structure GoodFam {ι : Type*} (P : (ι → G → ℂ) → Prop) : Prop where
  smooth : ∀ F, P F → ∀ q, h.IsSmoothFun (F q)
  deriv : ∀ F, P F → ∀ X : 𝔤, P fun q => h.rightDeriv X (F q)
  maj : ∀ F, P F → ∀ K : Set G, IsCompact K →
    ∃ u : ι → ℝ, Summable u ∧ ∀ q, ∀ x ∈ K, ‖F q x‖ ≤ u q

variable {h}

end Ad3.GA.SmoothLie
