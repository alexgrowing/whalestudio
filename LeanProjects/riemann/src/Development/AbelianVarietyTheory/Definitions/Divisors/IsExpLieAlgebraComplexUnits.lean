import Mathlib
import GroundTheory.AutomorphicForms.GKModules.RightRegular
import GroundTheory.AutomorphicForms.DixmierMalliavinBasic

noncomputable section

open MeasureTheory GroundTheory.Automorphic

namespace GlobalTheory.HCA

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤) {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤)

structure SmFn [MeasurableSpace G] (μ : Measure G) (S : Submodule ℂ (G → ℂ)) (K : Set G)
    (Λ : List (Fin d) → (G → ℂ) → ℂ) : Prop where
  lin : ∀ l, ∀ f ∈ S, ∀ f' ∈ S, ∀ c : ℂ, Λ l (c • f + f') = c * Λ l f + Λ l f'
  bdd : ∀ l, ∃ C : ℝ, ∀ f ∈ S, ‖Λ l f‖ ≤ C * ∫ x in K, ‖f x‖ ∂μ
  der : ∀ l i, ∀ f ∈ S, HasDerivAt (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) (Λ (i :: l) f) 0

def solG (P : Polynomial ℂ) : Submodule ℂ (G → ℂ) :=
  (LinearMap.ker (Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P)).map
    (h.smoothFuns (F := ℂ)).subtype

theorem mem_solG {P : Polynomial ℂ} {f : G → ℂ} : f ∈ solG h b P ↔ ∃ hf : h.IsSmoothFun f,
    Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P
      (⟨f, hf⟩ : h.smoothFuns (F := ℂ)) = 0 := by
  simp only [solG, Submodule.mem_map, LinearMap.mem_ker, Submodule.subtype_apply]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, hg⟩
  · rintro ⟨hf, h0⟩
    exact ⟨⟨f, hf⟩, h0, rfl⟩

namespace SmFnEx

def idChar : (⊤ : Subgroup ℂˣ) →* ℂ := (Units.coeHom ℂ).comp (Subgroup.subtype ⊤)

end SmFnEx

end GlobalTheory.HCA

end
