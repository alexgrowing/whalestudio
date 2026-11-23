import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

theorem latDR_subset_latHT :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ) (x : Sp C ⟶ X), latDR t x ⊆ latHT t p x := by
  intro E _ _ _ H X t C _ _ p x v hv
  obtain ⟨xO, hx, vO, htan, hvO⟩ := hv
  have h1 : epsMul (1 : C) = RingHom.id (DualNumber C) := by
    ext a <;> simp [epsMul]
  have h2 : spMap (RingHom.id (DualNumber C)) = 𝟙 _ := by
    simp [spMap]
  refine ⟨xO, hx, 0, vO, htan, ?_, ?_⟩
  · rw [pow_zero, h1, h2, Category.id_comp, hvO]
  · intro n c g _
    rw [pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top

end GlobalTheory.ShFam.Pad
