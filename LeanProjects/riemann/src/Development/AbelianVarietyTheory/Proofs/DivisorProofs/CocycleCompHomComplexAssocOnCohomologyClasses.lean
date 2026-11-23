import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem cocycle_comp_assoc_classes : ∀ (R : Type) [CommRing R] {K L M N : Cx R} {a b c ab bc abc : ℤ} (h1 : a + b = ab) (h2 : b + c = bc) (h3 : ab + c = abc) (h4 : a + bc = abc), (∀ (x : Cocycle K L a) (y : Cocycle L M b) (z : CohomologyClass M N c), cpre (zcomp x y h1) N c abc h3 z = cpre x N bc abc h4 (cpre y N c bc h2 z)) ∧ (∀ (x : Cocycle K L a) (y : CohomologyClass L M b) (z : Cocycle M N c), cpost K z ab abc h3 (cpre x M b ab h1 y) = cpre x N bc abc h4 (cpost L z b bc h2 y)) ∧ (∀ (x : CohomologyClass K L a) (y : Cocycle L M b) (z : Cocycle M N c), cpost K (zcomp y z h2) a abc h4 x = cpost K z ab abc h3 (cpost K y a ab h1 x)) := by
  intro R _ K L M N a b c ab bc abc h1 h2 h3 h4
  have hA : a + b + c = abc := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro x y z
    obtain ⟨z, rfl⟩ := z.mk_surjective
    rw [cpre_mk, cpre_mk, cpre_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA))
  · intro x y z
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [cpre_mk, cpost_mk, cpost_mk, cpre_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA))
  · intro x y z
    obtain ⟨x, rfl⟩ := x.mk_surjective
    rw [cpost_mk, cpost_mk, cpost_mk]
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_assoc x.1 y.1 z.1 h1 h2 hA).symm)

end GlobalTheory
