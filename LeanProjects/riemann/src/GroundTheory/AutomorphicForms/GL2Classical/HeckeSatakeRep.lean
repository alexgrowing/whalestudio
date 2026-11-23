import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.HeckeSatake
import GroundTheory.AutomorphicForms.HeckeIrreducible

open NumberField IsDedekindDomain Matrix MeasureTheory CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm ValuativeRel Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm Spherical Iwasawa GLnLocal HeckeAlgebra

variable (p : ℕ) [hp : Fact p.Prime]

def translateSpan (φ : AdelicGL ℚ 2 → ℂ) : Submodule ℂ (AdelicGL ℚ 2 → ℂ) :=
  Submodule.span ℂ (Set.range fun g : FiniteAdelicGL ℚ 2 => finRightRep g φ)

theorem translateSpan_le_comap (φ : AdelicGL ℚ 2 → ℂ) (g : FiniteAdelicGL ℚ 2) :
    translateSpan φ ≤ (translateSpan φ).comap (finRightRep g) := by
  rw [translateSpan, Submodule.span_le]
  rintro _ ⟨h, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
  exact Submodule.subset_span ⟨g * h, rfl⟩

def translateRep (φ : AdelicGL ℚ 2 → ℂ) : Representation ℂ (GL (Fin 2) (Qp p)) (translateSpan φ) :=
  (finRightRep.subrepresentation (translateSpan φ) (translateSpan_le_comap φ)).comp
    (localEmbedding (placeAt p))

def translateIncl (φ : AdelicGL ℚ 2 → ℂ) :
    Representation.IntertwiningMap (translateRep p φ) (localRightRep p) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap (translateRep p φ) (localRightRep p) (translateSpan φ).subtype
    fun _ _ => rfl

def awayIntertwining {y : FiniteAdelicGL ℚ 2}
    (hy : ∀ z, localEmbedding (placeAt p) z * y = y * localEmbedding (placeAt p) z) :
    Representation.IntertwiningMap (localRightRep p) (localRightRep p) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap (localRightRep p) (localRightRep p) (finRightRep y) fun z v => by
    change finRightRep y (finRightRep (localEmbedding (placeAt p) z) v) =
      finRightRep (localEmbedding (placeAt p) z) (finRightRep y v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hy]

variable {N : ℕ} [NeZero N] [MeasurableSpace (GL (Fin 2) (Qp p))] [BorelSpace (GL (Fin 2) (Qp p))]
  (μ : Measure (GL (Fin 2) (Qp p))) [μ.IsHaarMeasure]

end GL2Classical

end

end GroundTheory.Automorphic
