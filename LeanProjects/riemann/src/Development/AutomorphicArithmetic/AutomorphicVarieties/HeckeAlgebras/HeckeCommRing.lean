import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

noncomputable section

open IsLocalRing

namespace UpperTheory.V.Hi

variable {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M]

instance heckeCommRing (Y : Submodule A M) (op : ι → Module.End A M) [h : Fact (CommOn Y op)] : CommRing (heckeAlg Y op) :=
  { (inferInstance : Ring (heckeAlg Y op)) with
    mul_comm := fun a b => by
      have key : ∀ s ∈ {t : Module.End A Y | ∃ i, Restr t (op i)}, ∀ t ∈ {t : Module.End A Y | ∃ i, Restr t (op i)},
          s * t = t * s := by
        rintro s ⟨i, hi⟩ t ⟨j, hj⟩
        refine LinearMap.ext fun y => Subtype.ext ?_
        change (s (t y) : M) = t (s y)
        rw [hi, hj, hj, hi]
        exact h.out.2 i j y y.2
      exact (Algebra.adjoinCommSemiringOfComm A key).mul_comm a b }

def heckeGen (Y : Submodule A M) (op : ι → Module.End A M) [h : Fact (CommOn Y op)] (i : ι) : heckeAlg Y op :=
  ⟨(op i).restrict (h.out.1 i), Algebra.subset_adjoin ⟨i, fun _ => rfl⟩⟩

theorem IsCNL.ofCO (O R : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing R] [Algebra O R]
    [Alg.IsCO O R] : IsCNL R where
  complete := inferInstance
  finite := Finite.of_surjective _ (Alg.resMap_bijective O R).2

end UpperTheory.V.Hi
