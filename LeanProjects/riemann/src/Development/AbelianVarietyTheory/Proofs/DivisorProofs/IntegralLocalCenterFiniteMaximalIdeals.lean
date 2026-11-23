import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntVZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupActionRingHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

noncomputable section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem iotaF_injective (G : HTGroup p) (v : AwayP p) : Function.Injective (iotaF G v) := by
  have hf : Function.Injective (IsScalarTower.toAlgHom ℚ G.F G.C).toLinearMap :=
    (algebraMap G.F G.C).injective
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := Qv v) _ hf

def intFAlgMap (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    v.1.adicCompletionIntegers ℚ →+* intF G v h1 hm :=
  ((algebraMap (Qv v) (Qv v ⊗[ℚ] G.F)).comp (v.1.adicCompletionIntegers ℚ).subtype).codRestrict _ fun c => by
    rw [mem_intF]
    intro i
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      map_smul, Finsupp.smul_apply, smul_eq_mul, map_one]
    exact mul_mem c.2 (h1 i)

def intFCoord (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    letI := (intFAlgMap G v h1 hm).toAlgebra
    intF G v h1 hm →ₗ[v.1.adicCompletionIntegers ℚ] (Fin (Module.finrank ℚ G.C) → v.1.adicCompletionIntegers ℚ) :=
  letI := (intFAlgMap G v h1 hm).toAlgebra
  { toFun := fun m i => ⟨(basV G v).repr (iotaF G v m) i, (mem_intF G v h1 hm m).1 m.2 i⟩
    map_add' := fun a b => by
      funext i; apply Subtype.ext
      simp [map_add]
    map_smul' := fun c m => by
      funext i; apply Subtype.ext
      show (basV G v).repr (iotaF G v (algebraMap (Qv v) (Qv v ⊗[ℚ] G.F) (c : Qv v) * m)) i =
        (c : Qv v) * (basV G v).repr (iotaF G v m) i
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, map_smul]
      rfl }

theorem intFCoord_injective (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    Function.Injective (intFCoord G v h1 hm) := by
  intro a b hab
  apply Subtype.ext
  apply iotaF_injective G v
  apply (basV G v).repr.injective
  refine Finsupp.ext fun i => ?_
  exact congrArg Subtype.val (congrFun hab i)

theorem intF_finite (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    letI := (intFAlgMap G v h1 hm).toAlgebra
    Module.Finite (v.1.adicCompletionIntegers ℚ) (intF G v h1 hm) :=
  letI := (intFAlgMap G v h1 hm).toAlgebra
  Module.Finite.of_injective (intFCoord G v h1 hm) (intFCoord_injective G v h1 hm)

theorem intF_finite_maximal : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)),
    Set.Finite {I : Ideal (intF G v h1 hm) | I.IsMaximal} := by
  intro p _ G v h1 hm
  letI := (intFAlgMap G v h1 hm).toAlgebra
  haveI := intF_finite G v h1 hm
  exact ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.finite_maximal_ideals_of_finite (R := v.1.adicCompletionIntegers ℚ) (intF G v h1 hm)

end GlobalTheory.OrbFinAf
