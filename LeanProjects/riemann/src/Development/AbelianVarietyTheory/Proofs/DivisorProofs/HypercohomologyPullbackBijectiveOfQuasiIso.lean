import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeSeqExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafComplexMappingConeAcyclicOfQuasiIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.KInjPull

variable {C : Type*} [Category C] [Abelian C]

theorem cls_eq_zero_of_acyclic {A I : CochainComplex C ℤ} (hA : A.Acyclic) [I.IsKInjective] {n : ℤ}
    (z : Cocycle A I n) : CohomologyClass.mk z = 0 := by
  let g : A ⟶ I⟦n⟧ := Cocycle.homOf (z.rightShift n 0 (zero_add n))
  let H := IsKInjective.homotopyZero g hA
  have h1 : δ (-1) 0 (Cochain.ofHomotopy H) = (z.1.rightShift n 0 (zero_add n)) := by
    rw [δ_ofHomotopy, Cochain.ofHom_zero, sub_zero]
    have := Cocycle.ofHom_homOf_eq_self (z.rightShift n 0 (zero_add n))
    exact congrArg Subtype.val this
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • (Cochain.ofHomotopy H).rightUnshift (n - 1) (by omega), ?_⟩
  rw [δ_units_smul, Cochain.δ_rightUnshift _ (n - 1) (by omega) n 0 (by omega), h1]
  simp [smul_smul]

end GlobalTheory.EtC.KInjPull

theorem GlobalTheory.EtC.cpull_bijective_of_quasiIso : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [QuasiIso f] (I : Cx R) [I.IsKInjective] (n : ℤ), Function.Bijective (cpull f I n) := by
  intro R _ K L f _ I _ n
  have hA := GlobalTheory.EtC.mappingCone_acyclic R f
  have hz : ∀ m (x : CohomologyClass (mappingCone f) I m), x = 0 := by
    intro m x
    obtain ⟨z, rfl⟩ := x.mk_surjective
    exact KInjPull.cls_eq_zero_of_acyclic hA z
  obtain ⟨e1, e2, -⟩ := GlobalTheory.EtC.coneSeq_exact R f I n
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨w, rfl⟩ := (e1 x).1 hx
    rw [hz n w, map_zero]
  · exact (e2 y).1 (hz (n + 1) _)
