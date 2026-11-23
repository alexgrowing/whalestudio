import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhiAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MCorrBC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCorrPull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtIdBC

open CategoryTheory AlgebraicGeometry

private lemma flat_of_dvr {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
    (φ : O →+* O') (ϖ : O) (hϖ : Irreducible ϖ) (h0 : φ ϖ ≠ 0) : φ.Flat := by
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
    rw [map_mul, map_pow] at ha
    rcases mul_eq_zero.1 ha with h | h
    · exact (u.isUnit.map φ).ne_zero h
    · exact pow_ne_zero k h0 h
  algebraize [φ]
  have : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').2 hinj
  have : Module.IsTorsionFree O O' := inferInstance
  exact (inferInstance : Module.Flat O O')

theorem UpperTheory.Ru.crystallineComparison.ptIdBC :
    UpperTheory.Ru.crystallineComparison.PtIdBC := by
  intro l q n O O' _ _ _ _ _ _ φ ϖ hϖ hϖ' hq Y Y' p p' g hpb T hT hId
  have hflat : φ.Flat := flat_of_dvr φ ϖ hϖ hϖ'.ne_zero
  choose T' κ h1 h2 h3 _ using fun j => UpperTheory.Gal.crystallineComparison.corrPull_of l _ _ Y Y' _ p p' g hpb (T j) (hT j)
  refine ⟨T', κ, fun j => ⟨(h1 j).flip, (h2 j).symm, h3 j⟩, ?_⟩
  exact UpperTheory.Gal.crystallineComparison.ptIdBC_of l q n O O' φ hflat ϖ (φ ϖ) (fun _ _ => Iff.rfl)
    (fun a => Ideal.mem_span_singleton.2 (hq a)) Y Y' p p' g hpb T T' κ h1 h2 h3 hId
