import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleRestriction
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain IdeleLimit

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1))
  (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

set_option maxHeartbeats 4000000 in

theorem localInfl_finiteComponent_eq_idelesLocalRes (n : ℕ) (y : cohomology (ideleRep K.1 F.1) n) :
    (localInfl ι F n).hom ((finiteComponent (placeOfEmbedding ι F) n).hom y) =
      (idelesLocalRes ι n).hom ((levelInfl K F n).hom y) := by
  have h : finiteComponent (placeOfEmbedding ι F) n ≫ localInfl ι F n = levelInfl K F n ≫ idelesLocalRes ι n := by
    rw [finiteComponent, localInfl, levelInfl, idelesLocalRes, ← cohomologyMapAlong_comp,
      ← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_congr _ _ _ _
      (MonoidHom.ext fun σ => coe_localDecompHom_eq_restrictHom ι F σ)
      (fun u : Additive (IdeleGroup F.1) => congrArg Additive.ofMul (idelesProj_of ι F u.toMul).symm) n
  exact congrArg (fun φ => φ.hom y) h

end Finite

section Infinite

variable {v : InfinitePlace K.1} (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
  (F : FiniteSubfield) [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

set_option maxHeartbeats 4000000 in

theorem infLocalInfl_infiniteComponent_eq_infIdelesLocalRes (n : ℕ) (y : cohomology (ideleRep K.1 F.1) n) :
    (infLocalInfl ι F n).hom ((infiniteComponent (infPlaceOfEmbedding ι F) n).hom y) =
      (infIdelesLocalRes ι n).hom ((levelInfl K F n).hom y) := by
  have h : infiniteComponent (infPlaceOfEmbedding ι F) n ≫ infLocalInfl ι F n =
      levelInfl K F n ≫ infIdelesLocalRes ι n := by
    rw [infiniteComponent, infLocalInfl, levelInfl, infIdelesLocalRes, ← cohomologyMapAlong_comp,
      ← cohomologyMapAlong_comp]
    exact cohomologyMapAlong_congr _ _ _ _
      (MonoidHom.ext fun σ => coe_infLocalDecompHom_eq_restrictHom ι F σ)
      (fun u : Additive (IdeleGroup F.1) =>
        congrArg Additive.ofMul (infIdelesProj_of ι F u.toMul).symm) n
  exact congrArg (fun φ => φ.hom y) h

end Infinite

section Components

variable (ι : LocalEmbeddings K) {n : ℕ} (hn : 1 ≤ n)

set_option maxHeartbeats 4000000 in

theorem idelesLimitCohomologyEquiv_apply_inr (v : HeightOneSpectrum (𝓞 K.1)) (y : cohomology (limitRep K) n) :
    idelesLimitCohomologyEquiv ι hn y (.inr v) = (idelesLocalRes (ι.fin v) n).hom y := by
  obtain ⟨p, z, rfl⟩ := exists_levelInfl_eq n y
  rw [idelesLimitCohomologyEquiv_levelInfl]
  change (localInfl (ι.fin v) p.1 n).hom (ι.places.shapiro n (.inr v) p
      ((cohomologyMap (placeProj (.inr v)) n).hom z)) = _
  rw [CompatiblePlaces.shapiro_placeProj_inr]
  exact localInfl_finiteComponent_eq_idelesLocalRes (ι.fin v) p.1 n z

set_option maxHeartbeats 4000000 in

theorem idelesLimitCohomologyEquiv_apply_inl (v : InfinitePlace K.1) (y : cohomology (limitRep K) n) :
    idelesLimitCohomologyEquiv ι hn y (.inl v) = (infIdelesLocalRes (ι.inf v) n).hom y := by
  obtain ⟨p, z, rfl⟩ := exists_levelInfl_eq n y
  rw [idelesLimitCohomologyEquiv_levelInfl]
  change (infLocalInfl (ι.inf v) p.1 n).hom (ι.places.shapiro n (.inl v) p
      ((cohomologyMap (placeProj (.inl v)) n).hom z)) = _
  rw [CompatiblePlaces.shapiro_placeProj_inl]
  exact infLocalInfl_infiniteComponent_eq_infIdelesLocalRes (ι.inf v) p.1 n z

end Components

end

end GroundTheory.ProfCoh
