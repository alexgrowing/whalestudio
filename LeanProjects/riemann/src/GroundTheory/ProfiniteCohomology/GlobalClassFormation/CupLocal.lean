import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalRestriction
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalInvariants
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain

open scoped DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

variable (K) in

def unitsInvariantLimit (a : K.1ˣ) : (unitsLimitRep K).ρ.invariants :=
  ⟨Additive.ofMul (Units.map (algebraMap K.1 ℚ̄ : K.1 →* ℚ̄) a), fun g => by
    apply Additive.toMul.injective
    apply Units.ext
    change (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (algebraMap K.1 ℚ̄ (a : K.1)) = algebraMap K.1 ℚ̄ (a : K.1)
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (a : K.1).2⟩

@[simp]
theorem coe_unitsInvariantLimit (a : K.1ˣ) :
    ((Additive.toMul (unitsInvariantLimit K a : Additive ℚ̄ˣ) : ℚ̄ˣ) : ℚ̄) = algebraMap K.1 ℚ̄ (a : K.1) :=
  rfl

def globalCupClass (χ : Additive K.1.fixingSubgroup →ₜ+ QZ) (a : K.1ˣ) : cohomology (unitsLimitRep K) 2 :=
  (cupCharClassProf (unitsLimitRep K) χ).hom (unitsInvariantLimit K a)

section General

variable (Kv : Type) {Ωv : Type} [Field Kv] [Field Ωv] [Algebra K.1 Kv] [Algebra Kv Ωv] [Algebra K.1 Ωv]
  [IsScalarTower K.1 Kv Ωv] [Algebra.IsIntegral Kv Ωv] [IsGalois Kv Ωv] (ι : ℚ̄ →ₐ[K.1] Ωv)

theorem unitsLocalRes_globalCupClass (χ : Additive K.1.fixingSubgroup →ₜ+ QZ) (a : K.1ˣ) :
    (unitsLocalRes Kv ι 2).hom (globalCupClass χ a) =
      galCupClass Kv Ωv (contCharComp χ (globalDecomp Kv ι) (continuous_globalDecomp Kv ι))
        (Units.map (algebraMap K.1 Kv : K.1 →* Kv) a) := by
  refine cohomologyMapAlong_cupCharClassProf _ _ _ χ _ _ ?_
  apply Additive.toMul.injective
  apply Units.ext
  change algebraMap Kv Ωv (algebraMap K.1 Kv (a : K.1)) = ι (algebraMap K.1 ℚ̄ (a : K.1))
  rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]

end General

variable (ι : LocalEmbeddings K)

theorem placeInv_brauerLocal_globalCupClass_inr (v : HeightOneSpectrum (𝓞 K.1))
    (χ : Additive K.1.fixingSubgroup →ₜ+ QZ) (a : K.1ˣ)
    (g : Gal(AlgebraicClosure (v.adicCompletion K.1)/v.adicCompletion K.1))
    (hg : ∀ (y : AlgebraicClosure (v.adicCompletion K.1))
      (hy : y ∈ GroundTheory.LocalField.maximalAbelianExtension (v.adicCompletion K.1)
        (AlgebraicClosure (v.adicCompletion K.1))),
      g y = (GroundTheory.LocalField.localArtinMap (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
        (Units.map (algebraMap K.1 (v.adicCompletion K.1) : K.1 →* v.adicCompletion K.1) a) ⟨y, hy⟩ :
          AlgebraicClosure (v.adicCompletion K.1))) :
    placeInv (.inr v) (brauerLocal ι (globalCupClass χ a) (.inr v)) =
      χ (Additive.ofMul (globalDecomp (v.adicCompletion K.1) (ι.fin v) g)) := by
  rw [brauerLocal_apply_inr, unitsLocalRes_globalCupClass]
  exact brauerInvZOfIsSepClosure_galCupClass _ _ g hg

theorem placeInv_brauerLocal_globalCupClass_inl (v : InfinitePlace K.1)
    (χ : Additive K.1.fixingSubgroup →ₜ+ QZ) (a : K.1ˣ) (g : Gal(AlgebraicClosure v.Completion/v.Completion))
    (hg : g = 1 ↔ algebraMap K.1 v.Completion (a : K.1) ∈
      Set.range (Algebra.norm v.Completion : AlgebraicClosure v.Completion → v.Completion)) :
    placeInv (.inl v) (brauerLocal ι (globalCupClass χ a) (.inl v)) =
      χ (Additive.ofMul (globalDecomp v.Completion (ι.inf v) g)) := by
  rw [brauerLocal_apply_inl, unitsLocalRes_globalCupClass]
  exact quadraticInv_galCupClass _ _ (infAlgClosure_finrank_le_two v) (infAlgClosure_mul_mem_range_norm v) _ _ g hg

end

end GroundTheory.ProfCoh
