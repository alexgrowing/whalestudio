import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.ConeDefs
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalInvariants
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)

instance fintype_gal_infAlgClosure (v : InfinitePlace K.1) :
    Fintype Gal(AlgebraicClosure v.Completion / v.Completion) :=
  inferInstance

def gsRealFamily (v : {v : InfinitePlace K.1 // v.IsReal}) :
    Gal(AlgebraicClosure v.1.Completion / v.1.Completion) →ₜ* galUnramifiedOutside K.1 ℚ̄ S :=
  ⟨decompHomS v.1.Completion S (ιr v), continuous_decompHomS (Kv := v.1.Completion) S (ιr v)⟩

theorem gsRealFamily_apply (v : {v : InfinitePlace K.1 // v.IsReal})
    (σ : Gal(AlgebraicClosure v.1.Completion / v.1.Completion)) (y : maxUnramifiedOutside K.1 ℚ̄ S) :
    ιr v ((gsRealFamily S ιr v σ y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = σ (ιr v y) :=
  decompHom_apply ((ιr v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val) σ y

variable (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

abbrev gsTateCompactCohomology (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]
    (n : ℕ) : ModuleCat (ULift.{0} ℤ) :=
  tateCompactCohomologyRes (gsFinFamily S ιs) (gsRealFamily S ιr) M n

abbrev gsRealRes (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] (n : ℕ) :=
  globalToLocal (gsRealFamily S ιr) M (fun v => Rep.res (gsRealFamily S ιr v).toMonoidHom M)
    (fun _ => CategoryTheory.CategoryStruct.id _) n

end

end GroundTheory.ProfCoh
