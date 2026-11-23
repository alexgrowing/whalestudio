import Mathlib
import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsRep
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain

abbrev repAction {G M : Type*} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) :
    DistribMulAction G M where
  smul g x := ρ g x
  one_smul x := by
    change ρ 1 x = x
    rw [map_one, Module.End.one_apply]
  mul_smul g h x := by
    change ρ (g * h) x = ρ g (ρ h x)
    rw [map_mul, Module.End.mul_apply]
  smul_zero g := map_zero (ρ g)
  smul_add g := map_add (ρ g)

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]

noncomputable abbrev sUnitAction (S : Set (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (g : L ≃ₐ[K] L), ∀ w ∈ S, g • w ∈ S) :
    DistribMulAction (L ≃ₐ[K] L) (Additive (S.unit L)) :=
  repAction (GroundTheory.Global.sUnitRep S hS)

end GroundTheory.ProfCoh
