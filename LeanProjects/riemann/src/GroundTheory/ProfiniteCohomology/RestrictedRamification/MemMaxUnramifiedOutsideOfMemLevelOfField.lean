import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BrauerOrd
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

namespace PicInf

open CategoryTheory NumberField IsDedekindDomain IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} {S : Set (HeightOneSpectrum (𝓞 K.1))}

def levelOfField (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L] :
    FiniteSubfield :=
  ⟨(L.map (maxUnramifiedOutside K.1 ℚ̄ S).val).restrictScalars ℚ, by
    have := K.2
    have : FiniteDimensional K.1 (L.map (maxUnramifiedOutside K.1 ℚ̄ S).val) :=
      LinearEquiv.finiteDimensional (L.equivMap (maxUnramifiedOutside K.1 ℚ̄ S).val).toLinearEquiv
    have : FiniteDimensional ℚ (L.map (maxUnramifiedOutside K.1 ℚ̄ S).val) :=
      Module.Finite.trans K.1 (L.map (maxUnramifiedOutside K.1 ℚ̄ S).val)
    exact this⟩

variable (L : IntermediateField K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) [FiniteDimensional K.1 L]

theorem mem_levelOfField {z : ℚ̄} :
    z ∈ (levelOfField L).1 ↔ ∃ w ∈ L, ((w : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = z :=
  Iff.rfl

instance fact_le_levelOfField : Fact (K ≤ levelOfField L) :=
  ⟨fun z hz => (mem_levelOfField L).2 ⟨algebraMap K.1 _ ⟨z, hz⟩, L.algebraMap_mem _, rfl⟩⟩

theorem mem_maxUnramifiedOutside_of_mem_levelOfField {z : ℚ̄} (hz : z ∈ (levelOfField L).1) :
    z ∈ maxUnramifiedOutside K.1 ℚ̄ S := by
  obtain ⟨w, -, rfl⟩ := (mem_levelOfField L).1 hz
  exact w.2

end

end PicInf

end GroundTheory.ProfCoh
