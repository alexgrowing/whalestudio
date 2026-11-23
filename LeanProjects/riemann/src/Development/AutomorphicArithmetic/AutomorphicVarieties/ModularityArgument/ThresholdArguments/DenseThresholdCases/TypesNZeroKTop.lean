import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NzOfTypeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroKIface

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.NonzeroTypeTheory
theorem nz_of_typeData_alt (h2 : SmoothRepIrreducibleSubcontainingVector) (h3 : SmoothRepMinimalSubrepresentation) (h4 : SchurInjectiveFromIrreducible) (TD : _root_.UpperTheory.NonzeroTypeTheory.TypeDataAlt) : _root_.UpperTheory.NonzeroTypeTheory.NonzeroTypes := by
  intro E Ω _ _ _ _ _ A w h rc hrc n χ ho
  obtain ⟨J, lam, m, V0, v0, -, -, hsm, hv0, hvec, himp, hemb⟩ := TD E Ω A w h rc hrc n χ ho
  have : CompactSpace (GlobalTheory.LFun.KGL w n) :=
    isCompact_iff_compactSpace.1 (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  obtain ⟨S, p, hS0, hSst, hSirr, hpS, hpid, hpeq, hpv⟩ := h2 _ m V0 hsm v0 hv0
  obtain ⟨d, ξ, ι, hι, hrange, hint, hirr, hsmξ⟩ := h3 _ m V0 hsm S hS0 hSst hSirr
  refine ⟨d, ξ, hirr, hsmξ, fun π => ⟨?_, ?_⟩⟩
  · rintro ⟨g, hg0, hg⟩
    have hgi : Function.Injective g := h4 _ d ξ hirr π.V (π.ρ.comp (GlobalTheory.LFun.KGL w n).subtype) g hg0 hg
    obtain ⟨z, hz⟩ : p v0 ∈ LinearMap.range ι := hrange ▸ hpS v0
    refine himp π ⟨g z, fun h0 => hpv ?_, fun j => ?_⟩
    · have : z = 0 := hgi (h0.trans (map_zero g).symm)
      rw [← hz, this, map_zero]
    · have hξz : ξ (j : ↥(GlobalTheory.LFun.KGL w n)) z = ((lam j : ℂˣ) : ℂ) • z := hι (by
        rw [← hint, hz, ← hpeq, hvec j, map_smul, ← hz, map_smul])
      have := hg (j : ↥(GlobalTheory.LFun.KGL w n)) z
      rw [hξz, map_smul] at this
      exact this.symm
  · intro hc
    obtain ⟨f, hf, hfeq⟩ := hemb π hc
    obtain ⟨z, hz⟩ : ∃ z : Fin d → ℂ, z ≠ 0 := by
      by_contra hne
      push Not at hne
      have : S = ⊥ := by
        rw [← hrange, LinearMap.range_eq_bot]
        exact LinearMap.ext fun v => by rw [hne v, map_zero, LinearMap.zero_apply]
      exact hS0 this
    refine ⟨f ∘ₗ ι, fun h0 => hz (hι (hf ?_)), fun k v => ?_⟩
    · rw [map_zero, map_zero]
      exact LinearMap.congr_fun h0 z
    · simp only [LinearMap.comp_apply]
      rw [← hint, hfeq]
end UpperTheory.NonzeroTypeTheory
end
end
