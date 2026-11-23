import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.OfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivContraLocComp
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem exists_satFam_of_isDiscrete : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), (∀ x : CuspSub E N, ∀ᶠ v in Filter.cofinite, ∃ C, (CG.mk x).HasSat v C) ∧ ∀ (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∃ B, SatFam V B := by
  intro E _ _ _ N
  have hF := GlobalTheory.automorphicFormsFiniteGL
  refine ⟨fun x => UnrSat.eventually_hasSatGL_locRep hF E N x, fun V hV => ?_⟩
  choose σ hσ using GlobalTheory.DiscLocEx.exists_isLocCompGL hF E N V hV
  have h : ∀ w, ∃ B, GlobalTheory.LGrp.IsSpherical (σ w).ρ (GlobalTheory.LFun.KGL w N) → GlobalTheory.LFun.HasSatGL w (σ w).ρ B := fun w => by
    by_cases hs : GlobalTheory.LGrp.IsSpherical (σ w).ρ (GlobalTheory.LFun.KGL w N)
    · obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible (σ w).smooth (σ w).irred hs
      exact ⟨B, fun _ => hB⟩
    · exact ⟨0, fun h => absurd h hs⟩
  choose B hB using h
  refine ⟨B, fun φ hφ h0 => ?_⟩
  filter_upwards [GlobalTheory.SpehPair.eventually_spherical hV,
    LocSph.eventually_mem ((hV.aut φ hφ).level.mem_nhds (by simp))] with w hw hK
  refine GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (σ w).irred (hB w (hw _ (hσ w)))
    (fun f : GlobalTheory.LocDual.Maps V w (σ w) => f.1) (fun f => f.2.2) ?_ (GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_) h0
  · rw [GlobalTheory.LocDual.iSup_range_eq V hV.stable hV.irred w (σ w) (hσ w)]
    exact hφ
  · obtain ⟨g, rfl⟩ := hk
    exact hK g

end GlobalTheory.ResW
