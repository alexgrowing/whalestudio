import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CuspRep.UnrSat

open GlobalTheory.CuspRep GlobalTheory.LFun GlobalTheory.PRep

theorem exists_hasSatGL_locRep : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (v : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.LGrp.IsSpherical (π.locRep v) (GlobalTheory.LFun.KGL v a) → ∃ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL v (π.locRep v) B := by
  intro hF E _ _ _ a π v hs
  obtain ⟨σ, hσ, hadm⟩ := LocEx.exists_isLocComp hF E a π v
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs
  obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep E a).comp (locGL E a v)) σ.ρ σ.irred
    (fun f : LocSph.Maps π v σ => f.1) (fun f => f.2.2) (KGL v a : Set _) x.1 (fun e => hx0 (Subtype.ext e))
    (fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k hk))
    (by rw [LocSph.iSup_range_eq π v σ hσ]; exact x.2)
  have hsph : GlobalTheory.LGrp.IsSpherical σ.ρ (KGL v a) :=
    (Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩
  have hfin : FiniteDimensional ℂ (fixed σ.ρ (KGL v a)) :=
    hadm.2 _ (SatCompare.isOpen_isCompact_KGL v a).1 (SatCompare.isOpen_isCompact_KGL v a).2
  obtain ⟨B, hB⟩ := SatCompare.exists_hasSatGL ⟨σ.smooth, σ.irred⟩ hfin hsph
  exact ⟨B, HeightCounting.Blocks.hasSatGL_locRep hσ hB⟩

end GlobalTheory.CuspRep.UnrSat
