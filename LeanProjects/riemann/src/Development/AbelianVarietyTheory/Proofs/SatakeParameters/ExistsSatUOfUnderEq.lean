import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL
namespace GlobalTheory.CongL.SatConj

theorem exists_satU_of_under_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w u : HeightOneSpectrum (𝓞 E), IsSplitAt w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → (∃ B, SatU U w B) → ∃ B, SatU U u B := by
  intro E _ _ _ a U hU w u hw hu ⟨B, σ, ⟨hirr, f, hf0, hfm, hf⟩, hS⟩
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS.1
  have hf' : ∀ g x, f (σ.ρ g x) = RU E a (GlobalTheory.SplitPts.locPt hw g).1 (f x) := fun g x => by
    have := hf (GlobalTheory.SplitPts.locPt hw g) x
    simpa [GlobalTheory.SplitPts.cLoc_locPt hw g] using this
  have hinj : Function.Injective f := by
    have hk := ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hirr).2 (LinearMap.ker f) (fun g x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hf', hx, map_zero])
    rcases hk with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exact absurd (LinearMap.ker_eq_top.1 h) hf0
  have hloc : locU a u = locU a w := by
    unfold locU
    rw [hu]
  have hsu : IsSplitAt u := by
    by_cases h : u = w
    · exact h ▸ hw
    · exact ⟨w, Ne.symm h, hu.symm⟩
  have hKw : ∀ x : UA E a, cLoc u x ∈ GlobalTheory.LFun.KGL u a → cLoc w x ∈ GlobalTheory.LFun.KGL w a := by
    intro x hx
    rcases GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc hu with rfl | rfl
    · exact hx
    · have := GlobalTheory.BCT.GlobLev.integral_conjSrc x _ hx
      rwa [GlobalTheory.SplitPts.conjSrc_conjSrc_cm] at this
  have hfix : ∀ x ∈ locU a u, cLoc u x ∈ GlobalTheory.LFun.KGL u a → RU E a x (f v) = f v := by
    intro x hx hk
    have hx' : x ∈ locU a w := hloc ▸ hx
    have h1 : σ.ρ (cLoc w x) v = v := by simpa using hv ⟨_, hKw x hk⟩
    have h2 := hf ⟨x, hx'⟩ v
    rw [← h2]
    exact congrArg f h1
  obtain ⟨σ', S, hloc', hS', -⟩ := GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec E a U hU u hsu (f v) (hfm v)
    (fun h => hv0 (hinj (h.trans (map_zero f).symm))) hfix
  exact ⟨S, σ', hloc', hS'⟩

end GlobalTheory.CongL.SatConj
