import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianShortExact

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeSeqSheaf

theorem exists_shortExact (hP : GlobalTheory.CovTop.Hypotheses2) (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hc : ∃ c, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c)
    (H : T.Modules) (hH : GlobalTheory.DeRhamSheaf.IsDeRhamSheaf A H) :
    ∃ S : ShortComplex T.Modules, S.ShortExact ∧ Nonempty (S.X₂ ≅ H) ∧
      Nonempty (S.X₁ ≅ GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) ∧
        Nonempty (S.X₃ ≅ GlobalTheory.VB.dual (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A)) := by
  obtain ⟨e, he⟩ := (GlobalTheory.HodgeSeqSheaf.isDeRhamSheaf_iff A H).1 hH
  obtain ⟨i, hi⟩ := GlobalTheory.T.hodge_into_de_rham_injective hP T A g hA hg H e he
  obtain ⟨β, hβ, w⟩ := GlobalTheory.PrincipalPolPairing.exists_iso_dual hP.p5 T A g hA hg hc H e he _ i
    fun V hV x => by
      rw [← (hi V hV).2.1]
      exact LinearMap.mem_range_self _ x
  have hV := GlobalTheory.DeRhamSheaf.VB.isVB_of_isDeRhamSheaf hP.p5 T A g hA hg H hH
  haveI := hg
  have hF := GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.isVB_hodge A hA g
  exact ⟨ShortComplex.mk i (β ≫ GlobalTheory.VB.dualMap i) w,
    GlobalTheory.VB.lagrangian_shortExact T g _ H hF hV i β hβ (fun V hV => ⟨(hi V hV).1, (hi V hV).2.2⟩) w,
    ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩

theorem main : GlobalTheory.CovTop.HypothesesXH → GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.PoincareDeRhamDuality → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∃ c, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c) →
    ∀ H : T.Modules, GlobalTheory.DeRhamSheaf.IsDeRhamSheaf A H →
      ∃ S : ShortComplex T.Modules, S.ShortExact ∧ Nonempty (S.X₂ ≅ H) ∧
        Nonempty (S.X₁ ≅ GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A) ∧ Nonempty (S.X₃ ≅ GlobalTheory.VB.dual (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A)) :=
  fun _ hP _ T A _ g hA hg hc H hH => exists_shortExact hP T A g hA hg hc H hH

end GlobalTheory.HodgeSeqSheaf
