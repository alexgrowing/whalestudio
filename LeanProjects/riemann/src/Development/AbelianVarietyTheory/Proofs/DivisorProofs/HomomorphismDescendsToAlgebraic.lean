import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodRatioAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealMultiplicationUniformization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSymmetricVeryAmple
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HomDescentQb

theorem exists_holUnif (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : ∃ L : LB A.left, Nonempty (HolUnif A L g) := by
  have := hA.proper
  have := hA.comm
  obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ A hA
  have hamp : Out.RelAmple A H :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
  exact ⟨_, GlobalTheory.RealMultChart.exists_holUnif_of_compact A g hg
    (GlobalTheory.RealMultChart.compactSpace_points A H hamp)
    (fun a n hn => GlobalTheory.RealMultChart.exists_pow_eq A hA a n hn)⟩

theorem hom_descends : ∀ (A₀ B₀ : Over (Sp Qb)) [GrpObj A₀] [GrpObj B₀] (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B]
    (p : A.left ⟶ A₀.left) (q : B.left ⟶ B₀.left) (g g' : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom →
    IsAbelianScheme B₀ → SmoothOfRelativeDimension g' B₀.hom →
    IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p → IsGrpPullback B B₀ (spMap (algebraMap Qb ℂ)) q →
    ∀ α : A ⟶ B, IsMonHom α → ∃ α₀ : A₀ ⟶ B₀, IsMonHom α₀ ∧ α.left ≫ q = p ≫ α₀.left := by
  intro A₀ B₀ _ _ A B _ _ p q g g' hA₀ hgA₀ hB₀ hgB₀ hp hq α hα
  haveI : Countable Qb :=
    (Algebraic.countable ℚ ℂ).mono (fun z hz => mem_algebraicClosure_iff.1 hz) |>.to_subtype
  haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA₀ hp
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB₀ hq
  have hgA : SmoothOfRelativeDimension g A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hp.1 hgA₀
  have hgB : SmoothOfRelativeDimension g' B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback hq.1 hgB₀
  obtain ⟨L, ⟨u⟩⟩ := exists_holUnif A g hA hgA
  obtain ⟨L', ⟨u'⟩⟩ := exists_holUnif B g' hB hgB
  exact GlobalTheory.CMLiePeriod.descend hA₀ hB₀ hA hB hgA hgB u u' hp hq α

end GlobalTheory.HomDescentQb
