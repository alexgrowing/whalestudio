import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem IntFam.existsUnique_over : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ)
    (F₀ : IntFam I D k) (F : Type) [Field F] [Algebra (FractionRing R) F], ∃! s : Fam D F k, F₀.Over s := by
  intro R _ _ I D k F₀ F _ _
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hL := D.P.isLB
  have hext : ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F₀.F.s α)
      (D.famφB α) (DegPre.famε k) (F₀.f α) (DegPre.prB D (FractionRing R)).left 1 := fun α => by
    have h := F₀.ext α
    have e : scal (DegPre.BF D (FractionRing R)).hom (1 : R) = 1 := by
      unfold scal
      rw [map_one, map_one]
    rwa [e] at h
  have hov : F₀.Over (famPull D (FractionRing R) F hG k F₀.F) := fun α => by
    refine SectionScalarValuation.secScal_of_sval hL fun y J hJ => ?_
    show _ = sval (termPull D (FractionRing R) F k α (F₀.F.s α)) (𝟙 _) y J
    refine Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm
    refine Eq.trans ?_ (SectionScalarValuation.secScal_sval (hext α) _ y hJ)
    congr 1
    rw [Category.assoc, ← Over.comp_left, famMap_snd]
  refine ⟨_, hov, fun s hs => fam_ext fun α j => congrArg (fun q => LB.Sec.f q j)
    (sec_ext' hL fun y J hJ => ?_)⟩
  rw [← SectionScalarValuation.secScal_sval (hs α) (𝟙 _) y hJ, SectionScalarValuation.secScal_sval (hov α) (𝟙 _) y hJ]

end GlobalTheory.Mum
