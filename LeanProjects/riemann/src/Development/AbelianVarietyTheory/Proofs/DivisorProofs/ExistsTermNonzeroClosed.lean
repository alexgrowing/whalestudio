import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTermsStatement
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.NotIsThetaOfNonunit
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_term_nonzero_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (Y : Ext D.toPre), ∃ (b : D.toPre.SecB 1 0) (τ : SecK D.toPre.P.L Y.q.left 1)
      (y : Y.H.left), IsTermOf Y b τ ∧ Y.H.hom y = closedPoint R ∧ y ∈ nonzeroLocus τ := by
  intro R _ _ _ hB D Y
  haveI : IsNoetherianRing R := hB.1.1
  obtain ⟨-, -, hsurj, -, hterm⟩ := GlobalTheory.T.torusExtension_smooth_affine_surjective_fourierTerms R D.toPre Y
  obtain ⟨th, x, hx, hn⟩ :=
    GlobalTheory.ThetaSectionTest.exists_nonzero_closed GlobalTheory.abelianSchemeLaws_all.1.secBaseChange D.toPre
  obtain ⟨τ, hτ⟩ := hterm 1 0 th
  obtain ⟨y, rfl⟩ := Y.q.left.surjective x
  refine ⟨th, τ, y, hτ, ?_, ?_⟩
  · rw [← hx, ← Scheme.Hom.comp_apply, Over.w]
  · obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' D.toPre.P.isLB y
    have e := hτ Y.H (𝟙 _) y J hJ
    have hu : IsUnit (sval th (𝟙 Y.H ≫ Y.q).left y J) := by
      rw [Category.id_comp]
      exact GlobalTheory.ThetaUnit.isUnit_sval th _ y hn hJ
    have hτu : IsUnit (sval τ (𝟙 Y.H : Y.H ⟶ Y.H).left y J) := by
      rw [e]; exact hu.mul (Units.isUnit _)
    rw [Over.id_left] at hτu
    exact (GlobalTheory.SectionBaseChange.mem_nonzeroLocus τ _).2
      ⟨_, hJ.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left),
        (GlobalTheory.ThetaUnit.isUnit_gs_iff _ y _ (hJ.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left)) _).1 hτu⟩

end GlobalTheory.Mum
