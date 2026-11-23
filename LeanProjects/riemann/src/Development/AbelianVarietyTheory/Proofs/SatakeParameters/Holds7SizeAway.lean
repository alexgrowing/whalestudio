import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.PureDegreeZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedGaloisRepNarrow7
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TaylorYoshidaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolySmulScaleRoots
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentUnitarisableTwist
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiTempered
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsExhaustionGLHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfIrred
import Development.DiscreteGroups.GlobalIrreducibility.LConvFinal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideFurther
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapNormEqOfMapPowEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open GlobalTheory.GalCut7

noncomputable section

namespace GlobalTheory.GalCut7.SizeAway

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

open GlobalTheory.ResW in

theorem isUnitarisable (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (ha : 1 ≤ a)
    (π : CuspSub E a) (wt : ℤ) (hw : IsWeight π wt) (w : HeightOneSpectrum (𝓞 E)) (σ) (hσ : π.IsLocComp w σ) :
    GlobalTheory.SmGL.IsUnitarisable ((algNorm σ).nu (((wt : ℝ) / 2 : ℝ) : ℂ)).rep := by
  set t : ℝ := ((a : ℝ) - 1 - wt) / 2 with ht
  have hr := GlobalTheory.UnitLocWeight.rexp_eq ha hw
  have hu : (π.twist (nu E (-t))).IsUnitary := by
    have e := (letter_centralExponent E ⟨a, π⟩).2.2.1 ha (-t)
    refine ((rexp_eq_zero_iff_isUnitary E (tw ⟨a, π⟩ (-t)) ha).1.1 ?_)
    rw [e, hr]; ring
  have hU := isUnitarisable_of_isLocComp_cusp E a _ ha hu w _ (hσ.twist (nu E (-t)))
  have hloc : (nu E (-t)).loc w = GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ) :=
    GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (-t)) w
  set σ' := σ.twist (CuspSub.locDet a (nu E (-t)) w) (CuspSub.isOpen_ker_locDet (nu E (-t)) w) with hσ'
  have key : (algNorm σ).nu (((wt : ℝ) / 2 : ℝ) : ℂ) = IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
    have e1 : (((1 - (a : ℝ)) / 2 : ℝ) : ℂ) + (((wt : ℝ) / 2 : ℝ) : ℂ) = ((-t : ℝ) : ℂ) := by
      rw [ht]; push_cast; ring
    unfold algNorm
    rw [IrrGL.nu_nu, e1]
    unfold IrrGL.nu
    rw [IrrGL.tw_of]
    refine IrrGL.of_eq_of.2 ⟨?_⟩
    have e2 : GlobalTheory.SmGL.twist σ.ρ (GlobalTheory.SmGL.detChar (Fin a) (GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ))) =
        σ'.ρ := by
      ext g v
      change ((GlobalTheory.SmGL.detChar (Fin a) (GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ)) g : ℂˣ) : ℂ) • σ.ρ g v =
        ((CuspSub.locDet a (nu E (-t)) w g : ℂˣ) : ℂ) • σ.ρ g v
      congr 2
      simp [CuspSub.locDet, hloc, GlobalTheory.SmGL.detChar]
    rw [e2]
    exact .refl _
  rw [key]
  exact GlobalTheory.GenericUnitary.isUnitarisable_of_equiv (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred) hU

end GlobalTheory.GalCut7.SizeAway

end
