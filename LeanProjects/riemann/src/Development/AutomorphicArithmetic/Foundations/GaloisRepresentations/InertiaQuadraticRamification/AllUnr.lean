import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticNormHeckeCharRamifiedBelowRamifiedPrime
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem unramifiedAt_of_dec_fixes (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)) (hA : IsPlaceOver A w)
    (hfix : ∀ g ∈ Dec (F := maximalRealSubfield L) A, Fixes L g) :
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  haveI : IsAlgClosure (maximalRealSubfield L) Ω :=
    ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.trans _ L Ω⟩
  have hAv : IsPlaceOver A (w.under (𝓞 (maximalRealSubfield L))) := fun x => by
    rw [IsScalarTower.algebraMap_apply (maximalRealSubfield L) L Ω]
    exact hA (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x)
  obtain ⟨-, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A (w.under (𝓞 (maximalRealSubfield L))) w hAv hA
    fun σ hσ => hfix σ (Ine_le_Dec A hσ)
  exact Ideal.ramificationIdx_eq_one_iff.1 he

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.allUnr :
    SplitIff → AllUnr := by
  intro hS Y Ω _ _ _ _ _ T Q hQ w
  by_cases hw : IsSplitAt w
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact unramifiedAt_of_dec_fixes ↥Q.K Ω A w hA ((hS ↥Q.K Ω A w hA).1 hw)
  · exact (hQ.2.2.2.1 w hw).2.1
