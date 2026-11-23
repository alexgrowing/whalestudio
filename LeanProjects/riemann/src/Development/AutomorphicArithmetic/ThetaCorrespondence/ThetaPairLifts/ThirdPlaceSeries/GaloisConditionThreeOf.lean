import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.JointConditionOfConstituentConditionSplit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.DistinctAbsIrredConstituents

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
end
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo
end GlobalTheory.CrysFromGTwo
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys
end GlobalTheory.DualTwistCrys
end
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}
end GlobalTheory.CrysChiOne
end
section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open NumberField IsDedekindDomain
theorem galois_condition_three_of_alt_alt (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (h32 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (hr : GoodR D.nd i r)
    (hdec : Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))))
    (hHG : HG D.nd D.naut i) (hN9 : ResidualIrreducibleRankR D) (hB : LitBurnside (GE D.nd))
    (hc : AbsIrreducibleDistinct D i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG3 (D := D) i r ρ π := by
  have h2 : ∀ x (g : GE D.nd), (mapM (IsLocalRing.residue (D.nd.O i)) (rO D.nd i r x) g).charpoly =
      (mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π) g).charpoly *
        ∏ c ∈ Finset.Icc 1 D.R.t,
          (X - C (IsLocalRing.residue (D.nd.O i) ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))) := by
    intro x g
    have e1 := (_root_.UpperTheory.GalS.g3' ((h32 i).2.2 r hr).2.2.1).2 x π g
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i))) (charpoly_of_decomp D i r ρ π hdec g)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    refine e1.trans (e2.trans ?_)
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  refine ⟨hc, h2, ?_⟩
  have hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π)) := by
    refine ⟨isOpen_ker_redRep D i _ hcont, ?_⟩
    intro x w hw B σ hB' hσ
    rw [← (hr x).2.2 w hw B σ hB' hσ, ← Matrix.charpoly_map]
    exact (h2 x σ).symm
  have h3 := hB (D.nd.l i) D.R.r _ (hN9 i hHG _ hrb).1
  exact span_descent (D.naut.kFbar i) (fun g => mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π) g) h3
end Formalism.MainNotions.N
end
section
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
