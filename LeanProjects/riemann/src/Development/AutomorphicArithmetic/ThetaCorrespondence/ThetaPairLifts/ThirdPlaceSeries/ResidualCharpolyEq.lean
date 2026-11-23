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
end Formalism.MainNotions.N
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
theorem residual_charpoly_eq_alt_alt (hC : GlobalTheory.TwSys.Cheb) (D : D7) (h32 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (i : D.nd.Loc)
    (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i rep)
    (x π : D.nd.X i) (ρx ρ0 : GE D.nd →* GL (Fin D.R.r) (D.nd.O i))
    (hx : ∃ e, IsDecomp (t := D.R.t) (rep x) ρx (D.nd.chi i) e)
    (r0 : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) (hr0 : IsHeckeGalois D.nd i π r0)
    (h0 : ∃ e, IsDecomp (t := D.R.t) r0 ρ0 (D.nd.chi i) e) (g : GE D.nd) :
    ((mat ρx g).map (IsLocalRing.residue (D.nd.O i))).charpoly =
      ((mat ρ0 g).map (IsLocalRing.residue (D.nd.O i))).charpoly := by
  classical
  have hG3 := (_root_.UpperTheory.GalS.g3' ((h32 i).2.2 rep hr).2.2.1).2 x π g
  obtain ⟨ex, hex⟩ := hx
  obtain ⟨e0, he0⟩ := h0
  have dx := charpoly_of_decomp D i rep (fun _ => ρx) x ⟨ex, hex⟩ g
  have d0 := charpoly_of_decomp D i (fun _ => r0) (fun _ => ρ0) π ⟨e0, he0⟩ g
  have hc := charpoly_eq_of_isHeckeGalois hC D i rep hr π r0 hr0 g
  set res := IsLocalRing.residue (D.nd.O i)
  set P : (D.nd.O i)[X] := ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))
  have hP : (P.map res) ≠ 0 := by
    apply Polynomial.Monic.ne_zero
    apply Polynomial.Monic.map
    exact Polynomial.monic_prod_of_monic _ _ fun c _ => Polynomial.monic_X_sub_C _
  have e1 : ((mat ρx g).map res).charpoly * P.map res = ((mat ρ0 g).map res).charpoly * P.map res := by
    rw [Matrix.charpoly_map, Matrix.charpoly_map, ← Polynomial.map_mul, ← Polynomial.map_mul]
    have ex' : (rO D.nd i rep x g).charpoly = (mat ρx g).charpoly * P := dx
    have e0' : (mat r0 g).charpoly = (mat ρ0 g).charpoly * P := d0
    rw [← ex', ← e0', ← hc, ← Matrix.charpoly_map, ← Matrix.charpoly_map]
    exact hG3
  exact mul_right_cancel₀ hP e1
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
