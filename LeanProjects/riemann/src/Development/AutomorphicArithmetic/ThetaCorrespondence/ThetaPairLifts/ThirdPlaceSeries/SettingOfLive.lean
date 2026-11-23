import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.JointConditionOfConstituentConditionSplit
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResidualCharpolyEq
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
theorem setting_of_live_alt_alt : GlobalTheory.TwSys.Cheb → ∀ (D : D7), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc,
    ZDecomp D.nd i → Live D.nd i → ∃ (rep : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
      GoodR D.nd i rep ∧ GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.HidaSetting D.R.t (D.nd.T i) (D.nd.Z i) rep ρ (D.nd.chi i) := by
  intro hC D h32 hS i hZ hL
  classical
  obtain ⟨rep, hr⟩ := (h32 i).1.2
  have hG1 := ((h32 i).2.2 rep hr).1
  have hG3 := _root_.UpperTheory.GalS.g3' ((h32 i).2.2 rep hr).2.2.1
  have hJ := UpperTheory.GalS.jointCondition_of_constituentCondition_split D i rep hr (hG3.1 (Or.inr hL)) (hS i)
  let ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) := fun x =>
    if hx : x ∈ D.nd.Z i then Classical.choose (hZ x hx (rep x) (hr x)) else 1
  have hρ : ∀ x ∈ D.nd.Z i, ∃ e, IsDecomp (t := D.R.t) (rep x) (ρ x) (D.nd.chi i) e := by
    intro x hx
    have := Classical.choose_spec (hZ x hx (rep x) (hr x))
    simp only [ρ, dif_pos hx]
    exact this
  obtain ⟨π, hπ, r0, ρ0, hr0, h0, habs⟩ := hL
  refine ⟨rep, ρ, hr, D.nd.T_local i, D.nd.T_sep i, fun x => ?_, fun h d => ?_,
    hJ, hG3.2, hρ, fun x hx => ?_⟩
  · have hss := (hr x).2.1
    intro W hW
    obtain ⟨W', h1, h2⟩ := hss W fun g v hv => hW g v hv
    exact ⟨W', fun g v hv => h1 g v hv, h2⟩
  · obtain ⟨f, hf⟩ := hG1 h d
    have : (fun x => (mat (rep x) h).charpolyRev.coeff d) = (f : D.nd.X i → D.nd.O i) :=
      funext fun x => (hf x).symm
    rw [this]
    exact f.2
  · have hpos := pos_of_absIrrSub _ habs
    haveI : Nonempty (Fin D.R.r) := ⟨⟨0, hpos⟩⟩
    refine absIrrSub_of_span_eq_top hpos _ ?_
    refine span_eq_top_of_trace_eq _ (mapRep (IsLocalRing.residue (D.nd.O i)) ρ0) (fun g => ?_)
      (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs)
    rw [mat_mapRep, mat_mapRep, Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff,
      _root_.GlobalTheory.AbsoluteIrreducibilityOfTraceSpan.residual_charpoly_eq_alt_alt hC D h32 i rep hr x π (ρ x) ρ0 (hρ x hx) r0 hr0 h0 g]
end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end
section
end
end
end
