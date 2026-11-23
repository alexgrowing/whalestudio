import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiCrysOfConstituent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteContinuousCocyclesLocalGaloisRep

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwistedDualLoc

theorem continuous_T2O (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i)
    (hρ : Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :
    Continuous (T2O D.nd i ρ π) := by
  have h1 : Continuous fun g : GE D.nd => ((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) :=
    D.nd.chi_cont i 1
  have h2 : Continuous fun g : GE D.nd => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) :=
    GlobalTheory.LocalInv.eps_cont D.nd i
  have h3 : Continuous fun g : GE D.nd => ((ρ π g⁻¹ : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) := hρ.comp continuous_inv
  refine continuous_matrix fun a b => ?_
  have h : ∀ g : GE D.nd, T2O D.nd i ρ π g a b =
      ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) * (((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) *
        ((ρ π g⁻¹ : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) b a) := by
    intro g
    simp [T2O, WpO, rhoO, twistM, dualM]
  simp only [h]
  exact h2.mul (h1.mul (h3.matrix_elem b a))

theorem continuous_and_integral : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → Continuous (fun g => mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)) g) ∧ ∀ g a b, ‖((mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)) g a b : ↥LL'.1) : Om (D.nd.l i))‖ ≤ 1 := by
  intro D i w hw LL' h ρ π hρ
  have hc := GlobalTheory.WordJumpsCompare.continuous_loc D i w hw (T2O D.nd i ρ π) (continuous_T2O D i ρ π hρ)
  refine ⟨continuous_matrix fun a b => ?_, fun g a b => ?_⟩
  · exact Continuous.subtype_mk (continuous_subtype_val.comp (hc.matrix_elem a b)) _
  · exact GlobalTheory.LocalH1Finiteness.norm_toLL_le (D.nbr i w hw) _

end GlobalTheory.TwistedDualLoc
