import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAndResidualTrivComplexConj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CharDualDense

theorem t2_O0 {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) :
    T2Space (X.O0 i) :=
  (IsAdic.isHausdorff_iff (X.twistBaseCoefficientRing_isAdic i)).1 inferInstance

theorem finite_S0_conj {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) :
    ((X.S0 i : Set (PlE D.host)) ∪ {P | ∃ P' ∈ X.S0 i, IsConjPl D.host P P'}).Finite := by
  refine (X.S0 i).finite_toSet.union ?_
  refine ((X.S0 i).finite_toSet.biUnion (t := fun P' => {P | IsConjPl D.host P' P}) fun P' _ => ?_).subset ?_
  · exact (show ({P | IsConjPl D.host P' P} : Set (PlE D.host)).Subsingleton from
      fun a ha b hb => GlobalTheory.TwistDet.isConjPl_unique ha hb).finite
  · rintro P ⟨P', hP', hc⟩
    exact Set.mem_biUnion (x := P') hP' (GlobalTheory.TwistDet.isConjPl_symm hc)

theorem charDual_of_frobDual : ∀ (D : D7), GlobalTheory.TypeLeaf.FrobDense D → ∀ (i : D.ntw.Tw) (s : D.ntw.Sig i),
    FrobDual i s → CharDual i s := by
  intro D hF i s hFD g g' hg'
  haveI := t2_O0 D.ntw i
  have e : g' = GlobalTheory.TwistDet.cConj D.ntw g := by
    ext x
    rw [hg', GlobalTheory.TwistDet.cConj_apply]
  subst e
  refine GlobalTheory.TypeLeaf.charpoly_eq_of_dense (Gen.GE D.nd) (D.ntw.O0 i) D.R.r
    (fun g => Tdual i s (GlobalTheory.TwistDet.cConj D.ntw g))
    (fun g => ((((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t) • Tmat i s g)) _
    (hF _ (finite_S0_conj D.ntw i))
    ((GlobalTheory.PrimeToInertia.continuous_Tdual i s).comp (GlobalTheory.ResConjTriv.continuous_cConj D.ntw)) ?_ ?_ g
  · have h1 : Continuous fun g : Gen.GE D.nd => ((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) :=
      (GlobalTheory.PrimeToInertia.continuous_algebraMap_padicInt _ (D.ntw.twistBaseCoefficientRing_isAdic i) (GlobalTheory.PrimeToInertia.l_mem i)).comp
        (Units.continuous_val.comp (continuous_cycZ D.host.E D.nd.Om (D.ntw.l i)))
    exact (h1.pow _).smul (GlobalTheory.PrimeToInertia.continuous_Tmat i s)
  · rintro σ ⟨w, hwT, hsp, B, hB, hσ⟩
    refine hFD w (fun h => hwT (Or.inl h)) hsp (fun P' hc h => hwT (Or.inr ⟨P', h, hc⟩)) B hB σ _ hσ
      (GlobalTheory.TwistDet.cConj_apply D.ntw σ)

end GlobalTheory.CharDualDense

end
