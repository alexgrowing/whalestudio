import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

noncomputable section

open Formalism.BasicNotions IsDedekindDomain NumberField Matrix Formalism.L2.DIV Formalism.IndefR.Lev GlobalTheory.StdFrames GlobalTheory.AdIsom
open scoped TensorProduct

namespace GlobalTheory.LevNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

@[reducible] def kField {E : Type} [Field E] [NumberField E] (Q : Pl E) : Field (kP Q) :=
  haveI := Q.isMaximal
  Ideal.Quotient.field Q.asIdeal

attribute [local instance] kField

def adPlaces (D : D7) : PlaceSys (EAf D) (Formalism.L2.Herm.intAf D.host.F D.host.E) (Pl D.host.E) (fun Q => kP Q)
    (fun Q => resS D.host.F Q) where
  K Q := Q.adicCompletion D.host.E
  O Q := Q.adicCompletionIntegers D.host.E
  p Q := cpt Q
  e Q := idem Q
  surj Q x := by
    classical
    obtain ⟨z, hz⟩ := GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)
      (⟨Pi.single Q x, by
        refine Filter.mem_of_superset (Set.finite_singleton Q).compl_mem_cofinite fun Q' h => ?_
        show (Pi.single Q x : ∀ v : Pl D.host.E, v.adicCompletion D.host.E) Q' ∈ Q'.adicCompletionIntegers D.host.E
        rw [Pi.single_eq_of_ne h]
        exact zero_mem _⟩ : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    refine ⟨z, ?_⟩
    change toAd D z Q = _
    rw [hz]
    exact Pi.single_eq_same (M := fun v : Pl D.host.E => v.adicCompletion D.host.E) Q x
  e_self Q := ((isPlIdem_iff Q _).1 (isPlIdem_idem Q)).1
  e_ne Q := ((isPlIdem_iff Q _).1 (isPlIdem_idem Q)).2
  ext a h := cpt_ext fun Q => by rw [h Q, map_zero]
  int a := mem_OA a
  fin a := Filter.eventually_cofinite.1 (toAd D a).2
  r_surj Q y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, resS_oToS Q x⟩
  r_ker Q s := (resS_eq_zero_iff_cpt Q s).trans
    ((Valuation.isEquiv_valuation_valuationSubring Valued.v).lt_one_iff_lt_one)

end GlobalTheory.LevNorm

end
