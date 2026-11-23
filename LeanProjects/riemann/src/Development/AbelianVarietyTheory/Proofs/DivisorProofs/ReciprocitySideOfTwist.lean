import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlockTriangularTwoBlockSizesOfLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRowsStatement
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.BigOn.Exp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem recSide_of_twAdm : TwAdm → RecSide := by
  intro hA
  refine Formalism.MainNotions.Closed.imp hA fun Fm CH _ ⟨x0, H⟩ => ⟨x0, fun x hx h0 i p hr hm w hw j Z hRat => ?_⟩
  obtain ⟨hOK, -, -⟩ := H x hx h0 i p hr hm w hw j
  have hL := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hU : p.R.toRealDat.LUnif := hL.2.2.1
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have T := Z.tie ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  have hAR := GlobalTheory.SeriesTie.actRead_realRd _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ Z.ρ Z.good
    ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) Z.pin hU hW
  have hS : Formalism.MainNotions.IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun a => hr.ties.data _ j _ a fun u => ?_
    have hm0 := GlobalTheory.ExportType.thetaSeriesDatum_mem_levelTypeForms T hAR a
    exact sub_eq_zero.1 (LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hm0 u))
  have hb : baseSet (rdAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))) =
      Set.range ((Fm.D x i).nexp.th ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1) ((Fm.ex x hx i).nch.sd w)) :=
    (range_th T).symm
  have ht : (⋃ a ∈ Formalism.MainNotions.IntegralHeckeForms.SgJ (Fm.D x i).nexp (twE Fm x hx i) ((Fm.ex x hx i).nch.twI w) ((j : ℕ) + 1)
        ((Fm.ex x hx i).nch.sd w),
        (Fm.D x i).nexp.thPsi _ _ _ ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w)
          (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) a) =
      twSet Z.good (rdAt p w j Z.good (Z.ν ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w))) ((Fm.ex x hx i).nch.k' w)
        ((Fm.ex x hx i).nch.Q w) (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w) := by
    rw [hS, Set.biUnion_univ, iUnion_thPsi T hOK]
    ext y
    exact ⟨fun ⟨s, h, P, hd, _, hy⟩ => ⟨s, h, P, hd, hy⟩, fun ⟨s, h, P, hd, hy⟩ => ⟨s, h, P, hd, hRat.1 s h P hd, hy⟩⟩
  refine ⟨?_, ?_⟩
  · unfold baseLat
    rw [hb, hS, Set.image_univ, ← Set.range_comp]
    rfl
  · unfold twLat
    rw [ht]

end GlobalTheory.BigOn.Exp

end
