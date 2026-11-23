import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsStandardBasesLatticeAtPlaceOfAdaptedBasesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtLinAdaptedCoefEqStandardSeries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CombOfTied
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ShapeNormalisedThetaCombinationsDualBasesAtDStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormDgenEqOne
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical

namespace GlobalTheory.Ggeo.KerShapeD

theorem thetaKernelShapeAtD_ofKer_of_hyp_adapted : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D)
    (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → t.Adapted →
    ∀ ep be sg, OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hIn D L hT Gi Gl K Y cX ex t hH hA ep be sg
  intro u μ w hlev hcls i hi c c'
  have hpd : D.what₂.places.resChar w = D.host.d := by
    have h := hcls
    simp only [Host.cls, primeClass] at h
    split_ifs at h with h1 h2 h3 <;> first | exact h3 | cases h
  have hAd : AdPl D w := Or.inr (Or.inr hcls)
  have hlev' : LevFree Y u μ w := hlev
  obtain ⟨Pm, hBas, -, hConj, hTh⟩ := hA w hAd u μ hlev'
  have hStd : ∀ j, j ≤ D.R.m → ∀ cl, GlobalTheory.KerStd.StdBases D (t.ent.lam w) ((t.O u μ).lat j cl).1 (Pm j cl) :=
    fun j hj cl => GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat j cl).2.1 (fun τ => hBas j hj cl τ)
      (fun τ τ' h => hConj j hj cl τ τ' h)
  have hcomb := GlobalTheory.Ggeo.KerComb.comb_of_tied hIn.algT D L hT Gi Gl K Y cX ex t hH u μ w hlev' i hi c c'
  have hdg : IsDgen D t.cD := by
    rw [← t.O_dgen u μ]
    exact (t.O u μ).dgen_gen
  have hnorm : ∀ τ, ‖(fun _ => (1 : ℂ_[D.what₂.places.resChar w])) τ‖ ≤ ‖TaylorLogMetric.lamC (t.ent.lam w) (t.cD τ)‖ := by
    intro τ
    rw [GlobalTheory.EigenGenerator.norm_dgen_eq_one D t.cD hdg _ (t.ent.lam w) hpd τ]
    simp
  show OrbitPlaces.ShapeD D _ (t.ent.Th u μ w i c c')
  rw [hTh i hi c c', GlobalTheory.atLin_adCoef_eq_stdSer]
  exact GlobalTheory.T.shape_normalisedThetaCombinations_dualBases_at_d hIn D t.cc t.δ t.cc_ok t.δ_ok t.B t.χ t.χ_ok t.X t.seam t.seam_ok _ _ _ _ hcomb.1 _ (t.ent.lam w) hpd
    t.cD hdg (Pm i c) (Pm (i + 1) c') _ (hStd i hi.le c) (hStd (i + 1) hi c') hnorm _ hcomb.2

end GlobalTheory.Ggeo.KerShapeD
