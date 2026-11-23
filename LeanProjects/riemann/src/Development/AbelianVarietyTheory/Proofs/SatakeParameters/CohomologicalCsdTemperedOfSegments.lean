import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiTempered
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TemperedProductOfSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrableStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

theorem cohomologicalCsdTempered_of_caraianiTempered (hCar : CaraianiTempered) (hJac : TemperedProductOfSquareIntegrable)
    (hBer : EssSquareIntegrableSegments) : CohomologicalCsdTempered := by
  intro L _ _ _ n hn π hcsd hcoh y σ hloc
  haveI : CharZero (y.adicCompletion L) :=
    charZero_of_injective_algebraMap (algebraMap L (y.adicCompletion L)).injective
  have ht := hCar L n hn π hcsd hcoh y σ hloc
  obtain ⟨h, δ, hd, hδ, he⟩ :=
    (hJac (y.adicCompletion L) n (by omega) σ.V σ.ρ σ.smooth σ.irred).1 ht
  refine ⟨h, δ, hd, fun i => ⟨?_, ?_⟩, he⟩
  · refine (hBer (y.adicCompletion L) (δ i) (hδ i).1).1 ⟨1, isSmoothChar_one, ?_⟩
    rw [IrrGL.tw_one]
    exact (hδ i).2
  · exact GlobalTheory.T.unitarisable_of_square_integrable _ (δ i).1 _ (δ i).rep (δ i).2.rep.smooth (δ i).2.rep.irr (hδ i).2

end GlobalTheory.Published
