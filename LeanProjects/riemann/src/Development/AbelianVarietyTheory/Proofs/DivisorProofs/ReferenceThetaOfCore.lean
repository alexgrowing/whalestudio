import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSecOfMemCuspWWtZ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientWeightGapBoundsStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum

theorem refTheta_of_refCore : Size → RefCore → RefTheta := by
  intro hS hR
  have hW := GlobalTheory.T.quotient_weight_gap_bounds hS
  refine Closed.imp (Closed.and hR hW) fun _ _ _ ⟨⟨C, hC, a, h⟩, _, _, b, h'⟩ =>
    ⟨C, hC, max a b, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  obtain ⟨S, e, s, hPS, hT, hq⟩ := h x hx ((le_max_left _ _).trans hle) ι p hp i hi u1 hu
  have hD := (h' x hx ((le_max_right _ _).trans hle) ι p hp i hi u1 hu).2.2.2.2.2.2.1
  refine ⟨S, e, s, hPS, hT, fun q hq' => le_trans ?_ (hq q hq')⟩
  exact refExp_vp_cover_le _ p.T _ Y _ _ p.fw.laws ⟨by omega, by omega⟩ hY.1 _ _ hD _ q hq'

end GlobalTheory.RefSum

end
