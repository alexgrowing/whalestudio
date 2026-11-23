import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsRec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOrthProjPerpMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodLiftOntoOfBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnOfOnWithCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnClausesWithErrorOfSplitPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPlacesBoundChainTwoRunChainStatement
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.BigOn.OntoPath

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem onto_path : RunsSt → RatSt → GeoSt → (AtRec fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) → TwistSt →
    ShareSt → BadSt → ExpSt → PageSt → OntoX := by
  intro hRuns hRat hGeo hRank hTw hSh hBad hExp hPage
  have H := ((((((((hRuns.and hRat).and hGeo).and hRank).and hTw).and hSh).and hBad).and hExp).and hPage)
  refine Closed.imp H ?_
  intro eps Fm CH _ H _
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨xR, hR⟩, ⟨xQ, hQ⟩⟩, ⟨cG, hG⟩⟩, ⟨cK, hK⟩⟩, ⟨cT, hT⟩⟩, ⟨cS, hS⟩⟩, ⟨cB, hB⟩⟩, ⟨cE, hE⟩⟩, ⟨cP, hP⟩⟩ := H
  set c0 : ℝ := max (max (max (max cG cK) (max cT cS)) (max (max cB cE) cP)) 1 with hc0
  let c : OnConst := ⟨c0, 14, 66 * c0 + 4⟩
  have hcb : OnPage.ConstBad c := ⟨le_rfl, le_rfl⟩
  have l1 : cG ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l2 : cK ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l3 : cT ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l4 : cS ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l5 : cB ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l6 : cE ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l7 : cP ≤ c.C := le_trans (by simp) (le_max_left _ _)
  obtain ⟨x1, h1⟩ := hG c l1 hcb
  obtain ⟨x2, h2⟩ := hK c l2 hcb
  obtain ⟨x3, h3⟩ := hT c l3 hcb
  obtain ⟨x4, h4⟩ := hS c l4 hcb
  obtain ⟨x5, h5⟩ := hB c l5 hcb
  obtain ⟨x6, h6⟩ := hE c l6 hcb
  obtain ⟨x7, h7⟩ := hP c l7 hcb
  refine ⟨2 * max c.CE 0, by positivity,
    max (max (max xR xQ) (max x1 x2)) (max (max x3 x4) (max (max x5 x6) x7)), ?_⟩
  intro x hx hx0 i p hp hm C hCC
  have a0 : max xR xQ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx0)
  have b0 : max x1 x2 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx0)
  have c1 : max x3 x4 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx0)
  have d0 : max (max x5 x6) x7 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx0)
  obtain ⟨r, hr, hown⟩ := hR x hx (le_trans (le_max_left _ _) a0) i p hp hm
  have hrat := hQ x hx (le_trans (le_max_right _ _) a0) i p hp hm
  have hct := hm.2.1
  obtain ⟨O, hO⟩ := exists_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ (Fm.parT x hx i) (Fm.ex x hx i).kap_def
    (Fm.ex x hx i).errX r c hct.canon hct.halfEX hr
  have hrec : RecAt p (Fm.parT x hx i) r O := ⟨hO, hown⟩
  obtain ⟨gSup, gSpan, gLem, gData, gIdx, gDepth⟩ := h1 x hx (le_trans (le_max_left _ _) b0) i p hp hm r O hrec
  have kRank := h2 x hx (le_trans (le_max_right _ _) b0) i p hp hm r O hrec
  have tTw := h3 x hx (le_trans (le_max_left _ _) c1) i p hp hm r O hrec
  have sSh := h4 x hx (le_trans (le_max_right _ _) c1) i p hp hm r O hrec
  have bBad := h5 x hx (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) d0) i p hp hm r O hrec
  have eExp := h6 x hx (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) d0) i p hp hm r O hrec
  obtain ⟨pPage, pSizes, pX, pBad, pLev, pY, -, pE1u, pTie⟩ :=
    h7 x hx (le_trans (le_max_right _ _) d0) i p hp hm r O hrec
  have hL : Links2 p := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hp hm.1
  obtain ⟨hC, hOk, hU, hBL, hRR, -⟩ := hL
  have hI := GlobalTheory.ClassSumIdentity.leafIdentity_of_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1 hOk hC hU hrat
  have hT2 := GlobalTheory.BaseTwistIncl.leafTW2_of_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1 hOk hC hU hBL hrat
  obtain ⟨dG, dR, d2, dL⟩ := gDepth c.CE CH
  obtain ⟨err, herr⟩ := GlobalTheory.T.twistedPlacesBoundChain_twoRunChain _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1
    ((R2 p).num (F2 p) c.CE CH) c.CE hOk hC.grp.levels hC.grp.chiW hC.models hC.tup.mu_conj hC.thP.thG hU hBL hrat hRR
    pLev pY gSup gSpan gLem gIdx gData kRank hI hT2 tTw sSh bBad dG dR d2 dL pPage pSizes pX pBad (eExp c.CE CH) le_rfl
    (pTie c.CE CH)
  obtain ⟨hon, hD⟩ := GlobalTheory.T.onClauses_with_error_of_splitPart _ _ _ _ _ _ _ _ _ _ p c.CE CH err herr
  have hDpos : 0 < (p.S false).D := by rw [hD]; exact hRR.1
  have hJ : ∀ w ∈ (p.S false).Tw, ∀ j, 0 ≤ p.Z.J0 ((p.S false).μ w) w j := (eExp C CH).1
  exact on_of_onWith_canonical _ _ _ (p.S false) p.Z c.CE C CH CH err hDpos pE1u
    (le_trans (mul_le_mul_of_nonneg_left (le_max_left c.CE 0) zero_le_two) hCC) hJ (fun w j => p.err_eq w j) hon

end GlobalTheory.BigOn.OntoPath

end
