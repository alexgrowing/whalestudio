import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HostFieldTwoConjugatePlacesOverTwoStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthAtTwoOfUnscaledDepthBoundStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValuationBoundAtResidueCharacteristicStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SizesBoundAtTwoFirstRowsWeightsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem GlobalTheory.RunDepth.leafDepth2_run : (∀ (p : ℕ) [Fact p.Prime], AvFSt p) → (∀ (p : ℕ) [Fact p.Prime], HTFSt p) → ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → LeafDepth2 N O := by
  intro hAv hHT D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg _ hx hb tF
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hn : ∀ j, InR D j → 2 * D.R.f * D.R.r ≤ (lR Tp hK j).n := by
    intro j _
    show _ ≤ Tp.nWn
    refine le_trans ?_ Tp.nW_lo.1
    nlinarith [Nat.mul_le_mul_left (D.R.f * D.R.r) (show 2 ≤ D.R.r + 1 by omega)]
  have hL : LawsPi T (depOf T EX Tp hK) := lawsPi_depRun hM EX _ _ _ _ _ hn
  refine GlobalTheory.T.depthAtTwo_of_unscaled_depth_bound D.host.E T.Q.H T.Q.l T.Q.Dw T.Q.Xo T.Q.c (depOf T EX Tp hK) K Bs Df S P oc O ι N (numOf D L)
    hR.E_eq hR.σ_eq hR.T_eq ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ hL.piSplit hPg tF
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ ?_
  intro la hla j
  obtain ⟨Ap, hAp0, hAp, hle⟩ := GlobalTheory.T.sizes_bound_at_two_first_rows_weights D L Pm Tp hK T.Q hM.pins hx hb O.C hPg.1 (ι j) (hR.inR j)
  haveI : Fact (resCharOf la).Prime := ⟨Crude.resCharOf_prime la⟩
  obtain ⟨hsp, h2, hvd, hup⟩ := GlobalTheory.T.hostField_two_conjugate_places_over_two D T.Q.H hM.pins.1.1 (resCharOf la) (hR.sm_eq ▸ hla)
  refine ⟨_, ?_, GlobalTheory.T.unscaledDepth_le_placeOverTwo (resCharOf la) (hAv _) (hHT _) D.host.E T.Q.H (T.Q.Dw (ι j)) T.Q.l (T.Q.Xo (ι j)) T.Q.c
    hR.star_eq D.R.f (D.host.vdH (resCharOf la)) hvd hsp h2 la rfl _ _ _ (fun τ _ _ h => (hL.wts _ (hR.inR j)).1 τ h)
    (DepthTie.card_of_laws T _ hL hM.pins (ι j) (hR.inR j)) Ap hAp0 hAp⟩
  unfold OnObj.sC OnObj.Se
  rw [hR.T_eq, hR.m_eq, hR.vd_eq, hR.wt_eq, hR.f_eq, hR.Sc_eq, hR.eta_eq]
  refine le_trans (mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) (Nat.cast_nonneg _)) hle
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hAp0
