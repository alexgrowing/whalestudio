import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtMain
import Formalism.LocalToGlobal.ProjectiveLattices.RegularityR1ValuedPoints
import Formalism.LocalToGlobal.ProjectiveLattices.HeightF1OfData
import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.LawA13OfContinuous
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.KapTrdegPf
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import ReciprocityTheory.SemistableReduction.LatAll

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

theorem htConcl_dataOf (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    (hne : CompNe Xo c) (hfg : FnFG Xo c) (htr : FnTrdeg Xo c Dd) (hac : FnAlgClosed Xo c)
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) (het : NZAt h etR) (hta1 : NZAt h ta1R) (hta2 : NZAt h ta2R)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2)
    (huta1 : wtZ uta1.1 uta1.2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ ude.1 ude.2))
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2)
    (hfn : FnNe Xo c fn) (hconj : FnConj Xo c fn yP)
    (hbdd : LawBdd (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha1 : A1Bigness (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha2 : A2RegularityOrders (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha3' : LawA3' (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (sel : Fin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).del → Fin np)
    (ha4 : A4Selection (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) sel)
    (hnum : NumOK (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha13 : A13Measurable (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (hH1 : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).FinitePlaceHyp) (hF1d : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).TrivialPlaceHyp)
    (hLAM : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HtLAM) (hSup : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HtSup)
    (hI2et : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HeightIntegralEstimateTrivialPlace) (hI2be : (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HeightIntegralBoundEstimate) :
    Formalism.MainNotions.Gaps.HeightData.HtConcl ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).htOf (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13)
      ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).genericSection_of_axioms (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13))) :=
  (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).heights (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13)
    ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).genericSection_of_axioms (axHOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne hfg htr hac hwb het hta1 hta2 huet huta1 huta2 hfn hconj hbdd ha1 ha2 ha3' sel ha4 hnum ha13)) hH1 hF1d hLAM hSup hI2et hI2be

section Of

open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj.abelian₂ Formalism.L2.LamCM ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {Tc : Core D}

theorem htConcl_dataOf_of (hL : LawsCore Tc) (j : ℕ) [Fintype (Comp (Tc.Q.Xo j) Tc.Q.c)]
    [Nonempty (HeightOneSpectrum (𝓞 Tc.Q.c.F))] (h : GenFrEx (Tc.Q.Xo j) Tc.Q.c)
    (δ : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AddValuation (Om Z) (WithTop ℤ) → Ix (Tc.Q.Dw j) → ℤ)
    (fn : ∀ σ : Tc.Q.c.F →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt σ) → Ix (Tc.Q.Dw j) → ℝ)
    (yP : ∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, ∀ P : Om Z →+* ℂ, FrPt (Tc.Q.Xo j) Tc.Q.c (CAt (sgOf P)))
    (d N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR D.host.E)
    (wR : Fin (N + 1) → Tc.R j) (jc : Comp (Tc.Q.Xo j) Tc.Q.c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Tc.R j) (n0 : ℕ) (th0R : Fin n0 → Tc.R j) (uF0 : WtR D.host.E)
    (nk : ℕ) (thkR : Fin nk → Tc.R j) (MR : Set (Tc.R j)) (etR ta1R ta2R : Tc.R j)
    (nu : HeightOneSpectrum (𝓞 Tc.Q.c.F) → ℝ)
    (ip : (Tc.Q.c.F →+* ℂ) → (∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AC Z) → (∀ Z : Comp (Tc.Q.Xo j) Tc.Q.c, AC Z) → ℂ)
    (wsize : WTZ D.host.E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    (C : ((D.host.E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule Tc.Q.c.F (Tc.R j))
    (cls : ∀ (T : CDVR) (ι : Tc.Q.c.F →+* T.Fr), IntFr (Tc.Q.Xo j) Tc.Q.c T ι → Prop) (PY : HeightOneSpectrum (𝓞 Tc.Q.c.F) → Type)
    (lies : ∀ la (T : CDVR) (ι : Tc.Q.c.F →+* T.Fr), IntFr (Tc.Q.Xo j) Tc.Q.c T ι → PY la → Prop)
    {rU : ℕ} (U : ∀ σ : Tc.Q.c.F →+* ℂ, Unf (Tc.Q.Xo j) Tc.Q.c σ rU)
    (nuA : HeightOneSpectrum (𝓞 Tc.Q.c.F) → ℝ) (large₂ : SizeData₂ D) (CL AL : ℝ) (ka : WeightFamilies.Wt D j)
    (mx : (Tc.Q.c.F →+* ℂ) → ℝ)

    (hne : CompNe (Tc.Q.Xo j) Tc.Q.c) (hac : FnAlgClosed (Tc.Q.Xo j) Tc.Q.c)
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) (hetN : NZAt h etR) (hta1N : NZAt h ta1R) (hta2N : NZAt h ta2R)
    (hfn : FnNe (Tc.Q.Xo j) Tc.Q.c fn) (hconj : FnConj (Tc.Q.Xo j) Tc.Q.c fn yP)
    (hbdd : LawBdd (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR
      jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r))
    (ha1 : A1Bigness (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR
      jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r))
    (sel : Fin (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc
      np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r).del → Fin np)
    (ha4 : A4Selection (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR
      jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r) sel)
    (hT : OrdTie h δ cls PY lies) (hTQ : OrdTieQ h δ) (hTQZ : OrdTieQZ h δ)

    (hktr : KapTrdeg (Tc.Q.Xo j) Tc.Q.c d)
    (hD : DivFin (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR
      jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r))
    (hF : FrShFin (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR
      jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r) δ)
    (hst : STLoc h (d + Nat.card (FlagVar (Tc.Q.Dw j))) N uL wR jc) (hna : NrmAlong fn yP)
    (hR1 : RegularityR1ValuedPoints (Tc.Q.Xo j) Tc.Q.c C cls PY lies) (hR1Q : RegularityR1Quotient (Tc.Q.Xo j) Tc.Q.c C)
    (hwS : ∀ k, wR k ∈ sec (Tc.Q.Xo j) Tc.Q.c uL.1 uL.2) (hwC : ∀ k, wR k ∈ C uL.1 uL.2) (hwI : ∀ k, IntAlg (wR k))
    (hpS : ∀ k, thpR k ∈ sec (Tc.Q.Xo j) Tc.Q.c uF.1 uF.2) (hpC : ∀ k, thpR k ∈ C uF.1 uF.2) (hpI : ∀ k, IntAlg (thpR k))
    (heS : etR ∈ sec (Tc.Q.Xo j) Tc.Q.c uet.1 uet.2) (heC : etR ∈ C uet.1 uet.2) (heI : IntAlg etR)
    (h1S : ta1R ∈ sec (Tc.Q.Xo j) Tc.Q.c uta1.1 uta1.2) (h1C : ta1R ∈ C uta1.1 uta1.2) (h1I : IntAlg ta1R)
    (h2S : ta2R ∈ sec (Tc.Q.Xo j) Tc.Q.c uta2.1 uta2.2) (h2C : ta2R ∈ C uta2.1 uta2.2) (h2I : IntAlg ta2R)

    (hreg : regular₂ (Tc.Q.Xo j) Tc.Q.c U) (hdL : Dom uL.1 uL.2) (hdE : Dom uet.1 uet.2)
    (hws : ∀ k, wR k ∈ cusp (Tc.Q.Xo j) Tc.Q.c U uL.1 uL.2) (hetc : etR ∈ cusp (Tc.Q.Xo j) Tc.Q.c U uet.1 uet.2)
    (hnzc : NoCommonZero (Tc.Q.Xo j) Tc.Q.c wR)
    (halg : ∀ la, ∀ v ∈ valSet (Tc.Q.Xo j) Tc.Q.c (algCls (Tc.Q.Xo j) Tc.Q.c) la, 0 ≤ v etR ∧
      (v etR ≠ ⊤ → (⨅ k, v (wR k)) ≤ (nuA la : EReal) + ((cc / (2 * i) : ℝ) : EReal) * v etR))

    (hgt : GenFromTest (Tc.Q.Xo j) Tc.Q.c h)
    (hka : wtZ (wtA ka) ka.n = (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet
      uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive
      tableLineDegreeTwo Prw PO f r).n96 • wtZ uL.1 uL.2)
    (hj : InR D j) (hKey : KeyCore)
    (Xx : (Tc.U j Tc.σ₀).Comp → DataX D.host.E D.R.r) (hX : ∀ k, (Xx k).toData = (Tc.U j Tc.σ₀).X k)
    (M wf : ℝ) (hM : 0 < M)
    (hwf : ∀ k, (∑ τ, ((Tc.U j Tc.σ₀).X k).spread (laU (Tc.U j Tc.σ₀) (wtA ka) ka.n k) τ) ≤ wf) (hwf1 : 1 ≤ wf)
    (hr : 0 < D.R.r)
    (htr : ∀ k, ∀ v ∈ (Xx k).L', herm ((Tc.U j Tc.σ₀).X k).Gm v v = 0 → ∀ b : D.host.E,
      ReciprocityTheory.ChartRestriction.G.FD.cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ ((Tc.U j Tc.σ₀).X k).Γ, ((Tc.U j Tc.σ₀).X k).χ (laU (Tc.U j Tc.σ₀) (wtA ka) ka.n k) γ = 1 ∧
        ∀ τ : ((Tc.U j Tc.σ₀).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 =
          ((Tc.U j Tc.σ₀).X k).flowMat v τ ((M : ℂ) * τ.1 b))
    (hAA : ∀ k, ∀ a ∈ D.host.AA, ∀ v ∈ (Xx k).L', a • v ∈ (Xx k).Λ)
    (aMax : ℕ) (hPt : ∀ La, LamPtSt Tc j La) (hDeg : LamDegSt Tc.Q.H large₂.logOm) (hInd : LamIndSt)
    (hTie : ∀ k, LamTieSt Tc hL j ka (laOf Xx M wf k) aMax) (hLa1 : ∀ k, 1 ≤ laOf Xx M wf k)
    (hroom : ∀ k, ∀ s : ℕ, s ≤ aMax →
      (pDeg large₂.logOm + (1 / 2) * Real.log (laOf Xx M wf k)) *
          ((s : ℝ) + ((D.R.f * ((Tc.Q.Dw j).p + (Tc.Q.Dw j).q) : ℕ) : ℝ) * ka.n) +
        (s : ℝ) * Real.log ((D.R.r : ℝ) * laOf Xx M wf k) ≤
      WeightFamilies.PP0v D large₂ CL AL * (1 + Real.log ka.size) * ka.size)
    (hprod : ProdInLat hL j ka wR (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude
      uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet
      tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96)
    (hsupL : SupPTGe hL j h fn yP ka)
    (wL : WeightFamilies.Wt D j) (huL : uL = (wtA wL, wL.n)) (hwsz : wsize (wtZ uL.1 uL.2) = wL.size)
    (hlc : LamConst j large₂ CL AL ka PP0' (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka
      ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4
      Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).n96 wL.size)

    (hcx : ValAtCx h yP)
    (hwB : ∀ k, SupBdd (Tc.Q.Xo j) Tc.Q.c fn uL.1 uL.2 (wR k)) (hwN : ∀ k, NZSome h (wR k))
    (hpB : ∀ k, SupBdd (Tc.Q.Xo j) Tc.Q.c fn uF.1 uF.2 (thpR k)) (hpN : ∀ k, NZSome h (thpR k))
    (h1B : SupBdd (Tc.Q.Xo j) Tc.Q.c fn uta1.1 uta1.2 ta1R) (h1N : NZSome h ta1R)
    (h2B : SupBdd (Tc.Q.Xo j) Tc.Q.c fn uta2.1 uta2.2 ta2R) (h2N : NZSome h ta2R)
    (hmx : ∀ σ k, Real.log (supR (Tc.Q.Xo j) Tc.Q.c fn σ uL.1 uL.2 (wR k)) ≤ mx σ)
    (hmxm : meanK mx ≤ Gc * wsize (wtZ uL.1 uL.2))
    (hth : ∀ k, meanK (fun σ => Real.log (supR (Tc.Q.Xo j) Tc.Q.c fn σ uF.1 uF.2 (thpR k))) ≤ Gc * wsize (wtZ uF.1 uF.2))
    (hsa1 : meanK (fun σ => Real.log (supR (Tc.Q.Xo j) Tc.Q.c fn σ uta1.1 uta1.2 ta1R)) ≤
      2 * PI4 * (((d + Nat.card (FlagVar (Tc.Q.Dw j))) : ℕ) : ℝ) * wsize (wtZ uL.1 uL.2))
    (hsa2 : meanK (fun σ => Real.log (supR (Tc.Q.Xo j) Tc.Q.c fn σ uta2.1 uta2.2 ta2R)) ≤
      PI4 * (((d + Nat.card (FlagVar (Tc.Q.Dw j))) : ℕ) : ℝ) * wsize (wtZ uL.1 uL.2))

    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2)
    (huta1 : wtZ uta1.1 uta1.2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ ude.1 ude.2))
    (huta2 : wtZ uta2.1 uta2.2 = ((d + Nat.card (FlagVar (Tc.Q.Dw j))) + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2) (hcc : 0 ≤ cc)
    (hnum : NumOK (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR
      jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r))

    (hH1 : (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np
      thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r).FinitePlaceHyp)
    (hI2et : (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np
      thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r).HeightIntegralEstimateTrivialPlace)
    (hI2be : (dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np
      thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f
      r).HeightIntegralBoundEstimate) :
    Formalism.MainNotions.Gaps.HeightData.HtConcl ((dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet
      uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive
      tableLineDegreeTwo Prw PO f r).htOf (axHOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1
      uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo
      Prw PO f r hne (fnFG_of (Tc.Q.Xo j) Tc.Q.c (kapFG_pf (Tc.Q.Xo j) Tc.Q.c)) (fnTrdeg_of (Tc.Q.Xo j) Tc.Q.c d hktr) hac hwb hetN hta1N
      hta2N huet huta1 huta2 hfn hconj hbdd ha1 (lawA2_of_data (h := h) (δ := δ) (C := C) (cls := cls) (PY := PY) (lies
      := lies) (fn := fn) (yP := yP) (Dd := (d + Nat.card (FlagVar (Tc.Q.Dw j)))) (N := N) (T := T) (i := i) (g0 :=
      g0) (cc := cc) (uL := uL) (uF := uF) (uka := uka) (ude := ude) (uet := uet) (uta1 := uta1) (uta2 := uta2) (wR
      := wR) (jc := jc) (np := np) (thpR := thpR) (n0 := n0) (th0R := th0R) (uF0 := uF0) (nk := nk) (thkR := thkR)
      (MR := MR) (etR := etR) (ta1R := ta1R) (ta2R := ta2R) (nu := nu) (ip := ip) (wsize := wsize) (DF := DF) (PN :=
      PN) (PQ := PQ) (tableDegreeThreeBase := tableDegreeThreeBase) (PP0' := PP0') (Pd := Pd) (Gc := Gc) (PI4 := PI4) (Pet := Pet) (tableLineDegreeFive := tableLineDegreeFive) (tableLineDegreeTwo
      := tableLineDegreeTwo) (Prw := Prw) (PO := PO) (f := f) (r := r) (hT := hT) (hTQ := hTQ) (hR1 := hR1) (hR1Q := hR1Q) (hwS :=
      hwS) (hwC := hwC) (hwI := hwI) (hpS := hpS) (hpC := hpC) (hpI := hpI) (heS := heS) (heC := heC) (heI := heI)
      (h1S := h1S) (h1C := h1C) (h1I := h1I) (h2S := h2S) (h2C := h2C) (h2I := h2I) (huet := huet) (huta1 := huta1)
      (huta2 := huta2) (heN := hetN) (h1N := hta1N) (h2N := hta2N)) (lawA3'_dataOf (h := h) (hD := hD) (hF := hF))
      sel ha4 hnum (lawA13_of_data h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1
      uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo
      Prw PO f r (nrmContOff_of h fn yP _ N uL wR jc hst hna hfn (fnTrdeg_of (Tc.Q.Xo j) Tc.Q.c d hktr) (fnFG_of (Tc.Q.Xo j) Tc.Q.c (kapFG_pf (Tc.Q.Xo j) Tc.Q.c)) hwb))) ((dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1
      uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo
      Prw PO f r).genericSection_of_axioms (axHOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1
      uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo
      Prw PO f r hne (fnFG_of (Tc.Q.Xo j) Tc.Q.c (kapFG_pf (Tc.Q.Xo j) Tc.Q.c)) (fnTrdeg_of (Tc.Q.Xo j) Tc.Q.c d hktr) hac hwb hetN hta1N
      hta2N huet huta1 huta2 hfn hconj hbdd ha1 (lawA2_of_data (h := h) (δ := δ) (C := C) (cls := cls) (PY := PY) (lies
      := lies) (fn := fn) (yP := yP) (Dd := (d + Nat.card (FlagVar (Tc.Q.Dw j)))) (N := N) (T := T) (i := i) (g0 :=
      g0) (cc := cc) (uL := uL) (uF := uF) (uka := uka) (ude := ude) (uet := uet) (uta1 := uta1) (uta2 := uta2) (wR
      := wR) (jc := jc) (np := np) (thpR := thpR) (n0 := n0) (th0R := th0R) (uF0 := uF0) (nk := nk) (thkR := thkR)
      (MR := MR) (etR := etR) (ta1R := ta1R) (ta2R := ta2R) (nu := nu) (ip := ip) (wsize := wsize) (DF := DF) (PN :=
      PN) (PQ := PQ) (tableDegreeThreeBase := tableDegreeThreeBase) (PP0' := PP0') (Pd := Pd) (Gc := Gc) (PI4 := PI4) (Pet := Pet) (tableLineDegreeFive := tableLineDegreeFive) (tableLineDegreeTwo
      := tableLineDegreeTwo) (Prw := Prw) (PO := PO) (f := f) (r := r) (hT := hT) (hTQ := hTQ) (hR1 := hR1) (hR1Q := hR1Q) (hwS :=
      hwS) (hwC := hwC) (hwI := hwI) (hpS := hpS) (hpC := hpC) (hpI := hpI) (heS := heS) (heC := heC) (heI := heI)
      (h1S := h1S) (h1C := h1C) (h1I := h1I) (h2S := h2S) (h2C := h2C) (h2I := h2I) (huet := huet) (huta1 := huta1)
      (huta2 := huta2) (heN := hetN) (h1N := hta1N) (h2N := hta2N)) (lawA3'_dataOf (h := h) (hD := hD) (hF := hF))
      sel ha4 hnum (lawA13_of_data h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1
      uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo
      Prw PO f r (nrmContOff_of h fn yP _ N uL wR jc hst hna hfn (fnTrdeg_of (Tc.Q.Xo j) Tc.Q.c d hktr) (fnFG_of (Tc.Q.Xo j) Tc.Q.c (kapFG_pf (Tc.Q.Xo j) Tc.Q.c)) hwb))))) :=
  htConcl_dataOf h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np
    thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hne
    (fnFG_of (Tc.Q.Xo j) Tc.Q.c (kapFG_pf (Tc.Q.Xo j) Tc.Q.c)) (fnTrdeg_of (Tc.Q.Xo j) Tc.Q.c d hktr) hac hwb hetN hta1N hta2N huet huta1
    huta2 hfn hconj hbdd ha1 (lawA2_of_data (h := h) (δ := δ) (C := C) (cls := cls) (PY := PY) (lies := lies) (fn := fn)
    (yP := yP) (Dd := (d + Nat.card (FlagVar (Tc.Q.Dw j)))) (N := N) (T := T) (i := i) (g0 := g0) (cc := cc) (uL :=
    uL) (uF := uF) (uka := uka) (ude := ude) (uet := uet) (uta1 := uta1) (uta2 := uta2) (wR := wR) (jc := jc) (np :=
    np) (thpR := thpR) (n0 := n0) (th0R := th0R) (uF0 := uF0) (nk := nk) (thkR := thkR) (MR := MR) (etR := etR)
    (ta1R := ta1R) (ta2R := ta2R) (nu := nu) (ip := ip) (wsize := wsize) (DF := DF) (PN := PN) (PQ := PQ) (tableDegreeThreeBase :=
    tableDegreeThreeBase) (PP0' := PP0') (Pd := Pd) (Gc := Gc) (PI4 := PI4) (Pet := Pet) (tableLineDegreeFive := tableLineDegreeFive) (tableLineDegreeTwo := tableLineDegreeTwo) (Prw := Prw) (PO
    := PO) (f := f) (r := r) (hT := hT) (hTQ := hTQ) (hR1 := hR1) (hR1Q := hR1Q) (hwS := hwS) (hwC := hwC) (hwI :=
    hwI) (hpS := hpS) (hpC := hpC) (hpI := hpI) (heS := heS) (heC := heC) (heI := heI) (h1S := h1S) (h1C := h1C)
    (h1I := h1I) (h2S := h2S) (h2C := h2C) (h2I := h2I) (huet := huet) (huta1 := huta1) (huta2 := huta2) (heN :=
    hetN) (h1N := hta1N) (h2N := hta2N)) (lawA3'_dataOf (h := h) (hD := hD) (hF := hF)) sel ha4 hnum (lawA13_of_data
    h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0
    nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r (nrmContOff_of h fn yP _ N uL wR jc hst hna hfn (fnTrdeg_of (Tc.Q.Xo j) Tc.Q.c d hktr) (fnFG_of (Tc.Q.Xo j) Tc.Q.c (kapFG_pf (Tc.Q.Xo j) Tc.Q.c)) hwb)) hH1 (height_F1_of_data h δ
    fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk
    thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r U hreg hTQZ hdL hdE hws
    hetc hnzc hetN huet hcc nuA halg) (htLAM_of hL j h δ fn yP (d + Nat.card (FlagVar (Tc.Q.Dw j))) N T i g0 cc uL
    uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc
    PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r large₂ CL AL ka hgt hka
    (abelian₂.lamw_link Tc hL large₂ j hj ka CL AL siegelSpaceAlgebra_holds hKey ReciprocityTheory.MultiplicativeHeights.Closed.lemmaH Xx hX M wf hM hwf hwf1 hr htr hAA aMax hPt hDeg hInd hTie hLa1 hroom) hprod
    hsupL (by rw [hwsz]; exact hlc)) (htSup_of h δ fn yP (d + Nat.card (FlagVar
    (Tc.Q.Dw j))) N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip
    wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hfn (fnFG_of (Tc.Q.Xo j) Tc.Q.c (kapFG_pf (Tc.Q.Xo j) Tc.Q.c)) hcx huta1 huta2
    hwS hwB hwN hpS hpB hpN h1S h1B h1N h2S h2B h2N mx hmx hmxm hth hsa1 hsa2) hI2et hI2be

end Of

end Formalism.L2.Pj
