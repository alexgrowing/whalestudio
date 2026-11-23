import Mathlib
import Development.AutomorphicArithmetic.CharacterBoxes.ExS
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

namespace GlobalTheory.Fc

open GlobalTheory.Cp

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Hyps (N : FamClass → Prop) (DR : R1.DefT) : Type 1 where
  𝒜 : FamClass
  σ : RawSel Bundle 𝒜
  cT : ℝ → ℝ → ℝ
  hEx : MinkDiv → UpperTheory.Top.ExS 𝒜 cT
  hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm
  hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((sel σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.IndefR.RowsB ((selB σ) Fm hc x hx h i)
  hTw : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((sel σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.TieTwRec (Fm.L x i) ((selP σ) Fm hc x hx h i).1.S0.Tw
  hPA : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel σ Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.IndefR.Links.PrimRows3 (selB σ Fm hc x hx h i).Q.Rl (selB σ Fm hc x hx h i).Q.F ∧ (selP σ Fm hc x hx h i).1.A3.fam3.TypesSep3
  hLamP : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((sel σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.Rows.RowsHoldLam3 ((selP σ) Fm hc x hx h i).1
  hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((sel σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      DivRows3G ((selP σ) Fm hc x hx h i).1
  hDcPtG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((sel σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      DcPtG ((selP σ) Fm hc x hx h i).1
  hTu : Closed (WithTw (WithSm (WithChN 𝒜))) fun {eps} Fm _ => cT eps Fm.CYL ≤ Fm.CTu → TuSize Fm
  hn4 : Closed (WithTw (WithSm (WithChN 𝒜))) fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
      StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev
  hLit : LitThin
  hWu : Formalism.L2.SG.Pf.WuDecayOfGap
  hRF : Formalism.L2.SG.RowsDef.RowsFinDim
  hTF : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3
  c30 : List ℝ → Formalism.MainNotions.S.CountingConstants
  hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A
  sTy : Formalism.L2.SG.RowsPos.TypeP
  sNG : Formalism.L2.SG.RowsPos.RowNGP
  sM : Formalism.L2.SG.RowsPos.RowMainEqP
  sLp : Formalism.L2.SG.ThmSOwn.LoopRowS 3 (D3 3 𝒜) (fun Fm hc => ⟨((sel σ) Fm (d3_a hc)).1, fun x hx h i => ((selS σ) Fm (d3_a hc) x hx h i).toSTies⟩)
  sO : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, Formalism.L2.SG.ThmSOwn.TheoremSSelected Fm 3
      ⟨((sel σ) Fm (d3_a hc)).1, fun x hx h i => ((selS σ) Fm (d3_a hc) x hx h i).toSTies⟩
  h30 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.CountE.CountAllPointsClass Formalism.L2.SG.ThmSOwn.PLevT' Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb
  hInstR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : ((sel σ) Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep (Fm.D x i) ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) ((Fm.D x i).sp.Y 0).rank
  selJ : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel σ Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.SG.JoinSI.JoinSI (R := (sel σ Fm hc).2 x hx h i) (S := selS σ Fm hc x hx h i) (Q := (selB σ Fm hc x hx h i).Q)
  jOn : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ((Fm.D x i).what₂.V0 (Fm.D x i).what₂.mu0).map ((Fm.D x i).what₂.iota (Fm.D x i).what₂.mu0) = ⊤
  hMt : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (μ : (Fm.D x i).what₂.Tup) (a : NumberField.RingOfIntegers (Fm.D x i).what₂.LL),
      ∀ y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier, (Fm.D x i).what₂.embLL (a : (Fm.D x i).what₂.LL) • y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier
  rRows : R1.H_rRows DR 𝒜 σ
  aPt0 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 (Fm.D x i) u
  aPtTw : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPointIntegral (Fm.D x i) (Fm.ex x hx i).tw
  aPer0 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl (Fm.D x i)
  aPerTw : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible (Fm.D x i) (Fm.X x i) (Fm.ex x hx i).tw
  aP10 : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
      ∀ u, Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (Fm.D x i) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT (Fm.X x i) (Fm.ex x hx i).tw u
  aAtG : Closed (D3 3 𝒜) fun Fm _ => ∃ C1 : ℝ, (∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1
  aC2 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm
  hServ : ServT (D3 3 𝒜) fun Fm hc => (sel σ) Fm (d3_a hc)
  cIc : ℝ
  hcI : 0 < cIc
  irrC : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f)
  zL : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, ∃ xr : ℝ, ∀ x (hx : Fm.x1 < x) (h : ((sel σ) Fm (d3_a hc)).1 ≤ x), xr ≤ x →
      ∀ (i : Fm.Ix x) (k : Fin (Fm.D x i).R.m),
        Function.Surjective (Formalism.L2.DIV.lPrj (Fm.D x i) ((selP σ) Fm (d3_a hc) x hx h i).1.A3.A ((selP σ) Fm (d3_a hc) x hx h i).1.P0
          ((selP σ) Fm (d3_a hc) x hx h i).1.ψ0 (((selP σ) Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 ((selP σ) Fm (d3_a hc) x hx h i).1.Zs) k
          ((selP σ) Fm (d3_a hc) x hx h i).1.A3.A.μ0).mulVec
  tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm
  hU : ∀ D, MassRatioUnderVolume D
  hG : ∀ D, GenusMassVolumes.GenusMassAt D 2
  nRest : N (D3 3 𝒜)

end GlobalTheory.Fc

end
