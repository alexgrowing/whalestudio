import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentBlockMeasure
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictK
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfA
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfB

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData

namespace Formalism.L2.SG.Pf.MainEqCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abs

variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]

def genT (X : PB.Terms τ Rw I H H₁) : PB.Terms τ Rw I H H₁ :=
  { X with
    gener := fun t => ¬ X.gener t
    s0 := fun t t' => if X.s0 t t' = 1 ∧ X.scal t t' then 1 else 2 }

theorem genT_ngSet (X : PB.Terms τ Rw I H H₁) : (genT X).ngSet = X.genSet := by
  ext t
  simp [genT, PB.Terms.ngSet, PB.Terms.genSet]

theorem genT_one (X : PB.Terms τ Rw I H H₁) : (genT X).one (genT X).ngSet = X.sc X.genSet := by
  rw [genT_ngSet]
  ext p
  simp only [PB.Terms.one, PB.Terms.sc, PB.Terms.allPairs, Set.mem_setOf_eq]
  by_cases h : X.s0 p.1 p.2 = 1 ∧ X.scal p.1 p.2
  · have e : (genT X).s0 p.1 p.2 = 1 := by simp only [genT]; rw [if_pos h]
    rw [e]
    exact ⟨fun ⟨a, _⟩ => ⟨a, h.1, h.2⟩, fun ⟨a, _, _⟩ => ⟨a, rfl⟩⟩
  · have e : (genT X).s0 p.1 p.2 = 2 := by simp only [genT]; rw [if_neg h]
    rw [e]
    exact ⟨fun ⟨_, b⟩ => absurd b (by norm_num), fun ⟨_, b, c⟩ => absurd ⟨b, c⟩ h⟩

theorem genT_pairSum (X : PB.Terms τ Rw I H H₁) :
    (genT X).pairSum ((genT X).one (genT X).ngSet) = X.pairSum (X.sc X.genSet) := by
  rw [genT_one]; rfl

variable {Cl Nu : Type}

def ampGen (L : PN.LocalNG Cl Nu) (d : ∀ p, L.D p) : ℂ := ∏ p, L.aZ p (d p)

def weightedGenericAmplitudeSq (L : PN.LocalNG Cl Nu) (c : Cl) (ν : Nu) : ℝ :=
  match L.dat c ν with
  | none => 0
  | some d => L.rw c * ‖ampGen L d‖ ^ 2

def ZAt (L : PN.LocalNG Cl Nu) (C1 r : ℕ) : Prop :=
  ∀ p, ∑ d, L.wt p d * ‖L.aZ p d‖ ^ 2 ≤ L.H p ^ (C1 * (r + 1) ^ 2) * L.nn p

def MeanAmpGen : Prop :=
  ∀ (Cl Nu : Type) (L : PN.LocalNG Cl Nu) (C1 C0 r : ℕ), L.Basic → ZAt L C1 r → L.MassRatioAt C0 r → L.Unfold →
    ∀ S : Finset (Cl × Nu), ∑ x ∈ S, weightedGenericAmplitudeSq L x.1 x.2 ≤ L.Htot ^ PN.e7 C1 C0 r * L.ngenTot

def LocalInputG {E : Type} [Field E] {r : ℕ} (X : PB.Terms τ Rw I H H₁) (N : PN.NGData τ E r Cl Nu) (C1 C0 : ℕ) :
    Prop :=
  ∀ γ, PN.IsPt X N γ → ∀ S : Finset (Cl × Nu), ∃ L : PN.LocalNG Cl Nu, L.Basic ∧ ZAt L C1 r ∧ L.MassRatioAt C0 r ∧
    L.Unfold ∧ (∀ x ∈ S, N.a2 x.1 γ x.2 = weightedGenericAmplitudeSq L x.1 x.2) ∧ N.Hh γ = L.Htot ∧ N.ngen γ = L.ngenTot

def GenInputs {E : Type} [Field E] [NumberField E] {r : ℕ} (X : PB.Terms τ Rw I H H₁) (N : PN.NGData τ E r Cl Nu)
    (f C1 C0 A : ℕ) (CB b rd g TT cSt AAre e1 Ire : ℝ) : Prop :=
  PN.ClassInput (genT X) N ∧ PN.AmpInput (genT X) N ∧
  PN.NormalsInput (genT X) N (rd ^ (12 * r * (r + 1) * f) * TT ^ (6 * f)) ∧
  PN.PointsInput (genT X) N ∧ LocalInputG (genT X) N C1 C0 ∧ PN.MeasureInput (genT X) N cSt ∧
  PN.GenMassInput (genT X) N AAre e1 ∧ PN.HeightInput (genT X) N (g ^ f) ∧
  PN.PointSumInput (genT X) N (A * (r + 1) ^ 2)
    (Real.exp (CB * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) * Ire)

end Abs

def RowGenAbstract : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (τ Rw I H H₁ : Type) [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [CompleteSpace H₁] (X : PB.Terms τ Rw I H H₁) (r : ℕ) (Cl Nu : Type) (N : PN.NGData τ E r Cl Nu)
    (C1 C0 Aexp : ℕ) (Pc gf cSt AAre e1 TB : ℝ),
    PN.e7 C1 C0 r + PN.eN r + 6 ≤ Aexp → 0 < Pc → 1 ≤ gf → 0 ≤ cSt → 0 ≤ AAre → 0 ≤ e1 →
    X.AbsConv → PN.ClassInput (genT X) N → PN.AmpInput (genT X) N → PN.NormalsInput (genT X) N Pc →
    PN.PointsInput (genT X) N → LocalInputG (genT X) N C1 C0 → PN.MeasureInput (genT X) N cSt →
    PN.GenMassInput (genT X) N AAre e1 → PN.HeightInput (genT X) N gf → PN.PointSumInput (genT X) N Aexp TB →
    X.pairSum (X.sc X.genSet) ≤ X.Gam1 * (64 ^ (Fintype.card (InfinitePlace E) * (r + 1)) *
      (cSt * AAre * e1 * Pc * gf ^ Aexp * TB))

def RowGenJoint : Prop :=
  ∀ (C1 C0 A : ℕ) (CB CSt Cg CT : ℝ), 0 ≤ CB → 0 ≤ CSt → 0 ≤ Cg → 0 ≤ CT →
    C1 + C0 + 38 ≤ A → ∃ Cn : ℝ, 0 ≤ Cn ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (τ Rw I H H₁ : Type) [Fintype I]
      [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
      [CompleteSpace H₁] (X : PB.Terms τ Rw I H H₁) (r k : ℕ) (Cl Nu : Type) (N : PN.NGData τ E r Cl Nu)
      (P : Type) [Fintype P] (B : S3.MassData P) (b rd g TT cSt e1 Irat Ire : ℝ),
      X.AbsConv → X.Gam1 = B.Gam1 → PN.NormInputs B →
      PN.FrameInputs B rd g r k (Fintype.card (InfinitePlace E)) Irat Ire →
      PN.NGSizes Cg CT CSt r (Fintype.card (InfinitePlace E)) b rd g TT cSt e1 →
      GenInputs X N (Fintype.card (InfinitePlace E)) C1 C0 A CB b rd g TT cSt
        (PN.abelian₂ rd r k (Fintype.card (InfinitePlace E)) * B.AA) e1 Ire →
      X.RowMain (Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card (InfinitePlace E) : ℕ) * Real.log b))
        (B.d * B.d' / B.Dstar)

section Conc

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

def clsG (t : TauC Y u u) : Set (TauC Y u u) :=
  {t' | t' ∈ (Y.tO u u).genSet ∧ (Y.tO u u).rowOf t' = (Y.tO u u).rowOf t ∧ (Y.tO u u).s0 t t' = 1 ∧
    (Y.tO u u).scal t t'}

def grpGC (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :=
  ∑' t : TauC Y u u, ((Y.tO u u).genSet ∩ {t | clsG Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν}).indicator
    (Y.tO u u).vec t

def a2GC (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (c : Set (TauC Y u u)) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :
    ℝ :=
  ‖grpGC Y u c γ ν‖ ^ 2 / J2of Y u u νq γ

def NOfG (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) :
    PN.NGData (TauC Y u u) D.host.E D.R.rS (Set (TauC Y u u)) (NuC D) where
  cls := clsG Y u
  pt := ptPN
  nml := nmlOf Y u u
  a2 := a2GC Y u νL
  J2loc := J2of Y u u νL
  jacobianSquareBound := J2of Y u u νB
  n := nPt D.host.rdE D.R.k ((Tu D u : ℕ) * (Tu D u : ℕ))
  NG := NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ))
  ND := NDPt D.host.rdE
  Hh := HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u : ℕ))
  ngen := ng

end Conc

def GenCutC : Prop :=
  ∀ Cg cb Cw cT CT C0 A : ℝ, ∃ (C1 C0n Aexp : ℕ) (CB CSt Cgs CTs : ℝ), 0 ≤ CB ∧ 0 ≤ CSt ∧ 0 ≤ Cgs ∧ 0 ≤ CTs ∧
    C1 + C0n + 38 ≤ Aexp ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.S.Cnt.Hyp D large₂ u u C' Cl Cg cb Cw cT CT C0 A → ConcTie X Y →
      ∃ (P : Type) (_ : Fintype P) (B : S3.MassData P) (cSt e1 Irat Ire : ℝ)
        (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        Formalism.L2.SG.RealObj.NuQOK X u u νL ∧ Formalism.L2.SG.RealObj.NuQOK X u u νB ∧
        (Y.tO u u).Gam1 = B.Gam1 ∧ B.d * B.d' / B.Dstar = ddC X Y u u ∧ PN.NormInputs B ∧
        PN.FrameInputs B (2 * D.host.v) (X.B.g : ℝ) D.R.rS D.R.k D.R.f Irat Ire ∧
        PN.NGSizes Cgs CTs CSt D.R.rS D.R.f large₂.sc.b (2 * D.host.v) (X.B.g : ℝ)
          (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) cSt e1 ∧
        GenInputs (Y.tO u u) (NOfG Y u νL νB ng) D.R.f C1 C0n Aexp CB large₂.sc.b (2 * D.host.v) (X.B.g : ℝ)
          (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) cSt (PN.abelian₂ (2 * D.host.v) D.R.rS D.R.k D.R.f * B.AA) e1 Ire

open Formalism.L2.SG.NormCut in

def DegLeftActC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    OOIntAll X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) → AmpWellDef (X.Fu u) (X.Fu u) (Y.cs u) (Y.cs u) →
    OOFundIndep X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
    Formalism.L2.SG.Pf.SatGram.LeftAct (X.Fu u) (X.Fu u) Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) (Y.tO u u).degSet
      (Aset Y.TR (Y.cs u))

open Formalism.L2.SG.NormCut in

def DegRightActC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    OOIntAll X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) → AmpWellDef (X.Fu u) (X.Fu u) (Y.cs u) (Y.cs u) →
    OOFundIndep X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
    Formalism.L2.SG.Pf.SatGram.RightAct (X.Fu u) (X.Fu u) Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) (Y.tO u u).degSet
      (Aset Y.TR (Y.cs u))

open Formalism.L2.SG.NormCut in

def ChiNBiC : Prop := ∀ (D : D7) (X : HidaSetting D), ChiNBi X

open Formalism.L2.SG.NormCut in

def ColFreeC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    ColFree (X.Fu u) Y.TR (Y.cs u) (Aset Y.TR (Y.cs u)) (scOf Y.TR (Y.cs u))

def TypedCountC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X), ConcTie X Y → ∀ i : Fin 2,
    Fintype.card {v : Y.TR.Pl // Fintype.card (Y.TR.Fq v) = D.host.g i} = D.R.f

end Formalism.L2.SG.Pf.MainEqCut

namespace Formalism.L2.SG.Pf.MainEqCut

open Finset

theorem rowGenAbstract_of (hC : PN.ExactCores) (hCSS : PN.ClassSquaresSum) (hRFC : PN.RowFromClasses)
    (hCCS : PN.ClassCS) (hFB : PN.FirstBracket) (hSB : PN.SecondBracket) (hMG : MeanAmpGen) : RowGenAbstract := by
  intro E _ _ _ τ Rw I H H₁ _ _ _ _ _ _ X r Cl Nu N C1 C0 Aexp Pc gf cSt AAre e1 TB hexp hPc hgf hcSt hAA he1
    hAbs hClass hAmp hNorm hPts hLoc hMeas hGen hHt hTB
  obtain ⟨hStep4, hOm, hWCS, hE5⟩ := hC
  rw [← genT_pairSum]
  have hAbs' : (genT X).AbsConv := hAbs
  obtain ⟨hsum, heq⟩ := hRFC hCSS τ Rw I H H₁ (genT X) E r Cl Nu N hAbs' hClass
  rw [heq]
  have hG : 0 < (genT X).Gam1 := hAbs'.2.2
  show (genT X).Gam1 * _ ≤ (genT X).Gam1 * _
  apply mul_le_mul_of_nonneg_left _ hG.le
  apply hsum.tsum_le_of_sum_le
  intro Cs
  have hW : ∀ γ, PN.IsPt (genT X) N γ → 0 < Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ * (Pc * N.NG γ ^ 6) := by
    intro γ hγ
    have h1 := (hHt γ hγ).1
    have := Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E.blockMinorWeight_pos γ
    positivity
  have s1 : ∀ γ, PN.IsPt (genT X) N γ → 0 < Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight γ ∧ 0 ≤ N.J2loc γ ∧ 0 ≤ N.jacobianSquareBound γ ∧ 0 ≤ N.n γ ∧
      1 ≤ N.NG γ ∧ 1 ≤ N.ND γ ∧ 1 ≤ N.Hh γ := by
    intro γ hγ
    obtain ⟨L, hB, _, _, _, _, hH, _⟩ := hLoc γ hγ ∅
    refine ⟨Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E.blockMinorWeight_pos γ, hAmp.2.1 γ, (hMeas γ hγ).1, (hGen γ hγ).1, (hHt γ hγ).1, (hHt γ hγ).2.1, ?_⟩
    rw [hH]
    unfold PN.LocalNG.Htot
    exact Finset.prod_induction _ (fun x => 1 ≤ x)
      (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl (fun p _ => hB.2.1 p)
  have s2 : ∀ γ, PN.IsPt (genT X) N γ → ∀ S : Finset (Cl × Nu),
      ∑ x ∈ S, N.a2 x.1 γ x.2 ≤ 1 * N.Hh γ ^ PN.e7 C1 C0 r * N.ngen γ := by
    intro γ hγ S
    obtain ⟨L, hB, hZ, hMR, hU, ha, hH, hn⟩ := hLoc γ hγ S
    have := hMG Cl Nu L C1 C0 r hB hZ hMR hU S
    rw [Finset.sum_congr rfl ha, hH, hn, one_mul]
    exact this
  refine hCCS hWCS Cl (PN.Pts E r × Nu) H₁ (fun c x => PN.grp (genT X) N c x.1 x.2)
    (fun x => Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight x.1 * (Pc * N.NG x.1 ^ 6))
    (fun c x => N.a2 c x.1 x.2 * N.J2loc x.1) _ _ (by positivity) ?_ ?_ ?_ ?_ Cs
  · intro c j hj
    exact hW j.1 ⟨c, j.2, Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E.occ_of_ne (genT X) N c j.1 j.2 hj⟩
  · intro c j
    exact hAmp.2.2 c j.1 j.2
  · intro c T hT
    refine hFB (PN.Pts E r) Nu Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight (fun γ => Pc * N.NG γ ^ 6) (PN.Occ (genT X) N c) _
      (fun γ => Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E.blockMinorWeight_pos γ) ?_ ?_ ?_ T
      (fun x hx => Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E.occ_of_ne (genT X) N c x.1 x.2 (hT x hx))
    · intro γ ν hο
      have h1 := (hHt γ ⟨c, ν, hο⟩).1
      positivity
    · intro γ S hS
      exact hNorm c γ S hS
    · intro S hS
      refine hE5 E r S (fun γ hγ => ?_)
      obtain ⟨ν, hν⟩ := hS γ hγ
      exact hPts γ ⟨c, ν, hν⟩
  · intro T hT
    have key := hSB Cl (PN.Pts E r) Nu (PN.IsPt (genT X) N) N.a2 Formalism.HermitianLatticeCounting.ExpansionTerms.blockMinorWeight N.J2loc N.jacobianSquareBound N.n N.NG N.ND
      N.Hh N.ngen 1 cSt AAre e1 gf Pc TB (PN.e7 C1 C0 r) (PN.eN r) Aexp
      zero_le_one hcSt hAA he1 hgf hPc.le hexp hAmp.1 s1 s2 (fun γ hγ => (hMeas γ hγ).2)
      (fun γ hγ => (hGen γ hγ).2) (fun γ hγ => (hHt γ hγ).2.2) hTB T
      (fun x hx => ⟨x.1, x.2.2, Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.E.occ_of_ne (genT X) N x.1 x.2.1 x.2.2 (hT x hx)⟩)
    rw [one_mul] at key
    exact key

theorem rowGenJoint_of (hCh : PN.NGChain) (hMG : MeanAmpGen) : RowGenJoint := by
  intro C1 C0 A CB CSt Cg CT hCB hCSt hCg hCT hA
  obtain ⟨hc48, hCSS, hRFC, hCCS, hFB, hSB, _, _, hNorm, hFP, hNR, hES, hNum⟩ := hCh
  have hRG := rowGenAbstract_of hc48 hCSS hRFC hCCS hFB hSB hMG
  obtain ⟨Cn, hCn0, hCn⟩ := hNum A CB CSt Cg CT hCB hCSt hCg hCT
  refine ⟨Cn, hCn0, ?_⟩
  intro E _ _ _ τ Rw I H H₁ _ _ _ _ _ _ X r k Cl Nu N P _ B b rd g TT cSt e1 Irat Ire hAbs hGam hNI hFI
    hSz hIn
  obtain ⟨hCl, hAmp, hNo, hPt, hLoc, hMe, hGM, hHt, hTB⟩ := hIn
  have hnum := hCn r _ b rd g TT cSt e1 hSz
  obtain ⟨hf, hb, hrd, hrdb, hg1, hgb, hTT, hTTb, hcSt, hcStb, he1, he12⟩ := hSz
  obtain ⟨hAApos, hddpos⟩ := Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.F.pos_facts B hNI.1
  have hLam : 0 < PN.abelian₂ rd r k (Fintype.card (InfinitePlace E)) := by
    unfold PN.abelian₂; positivity
  have hrow := hRG E τ Rw I H H₁ X r Cl Nu N C1 C0 (A * (r + 1) ^ 2)
    _ _ cSt _ e1 _ (hES C1 C0 A r hA) (by positivity) (one_le_pow₀ hg1) hcSt
    (le_of_lt (mul_pos hLam hAApos)) he1 hAbs hCl hAmp hNo hPt hLoc hMe hGM hHt hTB
  have hnr := hNR hNorm hFP P B rd g r k _ Irat Ire hNI hFI
  unfold PB.Terms.RowMain
  refine le_trans hrow ?_
  rw [hGam]
  generalize Fintype.card (InfinitePlace E) = f at *
  set S : ℝ := 64 ^ (f * (r + 1)) with hS
  set Pc : ℝ := rd ^ (12 * r * (r + 1) * f) * TT ^ (6 * f) with hPc
  set gA : ℝ := (g ^ f) ^ (A * (r + 1) ^ 2) with hgA
  set ex : ℝ := Real.exp (CB * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) with hex
  set vg : ℝ := (rd / 2) ^ (f * (r + 1)) * g ^ (f * (r + 1) * (2 * r + 3)) with hvg
  set dd : ℝ := B.d * B.d' / B.Dstar with hdd
  set AAre : ℝ := PN.abelian₂ rd r k f * B.AA with hAAre
  set EX : ℝ := Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) with hEX
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hPc0 : 0 ≤ Pc := by rw [hPc]; positivity
  have hgA0 : 0 ≤ gA := by rw [hgA]; positivity
  have hex0 : 0 ≤ ex := by rw [hex]; positivity
  have hF : 0 ≤ S * cSt * e1 * Pc * gA * ex := by positivity
  calc B.Gam1 * (S * (cSt * AAre * e1 * Pc * gA * (ex * Ire)))
      = (S * cSt * e1 * Pc * gA * ex) * (B.Gam1 * AAre * Ire) := by ring
    _ ≤ (S * cSt * e1 * Pc * gA * ex) * (vg * dd) := mul_le_mul_of_nonneg_left hnr hF
    _ = (S * (cSt * e1 * Pc * gA * ex) * vg) * dd := by ring
    _ ≤ EX * dd := mul_le_mul_of_nonneg_right hnum hddpos.le

end Formalism.L2.SG.Pf.MainEqCut

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqCut

theorem rowMainEqC_of_cut (hCh : PN.NGChain) (hMG : MeanAmpGen) (hc : GenCutC) : RowMainEqC := by
  intro Cg cb Cw cT CT C0 A
  obtain ⟨C1, C0n, Aexp, CB, CSt, Cgs, CTs, h1, h2, h3, h4, hA, C'₀, Cl₀, h⟩ := hc Cg cb Cw cT CT C0 A
  obtain ⟨Cn, hCn, hK⟩ := rowGenJoint_of hCh hMG C1 C0n Aexp CB CSt Cgs CTs h1 h2 h3 h4 hA
  refine ⟨Cn, hCn, C'₀, Cl₀, fun C' Cl a b D large₂ X Y u hH hT ha => ?_⟩
  obtain ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, _, _, hG, hdd, hN, hF, hS, hIn⟩ :=
    h C' Cl a b D large₂ X Y u hH hT
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u) _ _ _ _ (Y.tO u u) D.R.rS D.R.k (Set (TauC Y u u)) (NuC D)
    (NOfG Y u νL νB ng) P B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
    cSt e1 Irat Ire
  rw [hcard] at key
  have r := key ha hG hN hF hS hIn
  rw [hdd] at r
  exact r

open Formalism.L2.SG.NormCut in

theorem normExpDegC_of (hHS : HSBlocks) (hFo : FoldOKC) (hO : OOIntAllC) (hA : AbsConvC) (hAW : AmpWellDefC)
    (hOF : OOFundIndepC) (hB : ChiNBiC) (hF : ColFreeC) (hLA : DegLeftActC) (hRA : DegRightActC) : NormExpDegC := by
  intro D X Y u hT
  have f1 := hFo D X Y u hT.1 hT.2.2.2.2.1
  have hFE := Formalism.L2.SG.Pf.fundExistsC_holds D X Y u u
  have hOO := hO D X Y u u f1 f1 hFE
  have hAbs := absConvTied_of_full hFo Formalism.L2.SG.Pf.fundExistsC_holds hO hA D X Y u u hT
  have hAW' := hAW D X Y u u hOO
  have hOF' := hOF D X Y u u hFE hOO
  have hL : ColLatK (Y.cs u) := Formalism.L2.SG.Pf.colLatK (X := X) (cs := Y.cs u)
  have hK : TermK (X.Fu u) (X.Fu u) (Y.cs u) (Y.cs u) :=
    Formalism.L2.SG.Pf.termK (X := X) (cs := Y.cs u) (cs' := Y.cs u)
  have hN : AdmN (X.Fu u) (X.Fu u) (Y.cs u) (Y.cs u) :=
    adm_norm_of_fixed_frames (cs := Y.cs u) (cs' := Y.cs u) (Full.frameTie (X := X) u u) hK (Formalism.L2.SG.Pf.modGAt (X := X))
  have hPar : AdmPar (X.Fu u) (X.Fu u) (Y.cs u) (Y.cs u) := adm_parity_of_norm (cs := Y.cs u) (cs' := Y.cs u) hK hN
  exact normExpansionOn_tOf (X.Fu u) (X.Fu u) Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) hHS gamma_product_sum_holds
    psi_natural_equiv_holds _ hAbs (chiNIndep_of_lat (Y.cs u) (Y.cs u) (hB D X) hL hL)
    (scOf Y.TR (Y.cs u)) (scOf Y.TR (Y.cs u))
    (colPhase_of Y.TR (Y.cs u) (Y.cs u) (leviCols_of (TR := Y.TR) (cs := Y.cs u) (cs' := Y.cs u) hL hL hPar)
      (phaseAt_of (TR := Y.TR) (cs := Y.cs u) (cs' := Y.cs u) hL hL hPar hN))
    (Aset Y.TR (Y.cs u)) (Aset Y.TR (Y.cs u)) (hF D X Y u hT) (hF D X Y u hT)
    (Formalism.L2.SG.Pf.SatGram.satGram_of Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) _ _ _ (hLA D X Y u hT hOO hAW' hOF')
      (hRA D X Y u hT hOO hAW' hOF'))

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.Pf.MainEqCut

open Finset

variable {Cl Nu : Type}

theorem step1G (L : PN.LocalNG Cl Nu) (hU : L.Unfold) (S : Finset (Cl × Nu)) :
    ∑ x ∈ S, weightedGenericAmplitudeSq L x.1 x.2 ≤ L.V0 * ∑ d, (∏ p, L.wt p (d p)) * ‖ampGen L d‖ ^ 2 := by
  have h : ∀ x : Cl × Nu, weightedGenericAmplitudeSq L x.1 x.2 =
      ∑ d, if L.dat x.1 x.2 = some d then L.rw x.1 * ‖ampGen L d‖ ^ 2 else 0 := by
    intro x
    unfold weightedGenericAmplitudeSq
    cases hd : L.dat x.1 x.2 with
    | none => simp
    | some d0 => simp [Finset.sum_ite_eq]
  calc ∑ x ∈ S, weightedGenericAmplitudeSq L x.1 x.2
      = ∑ x ∈ S, ∑ d, if L.dat x.1 x.2 = some d then L.rw x.1 * ‖ampGen L d‖ ^ 2 else 0 :=
        Finset.sum_congr rfl (fun x _ => h x)
    _ = ∑ d, ∑ x ∈ S, if L.dat x.1 x.2 = some d then L.rw x.1 * ‖ampGen L d‖ ^ 2 else 0 :=
        Finset.sum_comm
    _ = ∑ d, (∑ x ∈ S.filter (fun x => L.dat x.1 x.2 = some d), L.rw x.1) * ‖ampGen L d‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [← Finset.sum_filter, Finset.sum_mul]
    _ ≤ ∑ d, (L.V0 * ∏ p, L.wt p (d p)) * ‖ampGen L d‖ ^ 2 := by
        refine Finset.sum_le_sum (fun d _ => ?_)
        refine mul_le_mul_of_nonneg_right (hU d _ ?_) (by positivity)
        intro x hx
        exact (Finset.mem_filter.mp hx).2
    _ = L.V0 * ∑ d, (∏ p, L.wt p (d p)) * ‖ampGen L d‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun d _ => by ring)

theorem sum_prodG (L : PN.LocalNG Cl Nu) :
    ∑ d, (∏ p, L.wt p (d p)) * ‖ampGen L d‖ ^ 2 = ∏ p, ∑ d, L.wt p d * ‖L.aZ p d‖ ^ 2 := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  unfold ampGen
  rw [norm_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]

theorem meanAmplitudeGeneric_holds : MeanAmpGen := by
  intro Cl Nu L C1 C0 r hb hZ hM hU S
  have hH : ∀ p, 1 ≤ L.H p := hb.2.1
  have hV : 0 ≤ L.V0 := hb.2.2.2.2.2.1
  have hng : ∀ p, 0 ≤ L.ngen p := fun p => Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.ngen_nonneg L C0 r hb hM p
  have hY1 : ∀ p, (1 : ℝ) ≤ if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1 := by
    intro p
    split_ifs
    · have : 1 ≤ L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := one_le_pow₀ (hH p)
      linarith
    · exact le_refl _
  have h3 : ∀ p, L.nn p ≤
      (if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1) * L.ngen p := by
    intro p
    split_ifs with hp
    · exact hM.2 p hp
    · rw [one_mul, hM.1 p hp]
  have hloc : ∀ p, ∑ d, L.wt p d * ‖L.aZ p d‖ ^ 2 ≤ (L.H p ^ (C1 * (r + 1) ^ 2) *
      (if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1)) * L.ngen p := by
    intro p
    refine (hZ p).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (h3 p) (by have := hH p; positivity)
  have hprod : ∏ p, ∑ d, L.wt p d * ‖L.aZ p d‖ ^ 2 ≤ ∏ p, (L.H p ^ (C1 * (r + 1) ^ 2) *
      (if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1)) * L.ngen p :=
    Finset.prod_le_prod (fun p _ => Finset.sum_nonneg (fun d _ => mul_nonneg (hb.1 p d) (by positivity)))
      (fun p _ => hloc p)
  have hfin := Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.finish L (fun p => L.H p ^ (C1 * (r + 1) ^ 2))
    (fun p => if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1)
    (fun p => one_le_pow₀ (hH p)) hY1 (PN.e7 C1 C0 r) (by
      intro p
      show (if p ∈ L.Om then (4 : ℝ) else 1) * (L.H p ^ (C1 * (r + 1) ^ 2) *
        (if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1)) ≤
        L.H p ^ (C1 * (r + 1) ^ 2 + C0 * (r + 1) ^ 2 + 2 * (2 * r + 2) + 5)
      have e : L.H p ^ (C1 * (r + 1) ^ 2 + C0 * (r + 1) ^ 2 + 2 * (2 * r + 2) + 5) =
          L.H p ^ 5 * (L.H p ^ (C1 * (r + 1) ^ 2) * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2))) := by
        rw [← pow_add, ← pow_add]; congr 1; ring
      have hA : 1 ≤ L.H p ^ (C1 * (r + 1) ^ 2) := one_le_pow₀ (hH p)
      have hB : 1 ≤ L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := one_le_pow₀ (hH p)
      rw [e]
      split_ifs with hp
      · have h2 := Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.two_le_H L hb p hp
        have h32 : (32 : ℝ) ≤ L.H p ^ 5 := by
          calc (32 : ℝ) = 2 ^ 5 := by norm_num
            _ ≤ L.H p ^ 5 := pow_le_pow_left₀ (by norm_num) h2 5
        have hpos : 0 ≤ L.H p ^ (C1 * (r + 1) ^ 2) * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := by
          positivity
        calc 4 * (L.H p ^ (C1 * (r + 1) ^ 2) * (8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2))))
            = 32 * (L.H p ^ (C1 * (r + 1) ^ 2) * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2))) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h32 hpos
      · have h5 : 1 ≤ L.H p ^ 5 := one_le_pow₀ (hH p)
        rw [one_mul, mul_one]
        nlinarith [mul_le_mul h5 hB zero_le_one (le_trans zero_le_one h5)])
  have h4 : (1 : ℝ) ≤ 4 ^ L.Om.card := one_le_pow₀ (by norm_num)
  have hXY : 0 ≤ ∏ p, L.H p ^ (C1 * (r + 1) ^ 2) *
      (if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1) :=
    Finset.prod_nonneg (fun p _ => mul_nonneg (by have := hH p; positivity) (le_trans zero_le_one (hY1 p)))
  have hfin' : ∏ p, L.H p ^ (C1 * (r + 1) ^ 2) *
      (if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1) ≤ L.Htot ^ PN.e7 C1 C0 r := by
    nlinarith
  have hngP : 0 ≤ ∏ p, L.ngen p := Finset.prod_nonneg (fun p _ => hng p)
  calc ∑ x ∈ S, weightedGenericAmplitudeSq L x.1 x.2 ≤ L.V0 * ∑ d, (∏ p, L.wt p (d p)) * ‖ampGen L d‖ ^ 2 := step1G L hU S
    _ = L.V0 * ∏ p, ∑ d, L.wt p d * ‖L.aZ p d‖ ^ 2 := by rw [sum_prodG]
    _ ≤ L.V0 * ∏ p, (L.H p ^ (C1 * (r + 1) ^ 2) *
          (if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1)) * L.ngen p :=
        mul_le_mul_of_nonneg_left hprod hV
    _ = L.V0 * ((∏ p, L.H p ^ (C1 * (r + 1) ^ 2) *
          (if p ∈ L.Om then 8 * L.H p ^ (C0 * (r + 1) ^ 2 + 2 * (2 * r + 2)) else 1)) * ∏ p, L.ngen p) := by
        rw [Finset.prod_mul_distrib]
    _ ≤ L.V0 * (L.Htot ^ PN.e7 C1 C0 r * ∏ p, L.ngen p) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hfin' hngP) hV
    _ = L.Htot ^ PN.e7 C1 C0 r * L.ngenTot := by unfold PN.LocalNG.ngenTot; ring

theorem sqrt_add_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (√a + √b) ^ 2 ≤ 2 * (a + b) := by
  nlinarith [sq_nonneg (√a - √b), Real.sq_sqrt ha, Real.sq_sqrt hb]

theorem forty_le_exp : (40 : ℝ) ≤ Real.exp 32 := by
  have h := Real.add_one_le_exp (16 : ℝ)
  have e : Real.exp 32 = Real.exp 16 * Real.exp 16 := by rw [← Real.exp_add]; norm_num
  rw [e]; nlinarith

theorem pg_le {D : D7} {large₂ : SizeData₂ D} {Cl Cg CT : ℝ} (hK : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoParameterConditions D large₂ Cl Cg CT) {X : HidaSetting D}
    (Y : Full X) (hTC : ∀ i : Fin 2, Fintype.card {v : Y.TR.Pl // Fintype.card (Y.TR.Fq v) = D.host.g i} = D.R.f) :
    PgC Y ≤ (4 : ℝ) ^ D.R.f := by
  have hL : 0 < large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hb : 1 < large₂.sc.b := by
    unfold Formalism.BasicNotions.Scale.b
    have := Real.add_one_lt_exp (ne_of_gt hL); linarith
  have hk5 : 5 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hk : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk5
  have hkb : (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
  have h8 : (3 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hkb 8)
  have hg : ∀ i : Fin 2, (1 : ℝ) + 3 / (D.host.g i : ℝ) ≤ 2 := by
    intro i
    have h3 : (3 : ℝ) ≤ D.host.g i := h8.trans (hK.2.1 i).1
    have : 3 / (D.host.g i : ℝ) ≤ 1 := (div_le_one (by linarith)).2 h3
    linarith
  have h2 := Formalism.L2.SG.Pf.SatGram.prod_two (fun v => Fintype.card (Y.TR.Fq v)) (D.host.g 0) (D.host.g 1)
    D.host.g_ne (fun v => Y.TR.card_q v) (fun q : ℕ => (1 + 3 / (q : ℝ)))
  unfold PgC
  rw [h2, hTC 0, hTC 1]
  have e : (4 : ℝ) ^ D.R.f = 2 ^ D.R.f * 2 ^ D.R.f := by rw [← mul_pow]; norm_num
  rw [e]
  have p0 : 0 ≤ (1 : ℝ) + 3 / (D.host.g 0 : ℝ) := by positivity
  have p1 : 0 ≤ (1 : ℝ) + 3 / (D.host.g 1 : ℝ) := by positivity
  exact mul_le_mul (pow_le_pow_left₀ p0 (hg 0) _) (pow_le_pow_left₀ p1 (hg 1) _) (by positivity) (by positivity)

end Formalism.L2.SG.Pf.MainEqCut

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqCut

theorem typedCountC_of (hS : Formalism.L2.SG.Pf.SatGramLoc.SplitPrimeLoc) (hRC : Formalism.L2.SG.Pf.SatGramLoc.RedCore) :
    TypedCountC := by
  intro D X Y _ i
  rw [Formalism.L2.SG.Pf.SatGram.typed_count' (X := X) hS hRC Y.TR i]
  have h := Formalism.L2.SG.Pf.RowDictPf.f_eq X
  unfold Formalism.MainNotions.S.AutInst.f at h
  exact h

theorem diagNumC_of (hTC : TypedCountC) : DiagNumC := by
  intro Cg cb Cw cT CT C0 A CB C4 hCB hC4
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u _ hK2 hT hG => ?_⟩
  have hPg := pg_le hK2 Y (hTC D X Y hT)
  have hPg0 : 0 ≤ PgC Y := Finset.prod_nonneg fun v _ => by positivity
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have hc := Formalism.MainNotions.LatticeGluingRadicals.d_card D
    have : 0 < Fintype.card (InfinitePlace D.host.E) := Fintype.card_pos
    rw [hc] at this
    exact_mod_cast this
  have hf1n : 1 ≤ D.R.f := by exact_mod_cast hf1
  have hL1 : 1 < large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L; exact Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := by unfold Formalism.BasicNotions.Scale.b; exact Real.log_exp _
  have hm : mR D = (D.R.m : ℝ) := by unfold mR; exact_mod_cast D.R.rS_two
  have hm2 : (2 : ℝ) ≤ mR D := by rw [hm]; exact_mod_cast D.R.two_le_m
  have hm5 : (32 : ℝ) ≤ mR D ^ 5 := by
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ mR D ^ 5 := pow_le_pow_left₀ (by norm_num) hm2 5
  set t : ℝ := mR D ^ 5 * D.R.f * large₂.sc.L with ht
  have ht32 : 32 * (D.R.f : ℝ) ≤ t := by
    rw [ht]
    have : (32 : ℝ) * D.R.f * 1 ≤ mR D ^ 5 * D.R.f * large₂.sc.L :=
      mul_le_mul (mul_le_mul_of_nonneg_right hm5 (by positivity)) hL1.le zero_le_one (by positivity)
    linarith
  have ht0 : 0 ≤ t := by linarith
  set M : ℝ := max CB C4 with hM
  have hM0 : 0 ≤ M := le_trans hCB (le_max_left _ _)
  have hE1 : 1 ≤ Real.exp (M * t) := Real.one_le_exp (mul_nonneg hM0 ht0)
  have hgB : gamB D large₂ CB ≤ Real.exp (M * t) := by
    unfold gamB
    rw [hlogb]
    apply Real.exp_le_exp.mpr
    have : CB * mR D ^ 5 * D.R.f * large₂.sc.L = CB * t := by rw [ht]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) ht0
  have hgB0 : 0 ≤ gamB D large₂ CB := by unfold gamB; positivity
  have heL : epsL D ≤ 1 := by
    unfold epsL
    rw [Real.exp_le_one_iff]
    have hk : (1 : ℝ) ≤ D.R.k := by
      have := D.R.two_le_m; have := D.R.m_add_three_le_k
      exact_mod_cast (show 1 ≤ D.R.k by omega)
    have := Real.log_nonneg hk
    have : 0 ≤ (1 / 3 : ℝ) * D.R.k * D.R.f * Real.log D.R.k := by positivity
    linarith
  have heL0 : 0 ≤ epsL D := by unfold epsL; positivity
  have heN : epsNG D large₂ C4 ≤ Real.exp (M * t) := by
    unfold epsNG
    rw [hlogb]
    have h1 : ((2 : ℝ) ^ (D.R.k - 2 * D.R.rS - 5))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have h2 : Real.exp (C4 * mR D ^ 5 * D.R.f * large₂.sc.L) ≤ Real.exp (M * t) := by
      apply Real.exp_le_exp.mpr
      have : C4 * mR D ^ 5 * D.R.f * large₂.sc.L = C4 * t := by rw [ht]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) ht0
    calc ((2 : ℝ) ^ (D.R.k - 2 * D.R.rS - 5))⁻¹ * Real.exp (C4 * mR D ^ 5 * D.R.f * large₂.sc.L)
        ≤ 1 * Real.exp (M * t) := mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = Real.exp (M * t) := one_mul _
  have heN0 : 0 ≤ epsNG D large₂ C4 := by unfold epsNG; positivity
  have hGam : (D.mem u).A.GamP = Real.exp (large₂.CGam * t) := by
    rw [← Real.exp_log (lt_trans zero_lt_one (D.mem u).A.one_lt_gammaP), large₂.Gam_eq u, ht, hm]
    congr 1; ring
  have h40 : 10 * (4 : ℝ) ^ D.R.f ≤ Real.exp t := by
    have a1 : 10 * (4 : ℝ) ^ D.R.f ≤ (40 : ℝ) ^ D.R.f := by
      have : (10 : ℝ) ≤ 10 ^ D.R.f := by
        calc (10 : ℝ) = 10 ^ 1 := by norm_num
          _ ≤ 10 ^ D.R.f := pow_le_pow_right₀ (by norm_num) hf1n
      have e : (40 : ℝ) ^ D.R.f = 10 ^ D.R.f * 4 ^ D.R.f := by rw [← mul_pow]; norm_num
      rw [e]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have a2 : (40 : ℝ) ^ D.R.f ≤ Real.exp 32 ^ D.R.f := pow_le_pow_left₀ (by norm_num) forty_le_exp _
    have a3 : Real.exp 32 ^ D.R.f = Real.exp (D.R.f * 32) := (Real.exp_nat_mul _ _).symm
    have a4 : Real.exp (D.R.f * 32) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
    linarith
  rw [hGam]
  calc (√(PgC Y * (gamB D large₂ CB + 2 * epsL D)) + √(PgC Y * (epsL D + epsNG D large₂ C4))) ^ 2
      ≤ 2 * (PgC Y * (gamB D large₂ CB + 2 * epsL D) + PgC Y * (epsL D + epsNG D large₂ C4)) :=
        sqrt_add_sq_le (by positivity) (by positivity)
    _ = 2 * PgC Y * (gamB D large₂ CB + 3 * epsL D + epsNG D large₂ C4) := by ring
    _ ≤ 2 * (4 : ℝ) ^ D.R.f * (5 * Real.exp (M * t)) := by
        apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
        linarith
    _ = (10 * (4 : ℝ) ^ D.R.f) * Real.exp (M * t) := by ring
    _ ≤ Real.exp t * Real.exp (M * t) := mul_le_mul_of_nonneg_right h40 (by positivity)
    _ = Real.exp ((M + 1) * t) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (large₂.CGam * t) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hG ht0)

theorem typedCountC_holds : TypedCountC :=
  typedCountC_of Formalism.L2.SG.Pf.SatGramLoc.split_prime_local_holds Formalism.L2.SG.Pf.SatGramLoc.reduction_structure_holds

theorem diagNumC_holds : DiagNumC := diagNumC_of typedCountC_holds

end Formalism.L2.SG.Pf
