import Formalism.LocalToGlobal.GlobalTheory.FamRows
import Formalism.LocalToGlobal.GlobalTheory.ConclusionsOfPrimeNumberTheoremAP

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamColC

open Formalism Formalism.HN Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.FamCol

section Obj

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

abbrev eF (α : Type) [Fintype α] : α ≃ Fin (Fintype.card α) := Fintype.equivFin α

def rFr {α : Type} [Fintype α] [DecidableEq α] (X : InfinitePlace K → Matrix α α ℂ) :
    InfinitePlace K → Matrix (Fin (Fintype.card α)) (Fin (Fintype.card α)) ℂ :=
  fun w => Matrix.reindex (eF α) (eF α) (X w)

def Jg (κ κ₁ : Type) [Fintype κ] [DecidableEq κ] [Fintype κ₁] :
    Matrix (Fin (Fintype.card (κ ⊕ κ₁))) (Fin (Fintype.card κ)) ℂ :=
  Matrix.reindex (eF (κ ⊕ κ₁)) (eF κ) (Matrix.fromRows (1 : Matrix κ κ ℂ) (0 : Matrix κ₁ κ ℂ))

def Jo (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] [DecidableEq κ₁] :
    Matrix (Fin (Fintype.card (κ ⊕ κ₁))) (Fin (Fintype.card κ₁)) ℂ :=
  Matrix.reindex (eF (κ ⊕ κ₁)) (eF κ₁) (Matrix.fromRows (0 : Matrix κ κ₁ ℂ) (1 : Matrix κ₁ κ₁ ℂ))

def famQC [IsTotallyComplex K] (m : ℕ) (C : ColObj K I) (P : PlDat K I) (R : RowArg C) : LChain6.FamC I m where
  K := K
  Wd := R.Wd
  Dall := Fintype.card (R.κ ⊕ R.κ₁)
  D := Fintype.card R.κ
  D1 := Fintype.card R.κ₁
  V := fun u => (C.M u).V
  r := fun u => Fintype.card (C.M u).ι
  Vf := fun u => (C.Mf u).V
  d := fun u => Fintype.card (C.Mf u).ι
  b' := R.b'.reindex (eF R.κ)
  X' := rFr R.X'
  cc := R.cc
  b := fun u => (C.M u).b.reindex (eF (C.M u).ι)
  X := fun u => rFr (C.M u).X
  M := fun u => (C.M u).L
  N0 := C.Nu
  bf := fun u => (C.Mf u).b.reindex (eF (C.Mf u).ι)
  Xf := fun u => rFr (C.Mf u).X
  Mf := fun u => (C.Mf u).L
  j := C.incl
  σ := C.sgExp
  τ := C.tauExp
  B := R.B
  v := R.v
  Y := fun u => Matrix.reindex (eF (C.M u).ι) (eF (C.M u).ι) (R.Y u)
  Y' := Matrix.reindex (eF R.κ) (eF R.κ) R.Y'
  Pf := MatrixLatticeEstimates.toFin R.Bf
  Vr := MatrixLatticeEstimates.toFinV (fun u => C.Vr u R.v)
  ga := R.γ
  c := fun _ => 1
  Vrow := 1
  U := fun _ => 1
  J := Jg R.κ R.κ₁
  J1 := Jo R.κ R.κ₁
  S := (famC m C P R).S
  gain := (famC m C P R).gain
  Fj := (famC m C P R).Fj
  Ej := (famC m C P R).Ej
  iop := (famC m C P R).iop
  T := C.T
  h := R.h
  lam := C.lamT
  Dstar := C.Dstar
  η0 := R.η0
  η1 := R.η1
  e0 := R.e0

def rowsQC [IsTotallyComplex K] {m : ℕ} {C : ColObj K I} {P : PlDat K I} {R : RowArg C}
    (Rw : LChain6.Rows (famC m C P R)) : LChain6.Rows (famQC m C P R).toFam :=
  ⟨Rw.D, Rw.XE, Rw.R, Rw.ψ⟩

structure RowTr [Fintype I] (C : ColObj K I) (R : RowArg C) (x ε : ℝ) : Prop where
  X' : ∀ w, IsUnit (R.X' w).det
  Y : ∀ u, IsUnit (R.Y u).det
  Y' : IsUnit R.Y'.det
  cc_fg : R.cc.FG
  cc_span : Submodule.span K (R.cc : Set R.Wd) = ⊤
  into : ∀ u, (C.Npr u).map ((R.B u).restrictScalars (𝓞 K)) ≤ R.cc
  ht : ∀ u, R.B u ≠ 0 → htMap (C.M u).b (C.M u).X R.b' R.X' (R.B u) ≤ R.h u
  block : ∀ u (k : R.κ) (j : (C.M u).ι), R.Ball u (Sum.inl k) j =
    (R.Y'⁻¹ * (LinearMap.toMatrix (C.M u).b R.b' (R.B u)).map R.v.embedding * R.Y u) k j
  γ : ∀ u, 0 < R.γ u
  Ball : ∀ u, R.Ball u = R.Bf u * C.Vr u R.v
  η0_ge : -1 ≤ R.η0
  η0_le : R.η0 ≤ LChain6.E8 x ε
  η1_le : R.η1 ≤ LChain6.E8 x ε
  exponent_bound_ter : 0 ≤ R.e0
  sqrt_error_le_half : Real.sqrt R.e0 ≤ LChain6.E8 x ε
  inputS : MatrixLatticeEstimates.InputSG R.Bf R.γ C.Dstar R.η0 R.η1 R.e0
  irr : (1 - LChain6.E7 x ε) * (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) ≤ (Fintype.card R.κ : ℝ)

end Obj

section Fam7

variable {H : Type} {W : H → Type}

def designPointFamily (m : ℕ) (Q : ∀ u0, Pt (W u0)) : ∀ u0, LChain6.FamC (W u0) m :=
  fun u0 => famQC m (Q u0).C (Q u0).P (Q u0).R

end Fam7

section Collected

open Formalism.L2.Indef Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.GlobalTheoryTheory.FamRows

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}
  {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}

structure ExtHyp7 [Fintype I] (C : ColObj K I) (L : ColLink C Dc) (S : IndefCols Df Dc Sp N) (X : RowExt C S.D)
    (x ε : ℝ) : Prop where
  block : ∀ u (k : Fin S.D) (j : (C.M u).ι), (X.Bf u * C.Vr u Bs.v0) (Sum.inl k) j =
    ((dualFrame S.XE Bs.v0)⁻¹ * (LinearMap.toMatrix (C.M u).b (Pi.basisFun K (Fin S.D)).dualBasis
      (colB L S u)).map Bs.v0.embedding * (C.M u).X Bs.v0) k j
  γ : ∀ u, 0 < X.γ u
  η0_ge : -1 ≤ X.η0
  η0_le : X.η0 ≤ LChain6.E8 x ε
  η1_le : X.η1 ≤ LChain6.E8 x ε
  exponent_bound_ter : 0 ≤ X.e0
  sqrt_error_le_half : Real.sqrt X.e0 ≤ LChain6.E8 x ε
  inputS : Formalism.LFunctionChainParameters.MatrixLatticeEstimates.InputSG X.Bf X.γ C.Dstar X.η0 X.η1 X.e0
  irr : (1 - LChain6.E7 x ε) * (Fintype.card (Fin S.D ⊕ X.κ₁) : ℝ) ≤ (S.D : ℝ)

def LineClausesFromPackage : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (I : Type) [Fintype I]
    {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ} (A : FamIn K G Pl0 T m) (s : ℕ), A.fam.Ok s →
    A.fam.TypesSep →
    ∀ (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (Cn CH : ℝ)
    (Pk : IndefPkg A.fam.amb (faceC A P0 ψ0 P1 ψ1 Dc Sp Zsc) Cn CH)
    (C : ColObj K I) (L : ColLink C (Dc Pk.Zs)) (X : RowExt C Pk.core.cols.D) (hu : I → ℝ) (x ε : ℝ),
    L.Tied → (∀ u, Nonempty (RowIn Pk.core.cols (L.wU u) (L.NuD u) (sgD C u) (hu u))) →
    ExtHyp7 C L Pk.core.cols X x ε →
    RowTr C (rowArg C L Pk.core.cols X hu) x ε

end Collected

def SameNumbersTwoLayers : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (I : Type) [Fintype I] (m : ℕ) (C : ColObj K I)
    (P : PlDat K I) (R : RowArg C), ColFacts C → (∀ w, IsUnit (R.X' w).det) → R.cc.FG →
    SameNumbers (famQC m C P R).toFam (famC m C P R) ∧ SameNumbers (famC m C P R) (famQC m C P R).toFam

section Family

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
  Formalism.LFunctionChainParameters.LChain7

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

def DesignPointDataEqFamilyData : Prop :=
  ∀ (G : Glob) (cHH : ℝ) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Q : ∀ u0 : H, Pt (W u0)),
    (∀ u0, ColFacts (Q u0).C) → (∀ u0 v, IsUnit (((Q u0).R.X' v)).det) → (∀ u0, (Q u0).R.cc.FG) →
    mkData G cHH D ell N TT T2 a w (fun u0 => (designPointFamily m Q u0).toFam) = dataQ G cHH D ell N TT T2 a w Q

def LossHypothesesIff : Prop :=
  ∀ (D : ArithData H) (G : Glob) (C : Consts) (N : ℕ) (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (Q : ∀ u0 : H, Pt (W u0)) (Lp : H → LossP H m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → H → Prop) (Sig : ℕ → ℝ) (Cord eW KW : ℝ),
    LossHypD D G C N TT a w (fun u0 => (designPointFamily m Q u0).toFam) Lp P cand PR BAD Sig Cord eW KW ↔
      LossHypD D G C N TT a w (famQ m Q) Lp P cand PR BAD Sig Cord eW KW

def GainConditionIffDesignPointFamily : Prop :=
  ∀ (Q : ∀ u0 : H, Pt (W u0)) (u0 : H) (Ps : Finset ℕ) (cl : ℕ → DeficitSplitLemmas.PClass) (Tn an : ℝ),
    Fam6.GainIn (designPointFamily m Q u0).toFam Ps cl Tn an ↔ Fam6.GainIn (famQ m Q u0) Ps cl Tn an

def DivisionConditionIffDesignPointFamily : Prop :=
  ∀ (G : Glob) (C : Consts) (TT T2 : Finset H) (a : H → ℝ) (Q : ∀ u0 : H, Pt (W u0))
    (Rw : ∀ u0, Rows (famQ m Q u0)) (logOm C0 : ℝ) (g₁ g₂ : ℕ),
    (∀ u0, ColFacts (Q u0).C) →
    (DivIn G C TT T2 a (fun u0 => (designPointFamily m Q u0).toFam) (fun u0 => rowsQC (Rw u0)) logOm C0 g₁ g₂ ↔
      DivIn G C TT T2 a (famQ m Q) Rw logOm C0 g₁ g₂)

end Family

def PlaceFactsIff : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (I : Type) (m : ℕ) (C : ColObj K I)
    (P : PlDat K I) (R : RowArg C) (f g₁ g₂ : ℕ) (Xpp : ℝ), ColFacts C →
    (LChain6.Fam6.PlaceIn' (famQC m C P R).toFam f g₁ g₂ Xpp ↔ LChain6.Fam6.PlaceIn' (famC m C P R) f g₁ g₂ Xpp)

def SublatticeOfColumnLattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (I : Type) (m : ℕ) (C : ColObj K I)
    (P : PlDat K I) (R : RowArg C), ColFacts C → (famQC m C P R).SubIn

def TraceConditionOfLineHypothesesAndDimensionRatio : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (I : Type) [Fintype I] (C : ColObj K I) (R : RowArg C) (sg x ε : ℝ),
    RowHyp C R sg → sg / 2 ≤ LChain6.E8 x ε →
    (1 - LChain6.E7 x ε) * (Fintype.card (R.κ ⊕ R.κ₁) : ℝ) ≤ (Fintype.card R.κ : ℝ) → RowTr C R x ε

def LatticeHypothesesConcrete : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (I : Type) [Fintype I] (m : ℕ) (C : ColObj K I)
    (P : PlDat K I) (R : RowArg C) (Rw : LChain6.Rows (famC m C P R)) (sg Gam C0S delB : ℝ),
    ColFacts C → RowHyp C R sg → 0 < C0S → 0 < Gam → Fintype.card I = ⌈C0S * Gam ^ 2 / sg⌉₊ →
    (∀ u, C.Dstar / Gam ^ 2 / C0S ≤ (Fintype.card (C.Mf u).ι : ℝ)) →
    (famC m C P R).deF ≤ 1 / 4 → (famC m C P R).del ≤ delB →
    LBrDiv.RowsAreDual (famC m C P R) Rw.XE Rw.R Rw.ψ →
    (famQC m C P R).LatIn (rowsQC Rw) sg Gam C0S delB

def DivisionTheoremTraces : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (I : Type) [Fintype I] (m : ℕ) (C : ColObj K I)
    (P : PlDat K I) (R : RowArg C) (Rw : LChain6.Rows (famC m C P R)) (x ε sg Gam C0S : ℝ),
    ColFacts C → RowTr C R x ε → 0 < C0S → 0 < Gam → Fintype.card I = ⌈C0S * Gam ^ 2 / sg⌉₊ →
    LBrDiv.RowsAreDual (famC m C P R) Rw.XE Rw.R Rw.ψ →
    (famQC m C P R).TraceIn (rowsQC Rw) x ε sg Gam C0S

section Core

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
  Formalism.LFunctionChainParameters.LChain7 Formalism.L2.GlobalTheoryTheory.MergeGL2 Formalism.L2.GlobalTheoryTheory.MergeGL2c

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

def Conc7In (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (x ε k v : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Q : ∀ u0 : H, Pt (W u0))
    (Rw : ∀ u0, Rows (famQ m Q u0)) (O : SizeCountLevelObjects H W m TT) (η eK K logOm C0 cZ cL cE5 c5 C0S κ off : ℝ)
    (btH : H → ℝ) (g₁ g₂ : ℕ) : Prop :=
  (∀ u0, (Q u0).OkIn m (PhiSet (H := H)).card g₁ g₂ (XppTx x ε (Fintype.card H : ℝ))) ∧
  (∀ u0, ((Q u0).C.k : ℝ) = k) ∧
  (∀ u0, RowTr (Q u0).C (Q u0).R x ε) ∧
  (∀ u0, Fintype.card (W u0) = ⌈C0S * O.Gam ^ 2 / x ^ (-C.cHH)⌉₊) ∧
  DivIn (glob6 x ε k v g₁ g₂ C.cHH) C TT T2 a (famQ m Q) Rw logOm C0 g₁ g₂ ∧
  ((∀ u0 (u : W u0),
      ZiiR (dataQ (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w Q) cZ O.Sc O.LZ
        (Real.log ((Q u0).C.T u : ℝ)) ≤ (Q u0).C.zLow u ∧
      (Q u0).C.zUp u ≤ ZiiiR (dataQ (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w Q) cZ O.Sc O.LZ
        (Real.log ((Q u0).C.T u : ℝ))) ∧
    0 ≤ cZ ∧ 0 ≤ cL ∧ 0 ≤ O.Sc ∧ O.Sc ≤ Real.exp (x ^ (ε / 4)) ∧ O.LZ ≤ cL * Real.log (aTx x ε * (2 * v)) ∧
    cSlopeZ cZ cL (c5 + 1) ≤ C.cSlope) ∧
  ((∀ u0, exactMain (dataQ (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w Q) O.bN u0 - cE5 * Real.log (bTx x ε) - 1
        ≤ (Q u0).C.xLow ∧
      (Q u0).C.xUp ≤ c5 * (m : ℝ) * x ^ ε ∧ (Q u0).C.xVar ≤ c5 * Real.log k) ∧
    SectionsFourToSixTransfer.LevelWindow (dataQ (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w Q) O.Gam (fun u0 u => (Q u0).C.Xu u) ∧
    1 ≤ O.Gam ∧ Real.log O.Gam / (((PhiSet (H := H)).card : ℝ) * k) ≤ 1 ∧ 0 ≤ c5 ∧ cE5 + 6 ≤ c5 ∧ c5 + 3 ≤ C.cCount ∧
    ∀ u0 j ρ, 0 < O.bN u0 j ρ ∧ w u0 j (ePhi ρ) ≤ O.bN u0 j ρ * (1 + 1 / x) ∧ Real.log (O.bN u0 j ρ) ≤ 2 * x ^ ε) ∧
  3 ≤ C0S ∧
  (O.aM ≤ 2 * aTx x ε ∧ (∀ t, O.Wt t ≤ 2 * bpTx x ε) ∧ (∀ t : TT, O.bt t = btH t) ∧
    ∀ u0 u, (Q u0).C.lamT u
      ≤ lambdaIndex (dataQ (glob6 x ε k v g₁ g₂ C.cHH) C.cHH D ell N TT T2 a w Q) O.aM (O.VV u0 u) O.Wt O.bt) ∧
  Sizes6 x ε eK K k m N TT T2 a w η κ off btH (x ^ (-C.cHH)) O.Gam C0S g₁ g₂

def ConcCoreAt7' (q d : ℕ) [Fact q.Prime] [Fact d.Prime] (A Cord eD eL K cHH eK eW KW ε x : ℝ) : Prop :=
  ∃ (e : ℕ) (W : HA e → Type) (_ : ∀ u0, Fintype (W u0)) (_ : ∀ u0, Nonempty (W u0)) (m : ℕ)
    (k : ℝ) (C : Consts) (N : ℕ)
    (TT T2 : Finset (HA e)) (a btH : HA e → ℝ) (w : HA e → Fin m → E0 × HA e → ℝ)
    (Q : ∀ u0, Pt (W u0)) (Rw : ∀ u0, Rows (famQ m Q u0)) (O : SizeCountLevelObjects (HA e) W m TT)
    (Lp : HA e → LossP (HA e) m)
    (P : PrimeWindowSizeBounds.Par) (cand PR : Finset ℕ) (BAD : ℕ → HA e → Prop) (Sig : ℕ → ℝ) (η κ off : ℝ)
    (g₁ g₂ : ℕ) (logOm C0 cZ cL cE5 c5 C0S : ℝ),
    C.eDiv ≤ eD ∧ C.eLoss ≤ eL ∧ 1 ≤ C.cHH ∧ C.cHH ≤ cHH ∧ ConstsBound C K ∧ 28 ≤ C.cSl1 ∧
    P.e₂ = e ∧ P.η = η ∧ O.Sc = P.Sc ∧
    ((2 ^ e : ℕ) : ℝ) ≤ x ^ A ∧
    g₁.Prime ∧ g₂.Prime ∧
    PerHost e q d logOm ∧
    LossHypD (hostData e q d) (glob6 x ε k (hostV e q d) g₁ g₂ C.cHH) C N TT a w (famQ m Q) Lp P cand PR
      BAD Sig Cord eW KW ∧
    (∀ u0, Fam6.GainIn (famQ m Q u0) (inertPs (hostData e q d) N) (Lp u0).cl (TT.card : ℝ) (aTx x ε)) ∧
    Conc7In (hostData e q d) (hostEll e q d) x ε k (hostV e q d) C N TT T2 a w Q Rw O η eK K logOm
      C0 cZ cL cE5 c5 C0S κ off btH g₁ g₂

def CoreOfConcreteCoreAtPrimes : Prop :=
  ∀ (q d : ℕ) [Fact q.Prime] [Fact d.Prime] (A Cord eD eL K cHH eK eW KW ε x : ℝ),
    ConcCoreAt7' q d A Cord eD eL K cHH eK eW KW ε x → CoreAt7' q d A Cord eD eL K cHH eK eW KW ε x

def MainChainReduction : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧
    ((∀ ε : ℝ, 0 < ε → ε < 1 / 52 →
      ∃ A K cHH eK eW KW x₀ : ℝ, 0 < A ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
          ConcCoreAt7' (q1At ε x) (dAt ε x) A Cord 2 0 K cHH eK eW KW ε x) → LTop7.GrowthBoundAndRiemannHypothesis)

end Core

end Formalism.L2.GlobalTheoryTheory.FamColC

end
