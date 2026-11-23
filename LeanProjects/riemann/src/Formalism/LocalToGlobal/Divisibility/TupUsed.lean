import Mathlib
import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces
import Formalism.LocalToGlobal.Divisibility.MemberDIV
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace Formalism.L2.DIV

open Formalism.L2.Rows Formalism.L2.Indef

section IndefiniteRowSideFullHecke

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

def TupAllUsed (P : RowSideFamily ex) : Prop := ∀ t : P.T, Formalism.IndefR.RecTie.Used0 D (P.I.tup t)

theorem tupAllUsed_iff_cover (P : RowSideFamily ex) :
    TupAllUsed P ↔ ∀ t : P.T, t = P.A3.A.μ0 ∨ ∃ w, t = (P.A3.indefDown P.S0).μ (D.plEq w) := by
  have hT : TupTie D P.A3.A (P.A3.indefDown P.S0) P.I.tup := by
    exact P.tied.div.tup
  refine ⟨fun h t => ?_, fun h t => ?_⟩
  swap
  · rcases h t with rfl | ⟨w, rfl⟩
    · exact Or.inl hT.mu0
    · exact Or.inr ⟨w, (hT.muAt w).symm⟩
  rcases h t with h0 | ⟨w, hw⟩
  · exact Or.inl (hT.inj (h0.trans hT.mu0.symm))
  · exact Or.inr ⟨w, hT.inj (hw.trans (hT.muAt w))⟩

theorem tupAllUsed_of_cover (P : RowSideFamily ex)
    (h : ∀ t : P.T, t = P.A3.A.μ0 ∨ ∃ w, t = (P.A3.indefDown P.S0).μ (D.plEq w)) : TupAllUsed P := by
  have hT : TupTie D P.A3.A (P.A3.indefDown P.S0) P.I.tup := by
    exact P.tied.div.tup
  intro t
  rcases h t with rfl | ⟨w, rfl⟩
  · exact Or.inl hT.mu0
  · exact Or.inr ⟨w, (hT.muAt w).symm⟩

def LiftInvariantSpan (P : RowSideFamily ex) : Prop :=
  ∀ (i : Fin D.R.m) (t : P.T), Formalism.BasicNotions.Idx.Z0 D (P.I.tup t) ((i : ℕ) + 1) =
    Submodule.span ℂ (Set.range fun k =>
      (D.what₂.jMt (P.I.tup t) ((i : ℕ) + 1))
        (P.I.eMt i t ((lZ0 D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec (Pi.single k 1))))

def RationalLiftSpanAtUsedTuples (P : RowSideFamily ex) : Prop :=
  ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) →
    Formalism.BasicNotions.Idx.Z0 D (P.I.tup t) ((i : ℕ) + 1) =
    Submodule.span ℂ (Set.range fun k =>
      (D.what₂.jMt (P.I.tup t) ((i : ℕ) + 1))
        (P.I.eMt i t ((lZ0 D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec (Pi.single k 1))))

def ThTheta (P : RowSideFamily ex) : Prop :=
  ∀ (i : Fin D.R.m) (t : P.T) x,
    D.what₂.thetaP (P.I.tup t) ((i : ℕ) + 1) (D.what₂.jMt (P.I.tup t) ((i : ℕ) + 1) (P.I.eMt i t x)) =
      P.I.jW i (((P.A3.indefDown P.S0).θ i t).mulVec ((lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec x))

def ThThetaG (P : RowSideFamily ex) : Prop :=
  ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) → ∀ x,
    D.what₂.thetaP (P.I.tup t) ((i : ℕ) + 1) (D.what₂.jMt (P.I.tup t) ((i : ℕ) + 1) (P.I.eMt i t x)) =
      P.I.jW i (((P.A3.indefDown P.S0).θ i t).mulVec ((lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec x))

def DcPtG (P : RowSideFamily ex) : Prop :=
  ∀ (u : D.what₂.Word) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) →
    ∀ (x : Fin (P.Dc.a (P.I.wU u)) → D.what₂.LL) (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
    D.what₂.embLL (P.Dc.Pt (P.I.wU u) t x F) =
      D.what₂.perCol u (P.I.tup t) (D.jN u (P.I.eNu u x)) (P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))

variable {P : RowSideFamily ex}

theorem lift_invariant_span_used_of (h : LiftInvariantSpan P) : RationalLiftSpanAtUsedTuples P := fun i t _ => h i t

theorem lift_invariant_span_of_used (hU : TupAllUsed P) (h : RationalLiftSpanAtUsedTuples P) : LiftInvariantSpan P := fun i t => h i t (hU t)

theorem thThetaG_of (h : ThTheta P) : ThThetaG P := fun i t _ x => h i t x

theorem thTheta_of_G (hU : TupAllUsed P) (h : ThThetaG P) : ThTheta P := fun i t x => h i t (hU t) x

theorem dcPtG_of (h : RowsHoldDcPt3 P) : DcPtG P := fun u t _ x F => h u t x F

theorem dcPt_of_G (hU : TupAllUsed P) (h : DcPtG P) : RowsHoldDcPt3 P := fun u t x F => h u t (hU t) x F

theorem rowGuarded_iff (hU : TupAllUsed P) : LiftInvariantSpan P ∧ ThTheta P ↔ RationalLiftSpanAtUsedTuples P ∧ ThThetaG P := ⟨fun h => ⟨lift_invariant_span_used_of h.1, thThetaG_of h.2⟩, fun h => ⟨lift_invariant_span_of_used hU h.1, thTheta_of_G hU h.2⟩⟩

theorem dcPt_iff (hU : TupAllUsed P) : RowsHoldDcPt3 P ↔ DcPtG P := ⟨dcPtG_of, dcPt_of_G hU⟩

open Classical in

structure NumTieG (P : RowSideFamily ex) : Prop where

  Ij : ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) → ∀ w,
    D.what₂.Ij (P.I.tup t) ((i : ℕ) + 1) w = (P.A3.indefDown P.S0).Iw i t (D.plEq w)

  jw : ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) → ∀ w,
    D.what₂.jw (P.I.tup t) ((i : ℕ) + 1) w =
      Formalism.DivisionValues.jw ((P.A3.A.side P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs)).HT i t) (D.plEq w)
        ((P.A3.A.side P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs)).Tl i t)

  etaJ : ∀ (i : Fin D.R.m) w, D.what₂.etaJ ((i : ℕ) + 1) w =
    if D.plEq w ∈ (P.A3.indefDown P.S0).Tw then
      P.A3.A.fam.etaJ P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i ((P.A3.indefDown P.S0).μ (D.plEq w)) (D.plEq w) else 0

theorem numTieG_of (h : NumTie D P.A3.A (P.A3.indefDown P.S0) P.I.tup) : NumTieG P := ⟨fun i t _ w => h.Ij i t w, fun i t _ w => h.jw i t w, h.etaJ⟩

theorem numTie_of_G (hU : TupAllUsed P) (h : NumTieG P) : NumTie D P.A3.A (P.A3.indefDown P.S0) P.I.tup := ⟨fun i t w => h.Ij i t (hU t) w, fun i t w => h.jw i t (hU t) w, h.etaJ⟩

theorem numTie_iff_G (hU : TupAllUsed P) : NumTie D P.A3.A (P.A3.indefDown P.S0) P.I.tup ↔ NumTieG P := ⟨numTieG_of, numTie_of_G hU⟩

structure DivRows3G (P : RowSideFamily ex) : Prop where

  sharpRR : HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (P.A3.indefDown P.S1).RR (P.A3.indefDown P.S1).XE P.I.eRR

  baseRR : HLatTie ex.p0.s.RR (P.A3.indefDown P.S0).RR (P.A3.indefDown P.S0).XE P.I.eRR0

  divisionRows_rationalLift : RationalLiftSpanAtUsedTuples P

  thTheta : ThThetaG P

  num : NumTieG P

  colsBk : ∀ u x y, D.div.Bk u (P.I.eNu u x) (P.I.eRR y) =
    (P.A3.colData2 P.C (fun _ => ⊥) (fun _ _ => ⊥) (fun _ _ _ _ => 0)).B (P.I.wU u) x y

theorem DivRows3.toG (h : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) : DivRows3G P where
  sharpRR := h.sharpRR
  baseRR := h.baseRR
  divisionRows_rationalLift := lift_invariant_span_used_of h.divisionRows_rationalLift
  thTheta := thThetaG_of h.thTheta
  num := numTieG_of h.num
  colsBk := h.colsBk

theorem DivRows3G.toRows (hU : TupAllUsed P) (h : DivRows3G P) :
    DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I where
  sharpRR := h.sharpRR
  baseRR := h.baseRR
  divisionRows_rationalLift := lift_invariant_span_of_used hU h.divisionRows_rationalLift
  thTheta := thTheta_of_G hU h.thTheta
  num := numTie_of_G hU h.num
  colsBk := h.colsBk

theorem divRows3_iff_G (hU : TupAllUsed P) :
    DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I ↔ DivRows3G P := ⟨DivRows3.toG, DivRows3G.toRows hU⟩

end IndefiniteRowSideFullHecke

section Member

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.BasicNotions.DV Formalism.L2.Col Formalism.L2.DIV.Member

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {X : Fields} {e : X.Tau → (X.E →+* D.what₂.LL)} {Pr : Primes (fieldsLL D X e)}
  {W : Wts (fieldsLL D X e) Pr.Word D.R} {Ch : Chars (fieldsLL D X e) Pr D.R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ} {Gc : ChGlob (fieldsLL D X e) D.R.m} {m2 : ℕ}
  {F : ColFam W Ch sel Sg Gc m2 D.what₂.Word} {hX : (fieldsLL D X e).Ok}
  {v0 : InfinitePlace D.what₂.LL} {TU : Finset (Tup X.F X.E D.what₂.LL Sg)}
  {Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs D.R.r → D.what₂.LL)}
  {xiVal : Tup X.F X.E D.what₂.LL Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ}
  {trIv : Fin D.R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL}
  {hE : ∀ x, (evGSD W Ch sel ((famM W Ch sel hX v0 TU Xg xiVal trIv).fam3.base3.μ0 : TupF (X := fieldsLL D X e) TU).1
      (rPsymF (R := D.R) Ch) (F.wd x)).Ok}
  {ev : ∀ (Zs : DefSub (famM W Ch sel hX v0 TU Xg xiVal trIv).fam3.amb3) (t : TupF (X := fieldsLL D X e) TU),
      (Fin (((famM W Ch sel hX v0 TU Xg xiVal trIv).side3 (rPsymF (R := D.R) Ch).grp (rPsymF (R := D.R) Ch).chr Zs).nV t) →
        D.what₂.LL) →ₗ[D.what₂.LL] V0X W Ch sel t.1 Xg (rPsymF (R := D.R) Ch)}
  {Sp : ∀ Zs, SPer ((colM F hX v0 TU Xg xiVal trIv hE ev).face Zs)}

theorem tupAllUsed_of_TU (R : RestM F hX v0 TU Xg xiVal trIv hE ev Sp ex)
    (hTU : (↑TU : Set (Tup X.F X.E D.what₂.LL Sg)) ⊆
      insert ((famM W Ch sel hX v0 TU Xg xiVal trIv).A.μ0 : TupF (X := fieldsLL D X e) TU).1
        (Set.range fun w => (((famM W Ch sel hX v0 TU Xg xiVal trIv).indefDown R.S0).μ (D.plEq w)).1)) :
    TupAllUsed R.extendedDatum := by
  refine tupAllUsed_of_cover R.extendedDatum (fun t => ?_)
  obtain ⟨τ, hτ⟩ := t
  rcases hτ with h0 | hU
  · left
    exact Subtype.ext h0
  · rcases hTU hU with h1 | ⟨w, hw⟩
    · left
      exact Subtype.ext h1
    · right
      exact ⟨w, Subtype.ext hw.symm⟩

theorem tupAllUsed_iff_TU (R : RestM F hX v0 TU Xg xiVal trIv hE ev Sp ex) :
    TupAllUsed R.extendedDatum ↔ (↑TU : Set (Tup X.F X.E D.what₂.LL Sg)) ⊆
      insert ((famM W Ch sel hX v0 TU Xg xiVal trIv).A.μ0 : TupF (X := fieldsLL D X e) TU).1
        (Set.range fun w => (((famM W Ch sel hX v0 TU Xg xiVal trIv).indefDown R.S0).μ (D.plEq w)).1) := by
  refine ⟨fun h => ?_, tupAllUsed_of_TU R⟩
  intro τ hτ
  rcases (tupAllUsed_iff_cover R.extendedDatum).1 h (⟨τ, Or.inr hτ⟩ : TupF (X := fieldsLL D X e) TU) with h0 | ⟨w, hw⟩
  · exact Or.inl (congrArg Subtype.val h0)
  · exact Or.inr ⟨w, (congrArg Subtype.val hw).symm⟩

end Member

end Formalism.L2.DIV
