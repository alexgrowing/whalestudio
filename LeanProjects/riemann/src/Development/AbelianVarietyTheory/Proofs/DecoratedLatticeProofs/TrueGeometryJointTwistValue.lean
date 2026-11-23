import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceNormalisedCombinationsPreserveThetaFun
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.QPl.PinComb

variable {D : D7} {c : Comm D}

def mxSub (P : GlobalTheory.FinPl.Pl D → Prop) (S T : HSp D) : AddSubmonoid (WO S T) where
  carrier := {u | GlobalTheory.FinPl.MxAt P u}
  zero_mem' := fun i j => by
    simpa using (GlobalTheory.FinPl.idAt D P).zero_mem
  add_mem' {a b} ha hb := fun i j => by
    simpa using (GlobalTheory.FinPl.idAt D P).add_mem (ha i j) (hb i j)

theorem combAt_aconv {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} (l : List (WO S T →₀ ℂ))
    (hl : ∀ e ∈ l, GlobalTheory.FinPl.CombAt P e) : GlobalTheory.FinPl.CombAt P (aconv l) :=
  GlobalTheory.QPl.ThetaPin.aconv_support (mxSub P S T) l hl

theorem combAt_smul {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} (r : ℂ) {e : WO S T →₀ ℂ}
    (he : GlobalTheory.FinPl.CombAt P e) : GlobalTheory.FinPl.CombAt P (r • e) :=
  fun u hu => he u (Finsupp.support_smul hu)

theorem combAt_zero {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} : GlobalTheory.FinPl.CombAt P (0 : WO S T →₀ ℂ) :=
  fun u hu => by simp at hu

theorem combAt_mono {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ p, P p → P' p) {S T : HSp D} {e : WO S T →₀ ℂ}
    (he : GlobalTheory.FinPl.CombAt P e) : GlobalTheory.FinPl.CombAt P' e :=
  fun u hu => GlobalTheory.DisjComb.mxAt_mono h (he u hu)

theorem combAt_of_isCombAt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    {q : GlobalTheory.FinPl.SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y}
    {e : WO S T →₀ ℂ} {Ξ : Matrix Y Y' k → ℂ} (h : (ofSplit q).IsCombAt ψ FS FT e Ξ) : GlobalTheory.FinPl.CombAt (· = q.v) e :=
  fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D k q u (h.1 u hu)

variable {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle}

theorem eL_combAt (Q : QAt v χ) (j : ℕ) (hj : j ≤ Q.s) : GlobalTheory.FinPl.CombAt (· = Q.q.v) (Q.eL j) := by
  obtain ⟨d, hd⟩ : ∃ d, j + d = Q.s := ⟨Q.s - j, by omega⟩
  exact combAt_of_isCombAt (Q.eL_at j d hd)

theorem eT_combAt (Q : QAt v χ) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : GlobalTheory.FinPl.CombAt (· = Q.q.v) (Q.eT j h) := by
  have hj : j = Q.s := by have := Q.hs; omega
  subst hj
  exact combAt_of_isCombAt Q.eLT_at

theorem dL_combAt (Q : QAt v χ) (j : ℕ) (hj : j ≤ Q.s + 1) (α : Q.Ch j) (γ : Q.Ch (j + 1)) :
    GlobalTheory.FinPl.CombAt (· = Q.q.v) (Q.dL j α γ) := by
  rcases Nat.lt_or_ge j Q.s with h | h
  · obtain ⟨d, hd⟩ : ∃ d, j + 1 + d = Q.s := ⟨Q.s - (j + 1), by omega⟩
    exact combAt_of_isCombAt (Q.dL_mid j d hd α γ)
  · rcases Nat.eq_or_lt_of_le h with h' | h'
    · subst h'
      exact combAt_of_isCombAt (Q.dL_pen α γ)
    · have h'' : j = Q.s + 1 := by omega
      subst h''
      exact combAt_of_isCombAt (Q.dL_top α γ)

theorem pinTup_combAt {t : Tup c} (F : QFam v t) (sc cT : ℕ → ℂ) (j : ℕ) :
    GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) ((F.pinTup sc cT).eQ j) ∧
      (∀ h, GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) ((F.pinTup sc cT).eQT j h)) ∧
      ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) ((F.pinTup sc cT).dQ j α γ) := by
  have hQ : ∀ i, (F.Q i).q.v ∈ (F.pinTup sc cT).Q := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hmono : ∀ i {S T : HSp D} {e : WO S T →₀ ℂ}, GlobalTheory.FinPl.CombAt (· = (F.Q i).q.v) e →
      GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) e :=
    fun i _ _ _ he => combAt_mono (fun p hp => hp ▸ hQ i) he
  have hs : ∀ i, (F.Q i).s + 1 + 1 = D.R.m := fun i => (F.Q i).hs
  refine ⟨?_, fun h => ?_, fun α γ => ?_⟩
  · show GlobalTheory.FinPl.CombAt _ (if j + 1 < D.R.m then aconv (List.ofFn fun i => (F.Q i).eL j) else 0)
    split_ifs with hj
    · refine combAt_aconv _ fun e he => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
      exact hmono i (eL_combAt _ j (by have := hs i; omega))
    · exact combAt_zero
  · show GlobalTheory.FinPl.CombAt _ (aconv (List.ofFn fun i => (F.Q i).eT j h))
    refine combAt_aconv _ fun e he => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    exact hmono i (eT_combAt _ j h)
  · show GlobalTheory.FinPl.CombAt _ (if j < D.R.m then
      (∏ i, (F.Q i).wt j (F.eqv j α i)) • aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i)) else 0)
    split_ifs with hj
    · refine combAt_smul _ (combAt_aconv _ fun e he => ?_)
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
      exact hmono i (dL_combAt _ j (by have := hs i; omega) _ _)
    · exact combAt_zero

end GlobalTheory.QPl.PinComb

open GlobalTheory.QPl.PinComb in

theorem GlobalTheory.QPl.PinComb.famOf_pinTup_combAt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (J : ∀ t, QJ a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (pk W) (lvP W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j,
    GlobalTheory.FinPl.CombAt (· ∈ ((famOf a J row col hCh t).pinTup sc cT).Q) (((famOf a J row col hCh t).pinTup sc cT).eQ j) ∧ (∀ h, GlobalTheory.FinPl.CombAt (· ∈ ((famOf a J row col hCh t).pinTup sc cT).Q) (((famOf a J row col hCh t).pinTup sc cT).eQT j h)) ∧
    ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ ((famOf a J row col hCh t).pinTup sc cT).Q) (((famOf a J row col hCh t).pinTup sc cT).dQ j α γ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a _ _ J _ row col hCh sc cT t j
  exact pinTup_combAt _ sc cT j

end
