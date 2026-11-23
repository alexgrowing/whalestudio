import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FamCol
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}

abbrev chrK (W : RealPack ex) (t : W.P.T) (j : ℕ) : (AE (I.rec7 l Z))ˣ →* Circle := (pk W).toLevCh.mu t (j + 1)

set_option maxHeartbeats 1000000 in

structure QJ (a : GeoAll W u) (t : W.P.T) where
  Ch₀ : ℕ → Type
  A : TwDat I l Z u (W.P.I.tup t) Ch₀
  r : ℕ
  pl : Fin r → Pl (I.rec7 l Z).host.E
  mem : ∀ i, pl i ∈ (pk W).Q t
  E : ∀ i, QExt (a.Q (pl i) ⟨t, mem i⟩) (chrK W t)
  P : Fin r → BadPr I (W.P.I.tup t)
  hψ : ∀ i, Continuous (a.Q (pl i) ⟨t, mem i⟩).ψk
  sg : Fin r → ℂ
  π : ∀ i j, Ch₀ j → (E i).Ch j
  ι : ∀ j, (∀ i, (E i).Ch j) → Ch₀ j

variable {a : GeoAll W u} {t : W.P.T} (J : QJ a t)

abbrev QJ.G (i : Fin J.r) := a.Q (J.pl i) ⟨t, J.mem i⟩

abbrev QJ.Ch (j : ℕ) : Type := ∀ i, (J.E i).Ch j

def QJ.wt (j : ℕ) (α : J.Ch j) : ℂ := ∏ i, (J.E i).wt j (α i)

def QJ.dQ (s : ∀ j, J.Ch j → ℂ) (j : ℕ) (α : J.Ch j) (γ : J.Ch (j + 1)) :
    WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ :=
  (s j α * (s (j + 1) γ)⁻¹) • (J.wt j α • aconv (List.ofFn fun i => (J.E i).dL j (α i) (γ i)))

structure QJ.Reads : Prop where
  is : J.A.Is
  inj : Function.Injective J.pl
  surj : ∀ PP ∈ (pk W).Q t, ∃ i, J.pl i = PP
  chr : ∀ j, j < B.R.m → J.A.chr (j + 1) = chrK W t j
  res : ∀ i, (J.G i).Res (J.E i).δ ((pk W).xiR t (J.pl i))
  eq : ∀ i, (J.P i).1 = J.pl i
  sg : ∀ i, J.sg i = 1 ∨ J.sg i = -1
  tw : ∀ i, GlobalTheory.TwBridge.AtTwist (R := B.R) (k := (J.G i).k) I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i)
    ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (J.G i).s ((J.E i).tw (J.hψ i) (J.sg i))
  M : ∀ i, (J.E i).M = (I.cst (W.P.I.tup t)).M
  rep : ∀ i j d (h : j + d = (J.G i).s) (hj : j < B.R.m) β,
    GlobalTheory.TwBridge.IsGL (X := B.fields) (R := B.R) (k := (J.G i).k) ((J.G i).q.pr.comp (incA (I.rec7 l Z)))
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get hj) (J.P i)) ((J.E i).rep j d h (J.π i j β))

  cos : ∀ i β (e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → (J.E i).cos (J.π i ((J.G i).s + 1) β) =
      Submodule.Quotient.mk fun r => (ofSplit (J.G i).q).pr (Formalism.L2.Col.repY (J.A.p0 ((J.G i).s + 1) β).1.2 (e r))

  std : ∀ j, j + 1 < B.R.m → ∀ β, J.A.kb j β = TC.kStd X u (B.R.N j)

  pen : ∀ j (hj : j + 1 = B.R.m) β, ∃ k₀ h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j),
    k₀ ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)) k₀ = (TC.kStd X u (B.R.N j)).1 ∧ J.A.kA j β = k₀ * h ∧
    h ∈ GlobalTheory.FinPl.grpAt _ (fun p => ∃ i, (J.G i).q.v = p) ∧
    ∀ i (e : (J.G i).s + 1 = j), ∃ g ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J,
      (mt _ (e ▸ h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X ((J.G i).s + 1)))).map (J.G i).q.pr =
        ((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁ * ((J.G i).FX ((J.G i).s + 1) le_rfl).γ
  last : Nonempty (Unique (J.Ch₀ B.R.m))
  sec : ∀ j, j ≤ B.R.m → ∀ y i, J.π i j (J.ι j y) = y i

  cosG : ∀ (n : Fin a.n) y (e : XIx (Fin B.R.k) (Fin B.R.t) ((a.G n).s + 1) ≃ Fin (B.R.N ((a.G n).s + 1))),
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ r,
      (ofSplit (a.G n).q).pr (Formalism.L2.Col.repY (J.A.p0 ((a.G n).s + 1) (J.ι _ y)).1.2 (e r)) - (a.G n).S.y0 (Fin B.R.t) r ∈ 𝒪[(a.G n).k]
  live : J.A.Live J.ι

def QJ.Vol (V : ℕ → ℂ) : Prop :=
  ∀ j, j < B.R.m → ∀ α, (GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) : ℂ) * J.wt j α = V j

def QJ.Dat (C : ℕ → ℂ) (s : ∀ j, J.Ch j → ℂ) (ζ : ∀ j, J.Ch j → J.Ch (j + 1) → ℂ) (ρ : ℕ → ℂ) : Prop :=
  (∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1) ∧ (∀ α, s 0 α = 1) ∧ (∀ j, ∃ n : ℕ, 0 < n ∧ ρ j ^ n = 1) ∧
    ∀ j (hj : j + 1 ≤ B.R.m) α γ,
      IsRatDatum (pk W).ψ _ _ J.A.e (fun z => C j * J.wt j α * ζ j α γ * J.A.xi j hj (J.ι j α) (J.ι (j + 1) γ) z) (a.g.vac j)
        (comb (pk W).ψ _ _ (J.dQ s j α γ) (comb (pk W).ψ _ _ (a.v.dG j) (comb (pk W).ψ _ _ (a.v.dT j) (a.g.vac j)))) ∧
      ζ j α γ * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ) * (J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ)⁻¹ = ρ j

def QJ.VolT (VT : ℂ) : Prop :=
  ∃ UT : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X'),
    (∀ h, h ∈ UT ↔ a.g.bT⁻¹ * h * a.g.bT ∈ levS _ (pk W).βX (datXP (pk W) (lvP W) t)) ∧
    ∀ β, (GlobalTheory.SeeSaw.volLev a.g.volT UT : ℂ) * J.wt B.R.m β = VT

end GlobalTheory.Fam

end
