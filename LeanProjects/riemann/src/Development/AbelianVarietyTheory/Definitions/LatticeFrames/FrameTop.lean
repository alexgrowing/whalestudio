import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {u : D.what₂.Word}

structure XPart (D : D7) (u : D.what₂.Word) where
  c : GlobalTheory.ChainOnto.Com D
  top : StAt D.sp.X'
  x : ∀ j, DefSp (D.sp.X j)
  k : ∀ j, KerDat (D.sp.X j) (D.sp.X (j + 1))
  Lz : HSp D
  oT : ∀ n, n = D.R.m → OrthDec (D.sp.X n) D.sp.X' Lz
  Ram : ∀ j, Submodule ℂ (Col D u j)
  rd : ∀ j, Col D u j → (D.mem u).C.Y j → GA D (D.sp.X j) → ℂ
  eT : (D.mem u).P.Mt →ₗ[ℂ] top.st.CC c

@[reducible] def XPart.geo (a : XPart D u) (bot : StAt (D.sp.Y 0)) (mid : ℕ → GlobalTheory.ChainOnto.PiLocalization₂ D) : Geo D := ⟨a.c, bot, mid, a.top⟩

set_option maxHeartbeats 1000000 in

structure YPart (a : XPart D u) where
  bot : StAt (D.sp.Y 0)
  mid : ℕ → GlobalTheory.ChainOnto.PiLocalization₂ D
  p : ∀ j, GlobalTheory.ChainOnto.Step a.c ((a.geo bot mid).st j) ((a.geo bot mid).st (j + 1))
  pT : ∀ j, j + 2 * 0 + 2 = D.R.m → GlobalTheory.ChainOnto.Step a.c ((a.geo bot mid).st (j + 1)) a.top.st
  t : ∀ j, GA D ((a.geo bot mid).st j).V
  bes : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt ((a.geo bot mid).st j).V (D.sp.X j) ρ
  jac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → JacAt ((a.geo bot mid).st (j + 1)).V (D.sp.X (j + 1)) ρ
  sBF : ∀ j ρ h, StepBF a.c.ψ ((bes j ρ h).lev (a.x j).vol) ((jac j ρ h).lev (a.x (j + 1)).vol)
  sFB : ∀ j σ h, StepFB a.c.ψ ((jac j (σ + 1) h).lev (a.x (j + 1)).vol)
    ((bes (j + 1 + 1) σ (idx_step h)).lev (a.x (j + 1 + 1)).vol)
  lnk : ∀ j σ h, Link ((bes j (σ + 1) h).lev (a.x j).vol) (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ
  vL : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), VolM D (bes (j + 1 + 1) σ (idx_step h)).L.rank (D.sp.X (j + 1)).rank

@[reducible] def XPart.dat (a : XPart D u) (b : YPart a) : Dat D u where
  toGeo := a.geo b.bot b.mid
  p := b.p
  pT := b.pT
  t := b.t
  x := a.x
  k := a.k
  bes := b.bes
  jac := b.jac
  sBF := b.sBF
  sFB := b.sFB
  lnk := b.lnk
  vL := b.vL
  Lz := a.Lz
  oT := a.oT
  Ram := a.Ram
  S := fun _ => 0
  rd := a.rd
  eT := a.eT

@[reducible] def Dat.rescale (d : Dat D u) (s : ℕ → ℂ) : Dat D u :=
  { d with k := fun j => ⟨(d.k j).om, (d.k j).vac, s j • (d.k j).c⟩ }

section Off

open GlobalTheory.FinPl

structure OffX (a : XPart D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ι : Type) where
  p : ι → SplitPt D k
  I : List ι
  q : Unif k
  χ : ι → AddChar k Circle
  hχ : ∀ i, HasConductor (χ i) 1
  β : ∀ j i, Frame (p i) (D.sp.X j) (Fin (D.sp.X j).rank)
  Q : ∀ j, ι → Pair k (Fin (D.sp.X j).rank)
  cT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ
  cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ
  ζ₀ : Fin a.Lz.rank → D.host.E
  γ : ∀ i, Frame (p i) D.sp.X' (Fin D.sp.X'.rank)
  γ₀ : ∀ n, n = D.R.m → ∀ i, Frame (p i) (D.sp.X n) (Fin D.sp.X'.rank ⊕ Fin 1)

variable {a : XPart D u} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

structure OffY (o : OffX a k ι) (b : YPart a) where
  β₀ : ∀ j ρ h i, Frame (o.p i) (b.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)
  L : ∀ j, Lat ((a.dat b).st j).V
  M : ∀ j ρ h, Lat (b.bes j ρ h).V₀
  τ : ∀ j (h : j + 2 * 0 + 2 = D.R.m), Matrix (Fin (b.bes j 0 h).L.rank) (Fin a.Lz.rank) D.host.E

@[reducible] def OffX.off (o : OffX a k ι) {b : YPart a} (y : OffY o b) : OffDat (a.dat b) k ι :=
  ⟨o.p, o.I, o.q, o.χ, o.hχ, o.β, o.Q, y.β₀, y.L, y.M, o.cT, o.cG, y.τ, o.ζ₀, o.γ, o.γ₀⟩

def OffX.atT (o : OffX a k ι) (v : Pl D) : Prop := ∃ i, v = (o.p i).v

structure PinOffX (o : OffX a k ι) : Prop where
  nodup : o.I.Nodup
  all : ∀ i, i ∈ o.I
  inj : Function.Injective fun i => (o.p i).v
  off : ∀ i, (o.p i).v ∉ a.c.S
  overT : ∀ v : Pl D, o.atT v ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal
  char : ∀ i, (o.p i).IsChar a.c.ψ (o.χ i) ∧ (o.p i).UnitAA
  latT : ∀ j, j ≤ D.R.m → ∀ i, (o.β j i).IsLat (a.x j).L (o.Q j i).lat
  parts : ∀ j, j < D.R.m → CombAt o.atT (o.cT j) ∧ CombAt (· ∈ a.c.S) (o.cG j) ∧
    ∀ f, comb a.c.ψ _ _ (a.k j).c f = comb a.c.ψ _ _ (o.cG j) (comb a.c.ψ _ _ (o.cT j) f)
  rep : ∀ j, j < D.R.m → ∀ f, Vac a.c.ψ _ _ (a.x j).L (a.x (j + 1)).L o.atT f →
    OverAll a.c.ψ (o.β j) (o.β (j + 1)) (a.x j).L (a.x (j + 1)).L (fun i => phiOne (o.Q j i) (o.Q (j + 1) i)) o.I f
      (comb a.c.ψ _ _ (o.cT j) f)
  om : ∀ j, j < D.R.m → IsWeilDatumO a.c.ψ _ _ (a.c.μ (j + 1)) (a.c.μ (j + 1)) (a.k j).om
  line : IsLineVec a.Lz o.ζ₀
  norm : star o.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ o.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E)
  split : ∀ n (h : n = D.R.m) v, ¬ o.atT v → ∃ LZ : Lat a.Lz, IsSelfDualC _ LZ ∧ o.ζ₀ ∈ LZ ∧
    OrthAt (a.oT n h) (a.x n).L a.top.Λ LZ v
  topT : ∀ n (h : n = D.R.m) i, IsSumFrame (a.oT n h) o.ζ₀ (o.γ i) (o.γ₀ n h i) ∧
    ∃ (Λ : Submodule 𝒪[k] (Fin D.sp.X'.rank → k)) (s : 𝓀[k]ˣ), (o.γ i).IsLat a.top.Λ Λ ∧
      (∀ y, y ∈ (o.Q n i).ker ↔ ((o.γ₀ n h i).b' * (o.β n i).b) *ᵥ y ∈ lastKer Λ) ∧
      (o.Q n i).HasVal (((o.β n i).b' * (o.γ₀ n h i).b) *ᵥ (o.q.inv • avec k (Fin D.sp.X'.rank) 1 1)) s

end Off

section AtLevel

open GlobalTheory.LocMod

structure GX (a : XPart D u) (ζ₀ : Fin a.Lz.rank → D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [mea : MeasurableSpace k]
  [bor : BorelSpace k]
  ν : Measure k
  unitVol : IsUnitVol ν
  q : GlobalTheory.FinPl.SplitPt D k
  idem : Formalism.L2.NTheta.IsIdemAt q.e PP
  unit : q.UnitAA
  s : ℕ
  hs : s + 1 + 1 = D.R.m
  S : SymData k s D.R.k
  char : (ofSplit q).IsChar a.c.ψ S.ψ
  mu : ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (a.c.chS j)⁻¹ (S.μ j)
  FX : ∀ j, j ≤ s + 1 → Frame k (D.sp.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)
  FT : Frame k D.sp.X'.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))
  FM : Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)
  z₀ : Fin a.Lz.rank → k
  z₀_unit : ∃ c : k, valuation k c = 1 ∧ z₀ = c • fun i => (ofSplit q).pr (ζ₀ i)
  last : FM.β = fromCols ((a.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((a.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r)
  latX : ∀ j hj (y : XIx (Fin D.R.k) (Fin D.R.t) j → k), (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec (((FX j hj).β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X j) (a.x j).L (· = q.v)
  latM : ∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔
    (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (a.x (s + 1 + 1)).L (· = q.v)
  frameTop : ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin D.sp.X'.rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) D.sp.X' 1 a.top.β (FT.β.submatrix id e.symm)
  cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ
  cg_mid : ∀ j c (H : j + 1 + c = s), (ofSplit q).IsCombAt a.c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j)
    ((S.T (Fin D.R.t)).entry S.ψ ν j c H 1 1)
  cg_pen : (ofSplit q).IsCombAt a.c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s)
    fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))
  cg_top : (ofSplit q).IsCombAt a.c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1))
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))

attribute [instance] GX.fld GX.val GX.top GX.loc GX.mea GX.bor

variable {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E}

def GX.Red {PP : Formalism.L2.DIV.Pl D.host.E} (G : GX a ζ₀ PP) (x : G.S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) : Prop :=
  ∀ (i j : Fin D.R.k ⊕ Fin (G.s + 1)) (a' b' : Fin D.R.r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ i →
    b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ j → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = g.val a' b' →
      valuation G.k ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val i j - (ofSplit G.q).pr (z : D.host.E)) < 1

structure PinGX (G : ∀ PP : a.c.Pg, GX a ζ₀ PP.1) (cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) : Prop where
  grp : ∀ g : ∀ PP : a.c.Pg, GL (Fin D.R.r) (Formalism.L2.DIV.kP PP.1), g ∈ a.c.P.H ↔ ∀ PP, ∃ x, (G PP).Red x (g PP)
  chr : ∀ (g : a.c.P.H) (x : ∀ PP, (G PP).S.P.J), (∀ PP, (G PP).Red (x PP) (g.1 PP)) →
    a.c.P.chi g = ∏ PP, (G PP).S.P.lam (x PP)
  supp : ∀ j, ∀ w ∈ (cG j).support, GlobalTheory.FinPl.MxAt (· ∈ a.c.S) w
  prod : ∀ j, j < D.R.m → ∀ f, IsThetaFunO a.c.ψ _ _ f → comb a.c.ψ _ _ (cG j) f =
    a.c.Pg.attach.toList.foldr (fun PP f' => comb a.c.ψ _ _ ((G PP).cg j) f') f

end AtLevel

section World

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (w : World I l Z) {v : B.Word}
  (a : XPart (I.rec7 l Z) v) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (o : OffX a k ι) (G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1)

structure XPins : Prop where
  com : a.c.Is
  places : GlobalTheory.Core.Mi.IsTypePlaces a.c.Pg
  top : a.top.st.Is a.c B.R.m
  cpt : CoCpt (I.rec7 l Z).sp.X'
  x : ∀ j, j ≤ B.R.m → (a.x j).Is
  k : ∀ j, j < B.R.m → (a.k j).Is a.c.ψ a.c.θ (a.x j) (a.x (j + 1))
  off : PinOffX o
  lev : PinGX G o.cG
  col : ∃ s : ℕ → ℂ, (∀ j, s j ≠ 0) ∧ ∀ b : YPart a, GlobalTheory.AdForm.PinCol w ((a.dat b).rescale s)
  rdT : ∀ (b : YPart a) (y : OffY o b), GlobalTheory.FinPl.RdT (o.off y)
  rd0 : a.rd 0 = (GlobalTheory.Core.Mi.chart0 (w.C.forms v).to0).rd a.c.θ

structure YPins (b : YPart a) (y : OffY o b) : Prop where
  base : (a.dat b).Base
  off : GlobalTheory.FinPl.PinOff (o.off y)
  lev : GlobalTheory.LocMod.PinG (a.dat b) y.τ o.cG
  bot : GlobalTheory.Core.Mi.PinBot w.S (a.dat b)

end World

end GlobalTheory.SeeSaw

end
