import Formalism.LocalToGlobal.Columns.TiedRec
import Formalism.LocalToGlobal.Columns.Record
import Formalism.LocalToGlobal.Columns.RecLevelStep
import Formalism.LocalToGlobal.Columns.RowFormsLemmas

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure ColBase where
  R : Ranks
  host : Host R
  sp : Spaces R host.F host.E
  what₂ : ColRows R
  eTau : what₂.Tau ≃ (R.Psi)
  [wordFin : Fintype what₂.Word]
  u₀ : what₂.Word
  hcW : what₂.Word → what₂.Tau → HCParam R
  [nfLL : NumberField what₂.LL]
  [starLL : StarRing what₂.LL]
  embE : host.E →+* what₂.LL

  cond : ℕ

  piG : Fin 2 → 𝓞 host.E

  T : what₂.Word → ℕ

  piT : what₂.Word → 𝓞 host.E

  tops : Finset what₂.Tau

attribute [instance] ColBase.wordFin ColBase.nfLL ColBase.starLL

namespace ColBase

variable (B : ColBase)

@[reducible] def X : Fields where
  F := B.host.F
  E := B.host.E
  K := B.what₂.LL
  starE := B.host.cmStar
  Tau := B.what₂.Tau
  deTau := Classical.decEq _
  emb := fun τ => B.embE.comp (B.host.sigmaOf (B.eTau τ : B.R.GG) : B.host.E →+* B.host.E)

@[reducible] def Pr : Primes B.X where
  cond := B.cond
  g := B.host.g
  piG := B.piG
  Word := B.what₂.Word
  deWord := Classical.decEq _
  T := B.T
  piT := B.piT

@[reducible] def W : Wts B.X B.what₂.Word B.R where
  row := fun τ => RowPar.of (B.hcW B.u₀ τ)
  hc := B.hcW
  tops := B.tops

@[reducible] def σ₀ : B.X.K →+* ℂ := B.what₂.embLL

end ColBase

structure ColDat extends ColBase where

  Ch : Chars toColBase.X toColBase.Pr R.m

  lev : ∀ j, LevFam toColBase.X.E toColBase.X.K (R.N j) toColBase.Pr.vGs := colLevS Ch

  lev0 : lev 0 = colLev Ch 0 := by
    exact colLevS_of_lt _ (Nat.lt_of_lt_of_le (by norm_num) (Ranks.two_le_m _))

  levP : LevFam toColBase.X.E toColBase.X.K (R.N R.m - 1) toColBase.Pr.vGs := (rowTyG Ch (rPsharp Ch)).inv

  Ps : CharT toColBase.X toColBase.Pr

  num : AtTNum

  plEq : what₂.places.Pl ≃ HeightOneSpectrum (𝓞 what₂.LL)
  hX : toColBase.X.Ok
  hPr : toColBase.Pr.Ok
  hPs : Ps.Ok

  star_cx : ∀ x : what₂.LL, what₂.embLL (star x) = starRingEnd ℂ (what₂.embLL x)

structure ColArgs (d : ColDat) where

  G : ChainGlob (Pr := d.Pr) d.W d.σ₀

  A : ∀ u : d.what₂.Word, ChainArg (Pr := d.Pr) d.W d.lev G u

  th : ∀ u : d.what₂.Word, ThArg (Pr := d.Pr) d.W d.lev u
  free : ∀ u : d.what₂.Word, (stepGSD (Pr := d.Pr) d.W d.lev u 0).Free
  rowOk : (rowGSD (Pr := d.Pr) d.W d.levP).Ok
  piT_off : ∀ (u : d.what₂.Word) (w : d.Pr.vGs), d.Pr.piT u ∉ w.1.asIdeal
  levExt : LevExt (Pr := d.Pr) d.lev (Finset.Subset.refl _) d.levP

namespace ColDat

variable (d : ColDat) (a : ColArgs d)

theorem f_eq : d.X.f = d.R.f := d.what₂.card_Tau

@[reducible] def chain (u : d.what₂.Word) : ColumnChain d.R d.what₂.Tau (d.hcW u) :=
  recChain (Pr := d.Pr) (W := d.W) (Λ := d.lev) d.hX d.σ₀ a.G u (a.A u)

@[reducible] def atT (u : d.what₂.Word) : ColumnsAtT d.R (d.chain a u) :=
  recAtT (Pr := d.Pr) (W := d.W) (Λ := d.lev) d.hX d.hPr d.f_eq d.σ₀ d.star_cx u a.G (a.A u) d.Ps d.hPs (a.free u) d.num

@[reducible] def per (u : d.what₂.Word) : PeriodMap d.R (d.chain a u) :=
  recPer (Pr := d.Pr) (W := d.W) (Λ := d.lev) (Finset.Subset.refl _) (ΛM := d.levP) d.hX d.σ₀ d.star_cx u a.G (a.A u) a.rowOk

@[reducible] def forms (u : d.what₂.Word) :
    MemberForms d.what₂.LL d.what₂.embLL d.what₂.places d.what₂.Tau (d.hcW u) (d.chain a u) (d.atT a u) (d.per a u) :=
  recFormsX (Pr := d.Pr) (W := d.W) (Λ := d.lev) (Finset.Subset.refl _) (ΛM := d.levP) d.hX d.hPr d.f_eq d.σ₀ d.star_cx u a.G (a.A u) d.Ps d.hPs
    (a.free u) d.num d.what₂.places d.plEq a.rowOk (a.piT_off u) a.levExt (a.th u)

def crd (i : ℕ) (hi : i ≤ d.R.m) : (d.sp.X i).V ≃ₗ[d.host.E] (Fin (d.R.N i) → d.host.E) :=
  (d.sp.X i).frame.equivFun.trans (LinearEquiv.funCongrLeft d.host.E d.host.E (finCongr (d.sp.X_rank i hi)).symm)

def repr (u : d.what₂.Word) (i : ℕ) (c : StCl (Pr := d.Pr) d.W d.lev u i) : DecoSet d.X.E (d.R.N i) (d.Pr.vT u) d.Pr.vGs :=
  (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.rep c

open Classical in

def clsLat (u : d.what₂.Word) (i : ℕ) (c : StCl (Pr := d.Pr) d.W d.lev u i) : Submodule (𝓞 d.host.E) (d.sp.X i).V :=
  if hi : i ≤ d.R.m then
    (d.repr u i c).1.L.map (((d.crd i hi).symm : (Fin (d.R.N i) → d.host.E) →ₗ[d.host.E] (d.sp.X i).V).restrictScalars (𝓞 d.host.E))
  else (d.sp.X i).L0

@[reducible] def colRec : ColRec where
  R := d.R
  host := d.host
  sp := d.sp
  what₂ := d.what₂
  eTau := d.eTau
  u₀ := d.u₀
  hcW := d.hcW
  mem := fun u => ⟨d.chain a u, d.atT a u, d.per a u⟩
  embE := d.embE
  cOf := fun u => (d.piT d.u₀ : d.host.E) / (d.piT u : d.host.E)
  clsLat := fun u i c => d.clsLat u i c
  fm := fun u => d.forms a u

end ColDat

end Formalism.L2.Col
