import Mathlib
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
import Formalism.LocalToGlobal.Divisibility.Numbers
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

noncomputable section

namespace GlobalTheory.ColRows

open Module NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds
open Formalism.LatticeIndexTer (ph)

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def IsFrames (Df : DefSide Bs) (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ) : Prop :=
  ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df.HV Bs.μ0).map v.embedding

def RowsBody (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums Bs.J Pl) : Prop :=
  ∃ (ch : ColChain Dc u) (T : ChainTie ch Q), T.First (f0.comp (LinearMap.funLeft K K (Fin.cast ch.c0.symm))) ∧
    ∃ (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ)
      (_ : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df.HV Bs.μ0).map v.embedding)
      (hn : HtNums R (InfinitePlace K))
      (_ : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
        (Pi.basisFun K (Fin (Df.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn)
      (cb : CBData ch.X ch.Kj),
      ∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v

def FamFramed (F : GFam K) (h : F.Ok) : Prop :=
  ∃ (n : ℕ) (e : (Fin n → K) ≃ₗ[K] F.Forms) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) ∧
    ∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x ^ 2 : ℝ) : ℂ) = famIpAt F h v (e x) (e x)

def DatFramed (S : GSD K) (h : S.Ok) : Prop :=
  ∃ (n : ℕ) (e : (Fin n → K) ≃ₗ[K] S.EqFun) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) ∧
    ∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x ^ 2 : ℝ) : ℂ) = S.ipAt h v (e x) (e x)

def FactorBounds (Q : KerChain K) {J : Type} [Fintype J] (no : J → ℕ) (t : J → InfinitePlace K → ℝ) : Prop :=
  (∀ i < Q.n, ∀ v, StepBound_sq Q i v (∑ l ∈ Finset.univ.filter (fun l => no l = i), t l v)) ∧
    ∀ v, CplBound_sq Q v (∑ l ∈ Finset.univ.filter (fun l => Q.n ≤ no l), t l v)

end Generic

section Numbers

variable {J Pl : Type} [Fintype J] [Fintype Pl] [DecidableEq Pl] (R : RecNums J Pl)

def KerSide (Emb : Type) [Fintype Emb] (C : ℝ) (P : (J → Emb → ℝ) → Prop) : Prop :=
  ∃ (g0 : J → ℝ) (MainNotions : J → Emb → ℝ) (logOm : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' : J → ℝ) (vv logg : ℝ),
    (∀ τ, (∑ s, logOm τ s) / (Fintype.card Emb : ℝ) = R.logOm) ∧
    (∀ j s, MainNotions j s ≤ C * R.f * R.m ^ 2 * R.Nn ^ 2 * (logg + R.logT) + C * R.f * R.Nn ^ 2 * logg) ∧
    (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ C * R.L ∧
    (∀ j, logh j ≤ C * R.f * R.Nn ^ 2 * (R.L + R.logT + logg)) ∧
    (∀ j, logh' j ≤ C * R.f * R.Nn ^ 2 * (R.L + R.logT + logg)) ∧
    (∀ j, 0 ≤ g0 j ∧ g0 j ≤ R.Nn ^ 2) ∧
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * vv) ≤ C * R.La) ∧
    (∀ j τ, Real.log (2 * (∑ i, R.ν j τ i) + 2) ≤ C * R.La) ∧ logg ≤ C * R.L ∧
    P (Formalism.DimensionVariation.liftedMapLogSize R.ν g0 MainNotions logOm logth0 logh logh' vv)

def LastSide (CT A : ℝ) : Prop :=
  ∃ bT nτ lam1 D0 D1 logc logxi : Pl → ℝ,
    A ≤ -(∑ τ, nτ τ * R.logT) + (∑ τ, (2 * logc τ + logxi τ)) ∧
    (∀ τ, logc τ ≤ (R.Nn - 1) * D1 τ * Real.log (2 * R.a)) ∧
    (∀ τ, logxi τ ≤ R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)) ∧
    (∀ τ, nτ τ = lam1 τ - D0 τ) ∧ (∀ τ ∈ R.TT, lam1 τ = R.aT τ - (R.Nn - R.k) / 2) ∧
    (∀ τ, τ ∉ R.TT → R.S - (R.Nn - 1) / 2 ≤ lam1 τ) ∧
    (∀ τ, D0 τ ≤ R.S + R.m * R.η + (if τ ∈ R.TT then bT τ else 0)) ∧
    (∀ τ, D1 τ ≤ 3 * D0 τ + R.S + R.η) ∧ (∀ τ ∈ R.TT, bT τ ≤ 2 * R.b') ∧
    0 ≤ R.logT ∧ R.logT ≤ CT * R.m * R.L

end Numbers

structure Reads (N : NumDatum) {J : Type} [Fintype J] (eJ : J ≃ Fin N.R.m) (δ : Code N) (T : ℕ) (R : RecNums J (RPl N.R)) : Prop where
  tops : ∀ z, z ∈ R.TT ↔ IsTopPl N z
  aT : ∀ t ∈ N.TT, R.aT (false, t) = ((N.aT t : ℚ) : ℝ)
  logT : R.logT = Real.log (T : ℝ)
  phNu : ∀ j z, ∑ i, ph (R.ν j z i) = ∑ i ∈ Finset.range (N.R.N (eJ j).1), ph ((N.nu δ ((eJ j).1 + 1) z i : ℚ) : ℝ)
  sumNu : ∀ j z, ∑ i, R.ν j z i = ((N.nuAbs δ ((eJ j).1 + 1) z : ℚ) : ℝ)
  nums : R.L = N.sc.L ∧ R.a = N.sc.a ∧ R.b = N.sc.b ∧ R.La = N.La ∧ R.m = N.R.m ∧ R.f = N.R.f ∧ R.k = N.R.k ∧ R.Nn = N.Nm ∧
    R.S = N.Sc ∧ R.η = N.eta ∧ R.b' = N.sc.b' ∧ R.logOm = N.logOm

def lastLog {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) : ℝ :=
  -((∑ τ, Br.nBr (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℝ) * Real.log (Pr.T u : ℝ) +
    Real.log (∏ τ, ((Br.cBr (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℝ) ^ 2 *
      Br.kapBr ℝ (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ))

end GlobalTheory.ColRows
