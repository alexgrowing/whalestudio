import Formalism.SharpRestriction.GlobalSchurBounds.FrameCodeOfAdditive

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss

open Formalism.BasicNotions Formalism.MainNotions Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

def StPts : Prop :=
  ∀ (eps : ℝ) (Fm : FamP eps) (Cb : ℝ), ChosenTT Fm → ChosenBad Fm Cb → LinkG Fm → Lnk.StatementsAtPointsLargeScales Fm

def StCore : Prop :=
  ∀ (eps : ℝ) (Fm : FamP eps) (Cb : ℝ), ChosenTT Fm → ChosenBad Fm Cb → LinkG Fm → Fm.CoverAll → Lnk.SmallOrderPrimes Fm

def StLoss : Prop :=
  ∀ (eps : ℝ) (Fm : FamP eps) (Cb : ℝ), ChosenTT Fm → ChosenBad Fm Cb → LinkG Fm → Fm.CoverAll → Lnk.LossF Fm 0

def SlopeLoss : Prop :=
  ∀ (eps : ℝ) (Fm : FamP eps) (Cb eL : ℝ), 0 ≤ eL → ChosenTT Fm → ChosenBad Fm Cb → LinkG Fm → Fm.CoverAll →
    LocalQuadraticParts.SlopeLossFamily Fm eL

section AtRecord

variable {D : D7} {L : SizeData₂ D}

def bndP (L : SizeData₂ D) : ℕ :=
  max ⌊L.sc.a + L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))⌋₊ ⌊L.sc.X'' D.R.n⌋₊ + 1

open Classical in

def PsAt (L : SizeData₂ D) : Finset ℕ := (Finset.range (bndP L)).filter (fun p => p.Prime ∧ InertK D p)

open Classical in

def sAt (L : SizeData₂ D) (K : G.Consts) : Finset ℕ := (Finset.range ⌈L.sc.X'⌉₊).filter (fun p => G.Cand D L K p)

def TTv (D : D7) : Finset ℕ := D.host.TT.image Formalism.HC.Frame.A.val

def badAt (X : G.Inst D L) (p n : ℕ) : Prop := ¬ G.Good X p (X.bs (G.stepP D p) (D.R.ofNat n))

open Classical in

def clAt (X : G.Inst D L) (K : G.Consts) (p : ℕ) : PClass :=
  if p ∉ L.drop then PClass.served
  else if L.sc.X'' D.R.n < (p : ℝ) then PClass.high
  else if G.Cand D L K p ∧ L.sc.x ^ (-L.sc.eps) < G.Sig X K (G.aL L) (G.bL L) p then PClass.second
  else PClass.first

open Classical in

def gainQ (X : G.Inst D L) (K : G.Consts) (j p : ℕ) : ℝ :=
  if p ∈ L.drop then 0 else G.gainP X K (G.aL L) (G.bL L) p j

def ldAt (X : G.Inst D L) (K : G.Consts) (C bo : ℝ) : LD ℕ ℕ ℕ where
  W := PsAt L
  below := id
  l := fun p => Real.log p
  cl := clAt X K
  TTp := fun p => (G.TTP X K (G.aL L) (G.bL L) p).image Formalism.HC.Frame.A.val
  Iex := fun _ n p => (Finset.range (Nat.log p (G.aL L (D.R.ofNat n)).toNat + 2)).filter Odd
  at_ := fun n => (G.aL L (D.R.ofNat n) : ℝ)
  wz := fun j n p e => G.fill X (G.bL L) j (G.partner D p (D.R.ofNat n) e)
  Id := fun _ n => Finset.Icc 1 (Nat.log D.host.d (G.aL L (D.R.ofNat n)).toNat + 1)
  wd := fun j n i => LocalQuadraticParts.wAt D j (GlobalTheoryTheory.rho D (D.R.tau1 (D.R.ofNat n)) (ZetaZeroFreeRegion.gD D i))
  gainW := gainQ X K
  tauW := G.tauP X K (G.aL L) (G.bL L)
  gain := gainQ X K
  tau := G.tauP X K (G.aL L) (G.bL L)
  lo := loG L C bo
  fl := flG L C
  L₁ := fun p => (leastPowerExponent L p : ℝ)

structure ParTie (P : Par) (L : SizeData₂ D) (K : G.Consts) (C bo Cr : ℝ) : Prop where
  x : P.x = L.sc.x
  ε : P.ε = L.sc.eps
  e₂ : P.e₂ = D.R.e
  nA : P.nA = D.R.n
  k : P.k = D.R.k
  N : P.N = (D.R.N D.R.m : ℝ)
  t : P.t = D.R.t
  p₀ : P.p₀ = ⌈L.sc.p0 D.R.k⌉₊
  La : P.La = L.LaG
  rG : P.rG = (Formalism.MainNotions.rG L.sc.eps : ℝ)
  Sc : P.Sc = L.Sc
  η : P.η = L.etaSz
  ρ : P.ρ = G.rhoB D K L.sc
  th : P.th = 1 / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))
  K₀ : P.K₀ = (D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A)
  d : P.d = D.host.d
  C : P.C = max C 0
  Y : P.Y = L.sc.X' * (1 + Cr * G.rhoB D K L.sc)
  bo : P.bo = bo

structure PtH (X : G.Inst D L) (K : G.Consts) (Cr : ℝ) : Prop where
  fills : ∀ w, G.ParametersFill X K w
  supp_sat : ∀ w, ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n → w ∈ L.supp
  drop_iff : ∀ p : ℕ, p.Prime → (p ∈ L.drop ↔ NoGain X K Cr p ∧ ∀ u, p ≠ (D.mem u).A.T)
  Knn : K.Nonneg
  kapI : G.KapIDef X K
  Cr1 : 1 ≤ Cr
  numN : Lnk.NumN_at L

end AtRecord

section Family

variable {eps : ℝ} (Fm : FamP eps) (x : ℝ) (i0 : Fm.Ix x)

def par (C bo Cb Cord : ℝ) : Par where
  x := (Fm.L x i0).sc.x
  ε := (Fm.L x i0).sc.eps
  e₂ := (Fm.D x i0).R.e
  nA := (Fm.D x i0).R.n
  k := (Fm.D x i0).R.k
  N := ((Fm.D x i0).R.N (Fm.D x i0).R.m : ℝ)
  t := (Fm.D x i0).R.t
  p₀ := ⌈(Fm.L x i0).sc.p0 (Fm.D x i0).R.k⌉₊
  La := (Fm.L x i0).LaG
  rG := (Formalism.MainNotions.rG (Fm.L x i0).sc.eps : ℝ)
  Sc := (Fm.L x i0).Sc
  η := (Fm.L x i0).etaSz
  ρ := G.rhoB (Fm.D x i0) Fm.GK (Fm.L x i0).sc
  th := 1 / (((Fm.D x i0).R.k : ℝ) * (Fm.L x i0).sc.x ^ (Scale.A / 2))
  K₀ := ((Fm.D x i0).R.k : ℝ) ^ 2 * (Fm.L x i0).sc.x ^ (3 * Scale.A)
  d := (Fm.D x i0).host.d
  C := max C 0
  β := max Cb 0 * (Fm.L x i0).sc.x ^ (-2 : ℝ)
  Cord := Cord
  Y := (Fm.L x i0).sc.X' * (1 + Fm.Cr * G.rhoB (Fm.D x i0) Fm.GK (Fm.L x i0).sc)
  s₀ := ((Fm.D x i0).R.m : ℝ) * ((Fm.D x i0).host.TT.card : ℝ) * (Fm.L x i0).sc.x ^ (-12 : ℝ)
  bo := bo

variable {Fm x i0}

def aO (o : Lnk.Wt Fm x i0) (t : G.HH (Fm.D x i0)) : ℤ := Lnk.avOf o t.val

def bO (o : Lnk.Wt Fm x i0) (t : G.HH (Fm.D x i0)) : ℤ := Lnk.bvOf o t.val

def SigO (p : ℕ) (o : Lnk.Wt Fm x i0) : ℝ := G.Sig (Fm.Gx x i0) Fm.GK (aO o) (bO o) p

end Family

end Formalism.L2.GlobalTheoryTheory.Loss

end
