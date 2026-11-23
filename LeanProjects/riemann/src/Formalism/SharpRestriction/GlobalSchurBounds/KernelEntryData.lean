import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

noncomputable section

namespace Formalism.MainNotions.KernelEntryData

open Formalism.BasicNotions Formalism.MainNotions.G Finset

section Numbers

variable {n' : ℕ}

def lg (p : ℕ) (x : ℤ) : ℕ := FormalGroupSystem.lgp p x

def rho (p : ℕ) : ℝ := 1 / ((p : ℝ) ^ 2 - 1)

def gam (p : ℕ) : ℝ := (p : ℝ) * rho p

structure IsPart (r0 : ℕ) (nu : Fin n' → ℕ → ℤ) : Prop where
  nonneg : ∀ s i, 0 ≤ nu s i
  anti : ∀ s i, 1 ≤ i → nu s (i + 1) ≤ nu s i
  what₂ : ∀ s i, r0 < i → nu s i = 0

def al (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) (s : Fin n') : ℤ :=
  if s ∈ TT then nu s 1 - nu s 2 else 0

def cap (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) (s : Fin n') : ℤ :=
  if s ∈ TT then nu s 2 else nu s 1

def sz (rb : ℕ) (nu : Fin n' → ℕ → ℤ) (s : Fin n') : ℤ := ∑ i ∈ Icc 1 rb, nu s i

def low (rb : ℕ) (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) (s : Fin n') : ℤ := sz rb nu s - al TT nu s

def OtherPar (s s' : Fin n') : Prop := s'.val % 2 ≠ s.val % 2

instance (s s' : Fin n') : Decidable (OtherPar s s') := inferInstanceAs (Decidable (_ ≠ _))

def dLev (s s' : Fin n') : ℕ := (s'.val + n' - s.val) % n'

def DSet (TT : Finset (Fin n')) (s : Fin n') : Finset ℕ := (TT.filter fun s' => OtherPar s s').image (dLev s)

def gain (p : ℕ) (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) (s : Fin n') (e : ℕ) : ℝ :=
  max ((al TT nu s : ℝ) / (p : ℝ) ^ e - (cap TT nu (posAdd s e) : ℝ)) 0

def de (p r0 r1 rb : ℕ) (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) : ℝ :=
  ∑ s : Fin n', ((r1 : ℝ) * lg p (al TT nu s) + (r0 : ℝ) * (r1 : ℝ) * lg p (low rb TT nu s)) +
    ∑ s ∈ TT, ((lg p (al TT nu s) : ℝ)) ^ 2

def gsum (p : ℕ) (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) : ℝ :=
  ∑ s ∈ TT, ∑' e : ℕ, if 2 * e + 1 ∈ DSet TT s then 0 else gain p TT nu s (2 * e + 1)

def g0 (p r0 r1 rb : ℕ) (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ) : ℝ :=
  gsum p TT nu - de p r0 r1 rb TT nu

def fact_lg : Prop :=
  ∀ p : ℕ, p.Prime → ∀ e : ℕ, (e : ℝ) / ((p : ℝ) - 1) - lg p e ≤ (padicValNat p e.factorial : ℝ)

def fact_gam : Prop :=
  ∀ p : ℕ, 2 ≤ p → gam p = (p : ℝ) / ((p : ℝ) ^ 2 - 1) ∧
    HasSum (fun e : ℕ => ((p : ℝ) ^ (2 * e + 1))⁻¹) (gam p) ∧ gam p = 1 / ((p : ℝ) - 1) - rho p

def fact_d : Prop :=
  ∀ n' : ℕ, Even n' → ∀ s s' : Fin n', OtherPar s s' →
    IsLeast {e : ℕ | 1 ≤ e ∧ posAdd s e = s'} (dLev s s') ∧ Odd (dLev s s')

def fact_dinj : Prop := ∀ (n' : ℕ) (s s' s'' : Fin n'), dLev s s' = dLev s s'' → s' = s''

end Numbers

section Series

variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)

structure ValR : Prop where
  val : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc
  p_nonunit : ((p : Kc))⁻¹ ∉ Oc

def geV (x : Kc) (g : ℝ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℝ) ≤ g * b → x ^ b * (p : Kc) ^ (-a) ∈ Oc

def gaussGe {τ : Type} (y : MvPolynomial τ Kc) (g : ℝ) : Prop := ∀ n, geV p Oc (MvPolynomial.coeff n y) g

def IntSer {σ : Type} (f : MvPowerSeries σ Kc) : Prop := ∀ n, MvPowerSeries.coeff n f ∈ Oc

def JetInt {σ : Type} (f : MvPowerSeries σ Kc) : Prop :=
  ∀ n : σ →₀ ℕ, (∏ x ∈ n.support, ((n x).factorial : Kc)) * MvPowerSeries.coeff n f ∈ Oc

end Series

structure Shape where
  nV : ℕ
  n' : Fin nV → ℕ
  r0 : ℕ
  r1 : ℕ

namespace Shape

variable (Sh : Shape)

abbrev ZV : Type := Σ v : Fin Sh.nV, FormalGroupSystem.Zidx (Sh.n' v) Sh.r0 Sh.r1

abbrev FrV : Type := Σ v : Fin Sh.nV, Fin (Sh.n' v) × ℕ × Fin Sh.r0

abbrev Wt : Type := ∀ v : Fin Sh.nV, Fin (Sh.n' v) → ℕ → ℤ

abbrev ColCh : Type := ∀ v : Fin Sh.nV, Fin (Sh.n' v) → ℕ → ℕ → Fin Sh.r1

def colHt (rb : ℕ) (nu : Sh.Wt) (v : Fin Sh.nV) (s : Fin (Sh.n' v)) (c : ℕ) : ℕ :=
  ((Icc 1 rb).filter fun i => (c : ℤ) < nu v s i).card

def colFac (rb : ℕ) (nu : Sh.Wt) (I : Sh.ColCh) (v : Fin Sh.nV) (s : Fin (Sh.n' v)) (c : ℕ) :
    MvPolynomial Sh.ZV (MvPolynomial Sh.FrV ℤ) :=
  Matrix.det (Matrix.of fun (i i' : Fin (Sh.colHt rb nu v s c)) =>
    ∑ a : Fin Sh.r0,
      MvPolynomial.C (MvPolynomial.X (⟨v, (s, i.val, a)⟩ : Sh.FrV)) *
        MvPolynomial.X (⟨v, (s, a, I v s c i'.val)⟩ : Sh.ZV))

def PI (rb : ℕ) (nu : Sh.Wt) (I : Sh.ColCh) : MvPolynomial Sh.ZV (MvPolynomial Sh.FrV ℤ) :=
  ∏ v : Fin Sh.nV, ∏ s : Fin (Sh.n' v), ∏ c ∈ range (nu v s 1).toNat, Sh.colFac rb nu I v s c

variable {Kc : Type} [Field Kc] (Oc : Subring Kc)

def KG (rb : ℕ) (nu : Sh.Wt) (Th : MvPowerSeries Sh.ZV Kc) : AddSubgroup (MvPolynomial Sh.FrV Kc) :=
  AddSubgroup.closure {y | ∃ (I : Sh.ColCh) (g : MvPolynomial Sh.FrV Kc), (∀ n, MvPolynomial.coeff n g ∈ Oc) ∧
    y = g * FormalGroupSystem.applyD (Sh.PI rb nu I) Th}

variable (p : ℕ)

def sS (v : Fin Sh.nV) (e : Fin (Sh.n' v)) (a : Fin Sh.r0) (b : Fin Sh.r1) : MvPowerSeries Sh.ZV Kc :=
  fun n => ∑ l ∈ range (n.degree + 1),
    if n = Finsupp.single (⟨v, (FormalGroupSystem.posSub e (2 * l), a, b)⟩ : Sh.ZV) (p ^ (2 * l)) then (-1) ^ l else 0

def hhV (v : Fin Sh.nV) (u : Fin (Sh.n' v) → Kc) : MvPowerSeries Sh.ZV Kc :=
  ∑ s : Fin (Sh.n' v), MvPowerSeries.C (u s) *
    ∑ a : Fin Sh.r0, ∑ b : Fin Sh.r1, (Sh.sS p v s a b) ^ p * Sh.sS p v (posAdd s 1) a b

def InProd (h : Fin Sh.nV → MvPowerSeries Sh.ZV Kc) (F : MvPowerSeries Sh.ZV Kc) : Prop :=
  ∃ g : (Fin Sh.nV → ℕ) → MvPowerSeries Sh.ZV Kc, (∀ i, IntSer Oc (g i)) ∧
    ∀ α : Sh.ZV →₀ ℕ, MvPowerSeries.coeff α F =
      ∑ i ∈ Fintype.piFinset (fun _ : Fin Sh.nV => range (α.degree + 1)),
        MvPowerSeries.coeff α (MvPowerSeries.C (∏ v, ((p : Kc) ^ i v)⁻¹) * (∏ v, h v ^ i v) * g i)

def atPi (vp : Kc) (Th : MvPowerSeries Sh.ZV Kc) : MvPowerSeries Sh.ZV Kc :=
  fun n => vp ^ n.degree * MvPowerSeries.coeff n Th

def StrAt (vp : Kc) (Th : MvPowerSeries Sh.ZV Kc) : Prop :=
  ∃ u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc, (∀ v s, u v s ∈ Oc) ∧
    ∀ h' : Fin Sh.nV → MvPowerSeries Sh.ZV Kc,
      (∀ v, MvPowerSeries.constantCoeff (h' v) = 0 ∧ ∃ G, IntSer Oc G ∧
        h' v = Sh.hhV p v (u v) + MvPowerSeries.C (p : Kc) * G) →
      Sh.InProd Oc p h' (Sh.atPi vp Th)

def hhExp (v : Fin Sh.nV) (u : Fin (Sh.n' v) → Kc) : MvPowerSeries Sh.ZV Kc :=
  fun n => ∑ s : Fin (Sh.n' v), u s * ∑ a : Fin Sh.r0, ∑ b : Fin Sh.r1,
    ∑ l ∈ range (n.degree + 1), ∑ l' ∈ range (n.degree + 1),
      if n = Finsupp.single (⟨v, (FormalGroupSystem.posSub s (2 * l), a, b)⟩ : Sh.ZV) (p ^ (2 * l + 1)) +
          Finsupp.single (⟨v, (FormalGroupSystem.posSub (posAdd s 1) (2 * l'), a, b)⟩ : Sh.ZV) (p ^ (2 * l'))
      then (-1) ^ (l + l') else 0

end Shape

section Core

variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc) (Sh : Shape)

structure HidaSetting (rb : ℕ) (nu : Sh.Wt) (vp : Kc) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  valR : ValR p Oc
  vp_pow : vp ^ (p ^ 2 - 1) = (p : Kc)
  even : ∀ v, Even (Sh.n' v)
  two_le : ∀ v, 2 ≤ Sh.n' v
  part : ∀ v, IsPart Sh.r0 (nu v)
  rb_ge : Sh.r0 ≤ rb

def expansion : Prop :=
  p.Prime → p ≠ 2 → ValR p Oc → ∀ (v : Fin Sh.nV) (u : Fin (Sh.n' v) → Kc), (∀ s, u s ∈ Oc) →
    ∃ Y : MvPowerSeries Sh.ZV Kc, IntSer Oc Y ∧
      Sh.hhV p v u = Sh.hhExp p v u + MvPowerSeries.C (p : Kc) * Y

def fact_idx : Prop :=
  ∀ n' : ℕ, Even n' → ∀ (s : Fin n') (l l' : ℕ),
    posAdd (FormalGroupSystem.posSub s (2 * l)) (2 * l + 1) = posAdd (FormalGroupSystem.posSub (posAdd s 1) (2 * l')) (2 * l') ∧
    OtherPar (FormalGroupSystem.posSub s (2 * l)) (FormalGroupSystem.posSub (posAdd s 1) (2 * l'))

def JetNonnegativeValuation (rb : ℕ) (nu : Sh.Wt) (Th : MvPowerSeries Sh.ZV Kc) : Prop :=
  ∀ y ∈ Sh.KG Oc rb nu Th, gaussGe p Oc y 0

def StatementJetNonnegative : Prop :=
  ∀ (rb : ℕ) (nu : Sh.Wt) (Th : MvPowerSeries Sh.ZV Kc), JetInt Oc Th → JetNonnegativeValuation p Oc Sh rb nu Th

def valuationLowerBound (rb : ℕ) (nu : Sh.Wt) (TT : ∀ v, Finset (Fin (Sh.n' v))) : ℝ :=
  ∑ v, (gsum p (TT v) (nu v) - de p Sh.r0 Sh.r1 rb (TT v) (nu v))

def ValuationOneKernel (rb : ℕ) (nu : Sh.Wt) (Th : MvPowerSeries Sh.ZV Kc) : Prop :=
  ∀ TT : ∀ v, Finset (Fin (Sh.n' v)), ∀ y ∈ Sh.KG Oc rb nu Th,
    gaussGe p Oc y (valuationLowerBound p Sh rb nu TT) ∧ gaussGe p Oc y 0

def StatementValuationOneKernel : Prop :=
  ∀ (rb : ℕ) (nu : Sh.Wt) (vp : Kc) (Th : MvPowerSeries Sh.ZV Kc), HidaSetting p Oc Sh rb nu vp →
    Sh.StrAt Oc p vp Th → JetNonnegativeValuation p Oc Sh rb nu Th → ValuationOneKernel p Oc Sh rb nu Th

def KernelValuationBoundGains (rb : ℕ) (nu : Sh.Wt) (Th : MvPowerSeries Sh.ZV Kc) : Prop :=
  ∀ TT : ∀ v, Finset (Fin (Sh.n' v)), ∀ y ∈ Sh.KG Oc rb nu Th,
    gaussGe p Oc y (∑ v, g0 p Sh.r0 Sh.r1 rb (TT v) (nu v))

theorem corollary_valuation_of_theorem {rb : ℕ} {nu : Sh.Wt} {Th : MvPowerSeries Sh.ZV Kc} (h : ValuationOneKernel p Oc Sh rb nu Th) :
    KernelValuationBoundGains p Oc Sh rb nu Th := fun TT y hy => (h TT y hy).1

end Core

def StatementJetNonnegativeAllFields : Prop := ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape), StatementJetNonnegative p Oc Sh
def StatementValuationAllFields : Prop := ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape), StatementValuationOneKernel p Oc Sh
def expansionE : Prop := ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape), expansion p Oc Sh

def CorollaryNotationWeights : Prop :=
  ∀ (p n' k1 t j : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ), 1 ≤ k1 →
    g0 p (FormalGroupSystem.NN k1 t (j - 1)) (FormalGroupSystem.NN k1 t j) (FormalGroupSystem.NN k1 t j) TT (fun s i => FormalGroupSystem.nu t lam0 w j s i) =
      FormalGroupSystem.gA p t TT lam0 w j

def OneTopOddLevelsGain : Prop :=
  ∀ (p r0 r1 rb n' : ℕ) (nu : Fin n' → ℕ → ℤ) (s : Fin n'), DSet {s} s = ∅ ∧
    g0 p r0 r1 rb {s} nu = ∑' e : ℕ, gain p {s} nu s (2 * e + 1) - de p r0 r1 rb {s} nu

def OneParityTopsNoExclusion : Prop :=
  ∀ (p r0 r1 rb n' : ℕ) (nu : Fin n' → ℕ → ℤ) (TT : Finset (Fin n')),
    (∀ s ∈ TT, ∀ s' ∈ TT, ¬ OtherPar s s') →
    g0 p r0 r1 rb TT nu = ∑ s ∈ TT, ∑' e : ℕ, gain p TT nu s (2 * e + 1) - de p r0 r1 rb TT nu

def NoTopGainNegDefect : Prop :=
  ∀ (p r0 r1 rb n' : ℕ) (nu : Fin n' → ℕ → ℤ), g0 p r0 r1 rb (∅ : Finset (Fin n')) nu = -de p r0 r1 rb ∅ nu

section AtG

variable {p : ℕ} [Fact p.Prime] (X : FormalGroupSystem.Sys p)

def shX (j : ℕ) : Shape := ⟨X.G.P.nV, X.G.P.n', FormalGroupSystem.NN X.G.P.m X.t j, FormalGroupSystem.NN X.G.P.m X.t (j + 1)⟩

def nuX (j : ℕ) : (shX X j).Wt := fun v s i => X.nuv v (j + 1) s i

def rbX (j : ℕ) : ℕ := FormalGroupSystem.NN X.G.P.m X.t (j + 1)

variable {X} (Y : FormalGroupSystem.Pend X)

def ThX (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Y.Frm j La La') : MvPowerSeries (shX X j).ZV Y.Kc :=
  X.ThZA Y.Kc j (Y.ThA j La La' φ)

def JetIntegralAlongFrames (_D : D7) (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Y.Frm j La La', JetInt Y.Oc (ThX Y j La La' φ)

def ThetaStructureInFrames (_D : D7) (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La') (vp : Y.Kc), vp ^ (p ^ 2 - 1) = (p : Y.Kc) →
      (shX X j).StrAt Y.Oc p vp (ThX Y j La La' φ)

def KernelEntriesNonnegValuation (_D : D7) (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Y.Frm j La La', JetNonnegativeValuation p Y.Oc (shX X j) (rbX X j) (nuX X j) (ThX Y j La La' φ)

def KernelSecondLevelBound (_D : D7) (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∃ φ : Y.Frm j La La', ∀ (f : MvPowerSeries (shX X j).ZV Y.Kc) (g : ℝ),
      (∀ I : (shX X j).ColCh, gaussGe p Y.Oc (FormalGroupSystem.applyD ((shX X j).PI (rbX X j) (nuX X j) I) f) g) →
      ∀ G ∈ (X.Pj j).HtupW La.2, Y.inLatC (j + 1) g La'.2 (Y.kerF j La La' (FormalGroupSystem.linSub (Y.bc j La La' φ) f) G)

def K2eq_G (_D : D7) (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∃ φ : Y.Frm j La La', ∀ (f : MvPowerSeries (shX X j).ZV Y.Kc) (g : ℝ),
      (∀ I : (shX X j).ColCh, gaussGe p Y.Oc (FormalGroupSystem.applyD ((shX X j).PI (rbX X j) (nuX X j) I) f) g) ↔
      ∀ G ∈ (X.Pj j).HtupW La.2, Y.inLatC (j + 1) g La'.2 (Y.kerF j La La' (FormalGroupSystem.linSub (Y.bc j La La' φ) f) G)

def ValuationKernelEntries (_D : D7) (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Y.Frm j La La', ValuationOneKernel p Y.Oc (shX X j) (rbX X j) (nuX X j) (ThX Y j La La' φ)

def KernelValuationBoundTops (_D : D7) (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Y.Frm j La La', ∀ y ∈ (shX X j).KG Y.Oc (rbX X j) (nuX X j) (ThX Y j La La' φ),
      gaussGe p Y.Oc y (∑ v, X.g0v v (j + 1))

def StatementJetIntegralityKernel (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X), JetIntegralAlongFrames D X Y → KernelEntriesNonnegValuation D X Y

def StatementValuationKernelEntries (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X), (∃ vp : Y.Kc, vp ^ (p ^ 2 - 1) = (p : Y.Kc)) →
    ThetaStructureInFrames D X Y → KernelEntriesNonnegValuation D X Y → ValuationKernelEntries D X Y

def KernelNonnegArbitraryPartitions (_D : D7) (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La') (rb : ℕ) (nu : (shX X j).Wt), (∀ v, IsPart (shX X j).r0 (nu v)) → (shX X j).r0 ≤ rb →
      JetNonnegativeValuation p Y.Oc (shX X j) rb nu (ThX Y j La La' φ)

def ValuationArbitraryPartitions (_D : D7) (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La') (rb : ℕ) (nu : (shX X j).Wt), (∀ v, IsPart (shX X j).r0 (nu v)) → (shX X j).r0 ≤ rb →
      ValuationOneKernel p Y.Oc (shX X j) rb nu (ThX Y j La La' φ)

def StatementValuationArbitraryPartitions (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X), (∃ vp : Y.Kc, vp ^ (p ^ 2 - 1) = (p : Y.Kc)) →
    ThetaStructureInFrames D X Y → JetIntegralAlongFrames D X Y → ValuationArbitraryPartitions D X Y

def StatementCorollaryKernelEntries (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : FormalGroupSystem.Sys p) (Y : FormalGroupSystem.Pend X), ValuationKernelEntries D X Y → KernelValuationBoundTops D X Y

end AtG

section AtD

variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)

abbrev shD (nH r0 r1 : ℕ) : Shape := ⟨nH, fun _ => 2, r0, r1⟩

def beD (nH r0 r1 : ℕ) (u : Fin nH → Kc) : MvPowerSeries (shD nH r0 r1).ZV Kc :=
  ∑ t : Fin nH, MvPowerSeries.C (u t) * ∑ a : Fin r0, ∑ b : Fin r1,
    MvPowerSeries.X (⟨t, ((0 : Fin 2), a, b)⟩ : (shD nH r0 r1).ZV) *
      MvPowerSeries.X (⟨t, ((1 : Fin 2), a, b)⟩ : (shD nH r0 r1).ZV)

def expK {σ : Type} (f : MvPowerSeries σ Kc) : MvPowerSeries σ Kc :=
  fun n => ∑ k ∈ range (n.degree + 1), ((k.factorial : Kc))⁻¹ * MvPowerSeries.coeff n (f ^ k)

def IntD (nH r0 r1 : ℕ) (Th : MvPowerSeries (shD nH r0 r1).ZV Kc) : Prop :=
  ∃ (S : Kc) (u : Fin nH → Kc) (F0 : MvPowerSeries (shD nH r0 r1).ZV Kc),
    geV p Oc S (-(1 / 2)) ∧ (∀ t, u t ∈ Oc) ∧ JetInt Oc F0 ∧
      Th = expK (-(MvPowerSeries.C S) * beD nH r0 r1 u) * F0

def ct {nH : ℕ} (rb : ℕ) (TT : Finset (Fin nH)) (nu : Fin nH → Fin 2 → ℕ → ℤ) (t : Fin nH) : ℤ :=
  sz rb (nu t) 0 - (if t ∈ TT then nu t 0 1 - nu t 0 2 else 0) + (if t ∈ TT then nu t 1 1 else 0)

def sec4 (nH r0 r1 rb : ℕ) (TT : Finset (Fin nH)) (nu : (shD nH r0 r1).Wt)
    (Th : MvPowerSeries (shD nH r0 r1).ZV Kc) : Prop :=
  ∀ y ∈ (shD nH r0 r1).KG Oc rb nu Th, gaussGe p Oc y (-(1 / 2) * ∑ t, (ct rb TT nu t : ℝ))

def StatementRamifiedPrimes : Prop :=
  ∀ (nH r0 r1 rb : ℕ) (TT : Finset (Fin nH)) (nu : (shD nH r0 r1).Wt) (Th : MvPowerSeries (shD nH r0 r1).ZV Kc),
    p.Prime → ValR p Oc → (∀ t, IsPart r0 (nu t)) → r0 ≤ rb → IntD p Oc nH r0 r1 Th →
      sec4 p Oc nH r0 r1 rb TT nu Th

end AtD

def StatementRamifiedAllFields : Prop := ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc), StatementRamifiedPrimes p Oc

section At22

open TaylorLogMetric

def valuationRingCp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := Subring.closure {x | ‖x‖ ≤ 1}

variable (D : D7) {p d : ℕ} (Po : Pos D p d) (N N' : ℕ)

def sh22 : Shape := ⟨Fintype.card {v // v ∈ Po.V}, fun _ => d, N, N'⟩

def toT (x : (sh22 D Po N N').ZV) : TVar D Po N N' :=
  ((x.2.1.val : ZMod d), ((Fintype.equivFin {v // v ∈ Po.V}).symm x.1, x.2.2.1, x.2.2.2))

variable {N N'} [Fact p.Prime] [NeZero d]

def Th22 (lam : Qbar →+* ℂ_[p]) (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E)
    (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E) (ep : ℂ_[p])
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : MvPowerSeries (sh22 D Po N N').ZV ℂ_[p] :=
  FormalGroupSystem.resV (toT D Po N N') (atLin (fun k j => ep * chg D lam Po P P' k j) (fun j => MvPowerSeries.X j) F)

def DerTie (lam : Qbar →+* ℂ_[p]) (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E)
    (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E)
    (L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E))
    (L' : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N' → D.host.E)) : Prop :=
  ∀ j : TVar D Po N N', ∃ (m : ℕ) (r : Fin m → ℂ_[p]) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E),
    (∀ k, IsIntP (r k)) ∧ (∀ k, y k ∈ YYl D L L') ∧
      ∀ k' : D.what₂.Tau × Fin N' × Fin N,
        chg D lam Po P P' k' j = ∑ k, r k * lamC lam (embT D k'.1 (y k k'.2.1 k'.2.2))

end At22

open TaylorLogMetric in

def JetIntegralityAwayFromD (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ D.host.d → ∀ (N N' : ℕ)
    (L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E))
    (L' : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N' → D.host.E))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
    admitted D N N' L L' → IsComb D T e lam L L' F → JetsInt D lam (YYl D L L') F

open TaylorLogMetric in

theorem jet_integrality_of_integral (D : D7) (T : Tor D) (e : FamE D) (h : int22 D T e) : JetIntegralityAwayFromD D T e :=
  fun p _ lam hp N N' L L' F hA hC => ((h p lam N N' L L' hA).1 hp F hC).2.1

open TaylorLogMetric in

def InertOrbitsEven (D : D7) : Prop :=
  ∀ (p d : ℕ) (_ : Pos D p d), p.Prime → jacobiSym (-(D.host.d : ℤ)) p = -1 → Even d

open TaylorLogMetric in

def ValuationThetaFamily (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → AllSplit D p →
    ∀ (ep : ℂ_[p]), ‖ep‖ = 1 → ∀ (d : ℕ) [NeZero d] (Po : Pos D p d) (N N' : ℕ)
      (L : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E))
      (L' : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N' → D.host.E))
      (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E)
      (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E)
      (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
      admitted D N N' L L' → (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L (P v)) →
      (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L' (P' v)) →
      IsComb D T e lam L L' F → DerTie D Po lam P P' L L' →
      ∀ (rb : ℕ) (nu : (sh22 D Po N N').Wt), (∀ v, IsPart N (nu v)) → N ≤ rb →
        ValuationOneKernel p (valuationRingCp p) (sh22 D Po N N') rb nu (Th22 D Po lam P P' ep F)

open TaylorLogMetric in

def StatementValuationTheta (D : D7) : Prop :=
  ∀ (T : Tor D) (e : FamE D), InertOrbitsEven D → str22 D T e → int22 D T e → ValuationThetaFamily D T e

section Leaf

def IsLeaf (p : ℕ) {K : Type} [Field K] {h : ℕ} (t : Fin h → PowerSeries K) : Prop :=
  (∀ i, PowerSeries.constantCoeff (t i) = 0) ∧
  ∀ (i : Fin h) (n : ℕ), ∑ k ∈ range (n + 1), PowerSeries.coeff n ((t (FormalGroupSystem.posSub i k)) ^ (p ^ (2 * k))) / (p : K) ^ k =
    if i.val = 0 ∧ n = 1 then 1 else 0

def ze3 (p : ℕ) {K : Type} [Field K] {h : ℕ} (t : Fin h → PowerSeries K) (i1 : Fin h) : PowerSeries K :=
  PowerSeries.mk fun n =>
    ∑ k ∈ range (n + 1), PowerSeries.coeff n ((t (FormalGroupSystem.posSub i1 k)) ^ (p ^ (2 * k + 1))) / (p : K) ^ (k + 1)

def c3 (p : ℕ) {K : Type} [Field K] {h : ℕ} (t : Fin h → PowerSeries K) (i0 : Fin h) : K :=
  PowerSeries.coeff (p ^ 3) (ze3 p t (posAdd i0 1))

def fact_leaf : Prop :=
  ∀ (p : ℕ) (K : Type) [Field K] [CharZero K] (h : ℕ), 2 ≤ p → 1 ≤ h → ∃! t : Fin h → PowerSeries K, IsLeaf p t

def Sp (p n : ℕ) : ℕ := (Nat.digits p n).sum

def ZetaThreeLeadingCoefficient : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (h : ℕ) (i0 : Fin h), 2 ≤ h → i0.val = 0 → ∀ t : Fin h → PowerSeries ℚ, IsLeaf p t →
    (∀ n < p ^ 3, PowerSeries.coeff n (ze3 p t (posAdd i0 1)) = 0) ∧
      c3 p t i0 = ((p : ℚ) ^ 2)⁻¹ - ((p : ℚ) ^ (p + 1))⁻¹

def ZetaThreeValuation : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (h : ℕ) (i0 : Fin h), i0.val = 0 → ∀ t : Fin h → PowerSeries ℚ, IsLeaf p t →
    c3 p t i0 ≠ 0 ∧ padicValRat p (c3 p t i0) = -((p : ℤ) + 1)

def AllHitsTerm : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (h : ℕ) (i0 : Fin h), i0.val = 0 → ∀ t : Fin h → PowerSeries ℚ, IsLeaf p t →
    ∀ (A0 : ℚ), A0 ≠ 0 → padicValRat p A0 = 0 → ∀ κ : ℕ, 1 ≤ κ →
      padicValRat p (((p ^ 3 * κ).factorial : ℚ) * A0 * (-c3 p t i0) ^ κ) =
        (κ : ℤ) * (p : ℤ) ^ 2 + (padicValNat p κ.factorial : ℤ)

def ValuationNumbers : Prop :=
  ∀ p : ℕ, p.Prime → gam p * ((p : ℝ) ^ 3 + 1) = (p : ℝ) ^ 2 + (p : ℝ) / ((p : ℝ) - 1) ∧
    (∀ κ : ℕ, (κ : ℝ) * (p : ℝ) ^ 2 + (padicValNat p κ.factorial : ℝ) =
      gam p * ((p : ℝ) ^ 3 + 1) * κ - κ - (Sp p κ : ℝ) / ((p : ℝ) - 1)) ∧
    (∀ κ : ℕ, (Sp p κ : ℝ) / ((p : ℝ) - 1) ≤ lg p κ) ∧ (∀ κ : ℕ, 1 ≤ κ → 1 ≤ Sp p κ) ∧ ∀ e : ℕ, Sp p (p ^ e) = 1

variable (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc)

def IsU (x : Kc) : Prop := x ≠ 0 ∧ x ∈ Oc ∧ x⁻¹ ∈ Oc

def eqV (x : Kc) (N : ℤ) : Prop := IsU Oc (x * (p : Kc) ^ (-N))

def inZ (f : PowerSeries Kc) : MvPowerSeries (Fin 2) Kc := fun n => if n 1 = 0 then PowerSeries.coeff (n 0) f else 0

def jet2 (F : MvPowerSeries (Fin 2) Kc) (M κ : ℕ) : Kc :=
  (M.factorial : Kc) * (κ.factorial : Kc) * MvPowerSeries.coeff (Finsupp.single 0 M + Finsupp.single 1 κ) F

def leafKer (u : Kc) (ze : PowerSeries Kc) (A Psi : MvPowerSeries (Fin 2) Kc) : MvPowerSeries (Fin 2) Kc :=
  A * expK (-(MvPowerSeries.C u * inZ ze * MvPowerSeries.X 1)) * expK Psi

def H1 (vp : Kc) (A : MvPowerSeries (Fin 2) Kc) : Prop :=
  (∀ n : Fin 2 →₀ ℕ, vp ^ n.degree * MvPowerSeries.coeff n A ∈ Oc) ∧ IsU Oc (MvPowerSeries.constantCoeff A)

def H2 (Psi : MvPowerSeries (Fin 2) Kc) : Prop :=
  ∀ n : Fin 2 →₀ ℕ, (n 1 < p → MvPowerSeries.coeff n Psi = 0) ∧
    geV p Oc (MvPowerSeries.coeff n Psi) (-1 + 1 / ((p : ℝ) - 1) - ((n 0 : ℝ) + (n 1 : ℝ)) * rho p)

def JetSecondVariable : Prop :=
  p.Prime → p ≠ 2 → ValR p Oc → ∀ vp : Kc, vp ^ (p ^ 2 - 1) = (p : Kc) →
    ∀ (h : ℕ) (i0 : Fin h), 2 ≤ h → i0.val = 0 → ∀ t : Fin h → PowerSeries Kc, IsLeaf p t →
    ∀ (u : Kc) (A Psi : MvPowerSeries (Fin 2) Kc), IsU Oc u → H1 Oc vp A → H2 p Oc Psi → ∀ κ : ℕ, 1 ≤ κ →
      eqV p Oc (jet2 (leafKer u (ze3 p t (posAdd i0 1)) A Psi) (p ^ 3 * κ) κ)
        ((κ : ℤ) * (p : ℤ) ^ 2 + (padicValNat p κ.factorial : ℤ))

def JetAllHitsApproximation : Prop :=
  p.Prime → p ≠ 2 → ValR p Oc → ∀ vp : Kc, vp ^ (p ^ 2 - 1) = (p : Kc) →
    ∀ (h : ℕ) (i0 : Fin h), 2 ≤ h → i0.val = 0 → ∀ t : Fin h → PowerSeries Kc, IsLeaf p t →
    ∀ (u : Kc) (A Psi : MvPowerSeries (Fin 2) Kc), IsU Oc u → H1 Oc vp A → H2 p Oc Psi → ∀ κ : ℕ, 1 ≤ κ →
      ∃ ε : Kc, geV p Oc ε (1 / 6) ∧
        jet2 (leafKer u (ze3 p t (posAdd i0 1)) A Psi) (p ^ 3 * κ) κ =
          ((p ^ 3 * κ).factorial : Kc) * MvPowerSeries.constantCoeff A * (-(u * c3 p t i0)) ^ κ * (1 + ε)

def TTT (n' : ℕ) : Set (ℕ × ℕ) :=
  {x | ∃ j j' : ℕ, Odd j ∧ Even j' ∧
    ((x = (p ^ j, p ^ j') ∧ j % n' = (3 + j') % n') ∨ (x = (p ^ j', p ^ j) ∧ (3 + j) % n' = j' % n'))}

def fact_TTT : Prop :=
  ∀ p n' : ℕ, 2 ≤ p → 4 ≤ n' → ∀ x ∈ TTT p n',
    (x.2 = 1 → ∃ j : ℕ, j % n' = 3 ∧ x.1 = p ^ j ∧ p ^ 3 ≤ x.1) ∧ (x.2 ≠ 1 → p ≤ x.2)

abbrev shL (n' : ℕ) : Shape := ⟨1, fun _ => n', 1, 1⟩

def expXY (n' : ℕ) (h4 : 4 ≤ n') (a b : ℕ) : (shL n').ZV →₀ ℕ :=
  Finsupp.single (⟨0, ((⟨0, by omega⟩ : Fin n'), 0, 0)⟩ : (shL n').ZV) a +
    Finsupp.single (⟨0, ((⟨3, by omega⟩ : Fin n'), 0, 0)⟩ : (shL n').ZV) b

def ExpansionMonomialsSupport : Prop :=
  ∀ (p n' : ℕ) (Kc : Type) [Field Kc] (u : Fin n' → Kc), 2 ≤ p → Even n' → ∀ h4 : 4 ≤ n', ∀ a b : ℕ,
    MvPowerSeries.coeff (expXY n' h4 a b) ((shL n').hhExp p 0 u) ≠ 0 → (a, b) ∈ TTT p n'

def modProd (m : ℕ × ℕ →₀ ℕ) (i3 : ℕ) (u : ℕ × ℕ → Kc) (Y0 U : MvPowerSeries (Fin 2) Kc) : MvPowerSeries (Fin 2) Kc :=
  MvPowerSeries.C (((p : Kc) ^ ((∑ x ∈ m.support, m x) + i3))⁻¹) *
    (∏ x ∈ m.support, (MvPowerSeries.C (u x) * MvPowerSeries.X 0 ^ x.1 * MvPowerSeries.X 1 ^ x.2) ^ m x) *
    (MvPowerSeries.C (p : Kc) * Y0) ^ i3 * U

def hits (m : ℕ × ℕ →₀ ℕ) : ℕ := ∑ x ∈ m.support.filter (fun x => x.2 = 1), m x

def typeZ (m : ℕ × ℕ →₀ ℕ) : ℕ := ∑ x ∈ m.support.filter (fun x => x.2 ≠ 1), m x

def modJet (vp : Kc) (κ : ℕ) (F : MvPowerSeries (Fin 2) Kc) : Kc := (vp ^ (p ^ 3 * κ + κ))⁻¹ * jet2 F (p ^ 3 * κ) κ

def RankOneModuleClause : Prop :=
  p.Prime → p ≠ 2 → ValR p Oc → ∀ vp : Kc, vp ^ (p ^ 2 - 1) = (p : Kc) → ∀ n' : ℕ, Even n' → 4 ≤ n' →
    ∀ (m : ℕ × ℕ →₀ ℕ) (i3 : ℕ) (u : ℕ × ℕ → Kc) (Y0 U : MvPowerSeries (Fin 2) Kc),
      (∀ x ∈ m.support, x ∈ TTT p n') → (∀ x, u x ∈ Oc) → IntSer Oc Y0 → MvPowerSeries.constantCoeff Y0 = 0 → IntSer Oc U →
      ∀ κ : ℕ, 1 ≤ κ →
        (¬ (hits m + p * typeZ m ≤ κ) → modJet p vp κ (modProd p m i3 u Y0 U) = 0) ∧
        geV p Oc (modJet p vp κ (modProd p m i3 u Y0 U))
          (gam p * ((p : ℝ) ^ 3 + 1) * κ - 2 * lg p κ - hits m - typeZ m) ∧
        geV p Oc (modJet p vp κ (modProd p m i3 u Y0 U))
          (gam p * ((p : ℝ) ^ 3 + 1) * κ - 2 * ((Sp p κ : ℝ) / ((p : ℝ) - 1)) - hits m - typeZ m)

def ProductHitsCoefficient : Prop :=
  p.Prime → p ≠ 2 → ∀ n' : ℕ, Even n' → 4 ≤ n' →
    ∀ (m : ℕ × ℕ →₀ ℕ) (i3 : ℕ) (u : ℕ × ℕ → Kc) (Y0 U : MvPowerSeries (Fin 2) Kc),
      (∀ x ∈ m.support, x ∈ TTT p n') → MvPowerSeries.constantCoeff Y0 = 0 → ∀ κ : ℕ, 1 ≤ κ → hits m = κ →
        MvPowerSeries.coeff (Finsupp.single 0 (p ^ 3 * κ) + Finsupp.single 1 κ) (modProd p m i3 u Y0 U) =
          if m = Finsupp.single (p ^ 3, 1) κ ∧ i3 = 0 then
            ((p : Kc) ^ κ)⁻¹ * u (p ^ 3, 1) ^ κ * MvPowerSeries.constantCoeff U else 0

def ValueWithoutHits : Prop :=
  p.Prime → p ≠ 2 → ValR p Oc → ∀ vp : Kc, vp ^ (p ^ 2 - 1) = (p : Kc) →
    ∀ U : MvPowerSeries (Fin 2) Kc, IntSer Oc U → ∀ κ : ℕ, 1 ≤ κ →
      geV p Oc (modJet p vp κ U) (gam p * ((p : ℝ) ^ 3 + 1) * κ - 2 * ((Sp p κ : ℝ) / ((p : ℝ) - 1))) ∧
      geV p Oc (modJet p vp κ U) (gam p * ((p : ℝ) ^ 3 + 1) * κ - 2 * lg p κ)

def ThreeAdicExceptionalCases : Prop :=
  ∀ (h : ℕ) (i0 : Fin h), i0.val = 0 → ∀ t : Fin h → PowerSeries ℚ, IsLeaf 3 t →
    ∀ κ v : ℕ, ((κ = 3 ∧ v = 13) ∨ (κ = 9 ∧ v = 40) ∨ (κ = 27 ∧ v = 121)) →
      padicValRat 3 (PowerSeries.coeff (27 * κ) ((-ze3 3 t (posAdd i0 1)) ^ κ) / (κ.factorial : ℚ)) = -(v : ℤ) ∧
      (v : ℤ) = 4 * κ + padicValNat 3 κ.factorial

end Leaf

def JetClausesAllFields : Prop := ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc), JetSecondVariable p Oc
def JetTermAllFields : Prop := ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc), JetAllHitsApproximation p Oc
def RankOneModuleAllFields : Prop := ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc), RankOneModuleClause p Oc
def ProductHitsCoefficientAllFields : Prop := ∀ (p : ℕ) (Kc : Type) [Field Kc], ProductHitsCoefficient p (Kc := Kc)
def ValueWithoutHitsAllFields : Prop := ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc), ValueWithoutHits p Oc

def ValuationStatementsAtKernels (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (X : FormalGroupSystem.Sys (D.what₂.places.resChar w)) (Y : FormalGroupSystem.Pend X),
    X.G = D.gat u w h →
    (∃ vp : Y.Kc, vp ^ ((D.what₂.places.resChar w) ^ 2 - 1) = ((D.what₂.places.resChar w : ℕ) : Y.Kc)) →
    JetIntegralAlongFrames D X Y → ThetaStructureInFrames D X Y → KernelEntriesNonnegValuation D X Y ∧ ValuationKernelEntries D X Y ∧ KernelValuationBoundTops D X Y

def StatementFamilyJetIntegrality {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), StatementJetIntegralityKernel (Fm.D x i)
def StatementFamilyValuationKernel {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), StatementValuationKernelEntries (Fm.D x i)
def StatementFamilyArbitraryPartitions {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), StatementValuationArbitraryPartitions (Fm.D x i)
def StatementFamilyCorollaryKernel {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), StatementCorollaryKernelEntries (Fm.D x i)
def StatementFamilyValuationsAtKernels {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), ValuationStatementsAtKernels (Fm.D x i)
def StatementFamilyValuationTheta {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), StatementValuationTheta (Fm.D x i)

theorem one_top_odd_levels_gain : OneTopOddLevelsGain := by
  intro p r0 r1 rb n' nu s
  have h : DSet {s} s = ∅ := by
    unfold DSet
    rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    simp [OtherPar]
  refine ⟨h, ?_⟩
  unfold g0 gsum
  simp [h]

theorem one_parity_tops_excluded_none : OneParityTopsNoExclusion := by
  intro p r0 r1 rb n' nu TT hT
  unfold g0 gsum
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have h : DSet TT s = ∅ := by
    unfold DSet
    rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]
    intro x hx
    exact hT s hs x hx
  simp [h]

theorem no_top_gain_neg_defect : NoTopGainNegDefect := by
  intro p r0 r1 rb n' nu
  unfold g0 gsum
  simp

theorem fact_dinj_pf : fact_dinj := by
  intro n' s s' s'' h
  unfold dLev at h
  have h1 := s.isLt
  have h2 := s'.isLt
  have h3 := s''.isLt
  apply Fin.ext
  by_cases a : s.val ≤ s'.val <;> by_cases b : s.val ≤ s''.val
  · have e1 : (s'.val + n' - s.val) % n' = s'.val - s.val := by
      rw [show s'.val + n' - s.val = (s'.val - s.val) + n' by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have e2 : (s''.val + n' - s.val) % n' = s''.val - s.val := by
      rw [show s''.val + n' - s.val = (s''.val - s.val) + n' by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · have e1 : (s'.val + n' - s.val) % n' = s'.val - s.val := by
      rw [show s'.val + n' - s.val = (s'.val - s.val) + n' by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have e2 : (s''.val + n' - s.val) % n' = s''.val + n' - s.val := Nat.mod_eq_of_lt (by omega)
    omega
  · have e2 : (s''.val + n' - s.val) % n' = s''.val - s.val := by
      rw [show s''.val + n' - s.val = (s''.val - s.val) + n' by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have e1 : (s'.val + n' - s.val) % n' = s'.val + n' - s.val := Nat.mod_eq_of_lt (by omega)
    omega
  · have e1 : (s'.val + n' - s.val) % n' = s'.val + n' - s.val := Nat.mod_eq_of_lt (by omega)
    have e2 : (s''.val + n' - s.val) % n' = s''.val + n' - s.val := Nat.mod_eq_of_lt (by omega)
    omega

theorem al_eq {n' k1 : ℕ} (t j : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ)
    (hk : 1 ≤ k1) (s : Fin n') : al TT (fun s i => FormalGroupSystem.nu t lam0 w j s i) s = FormalGroupSystem.al TT lam0 s := by
  unfold al FormalGroupSystem.al FormalGroupSystem.nu
  have h1 : (1 ≤ 1 ∧ 1 ≤ k1 + 1) := ⟨le_refl _, by omega⟩
  have h2 : (1 ≤ 2 ∧ 2 ≤ k1 + 1) := ⟨by omega, by omega⟩
  simp only [h1, h2, and_self, if_true]
  split_ifs <;> ring

theorem corollary_notation_weights_holds : CorollaryNotationWeights := by
  intro p n' k1 t j TT lam0 w hk
  have ha := al_eq t j TT lam0 w hk
  unfold g0 gsum de FormalGroupSystem.gA FormalGroupSystem.de gain low sz lg FormalGroupSystem.lsz
  simp only [ha]
  rfl

section G
variable {p : ℕ} [Fact p.Prime] (X : FormalGroupSystem.Sys p)

theorem colExp_zero (j : ℕ) (I : X.ColCh j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (c : ℕ) :
    X.colExp j I (fun _ => 0) v s c = 0 := by
  unfold FormalGroupSystem.Sys.colExp
  split_ifs <;> simp

theorem PI_X (j : ℕ) (I : X.ColCh j) : X.PI j I (fun _ => 0) = (shX X j).PI (rbX X j) (nuX X j) I := by
  unfold FormalGroupSystem.Sys.PI Shape.PI
  simp only [colExp_zero, pow_zero, one_mul]
  rfl

theorem Nprime_zero {n' k1 : ℕ} (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) :
    FormalGroupSystem.Nprime lam0 w j 0 = 0 := by
  unfold FormalGroupSystem.Nprime
  simp

theorem admissible_valuation_zero (D : Formalism.BasicNotions.D7) (Y : FormalGroupSystem.Pend X) (h : KernelSecondLevelBound D X Y) :
    ∀ j < X.mm, ∀ (La : X.Lt j) (c' : X.Lv.comp (j + 1)) (L' L'' : (X.Pj (j + 1)).Tup),
    (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup L' → (∀ v', L'' v' = L' v') →
    ∃ φ : Y.Frm j La (c', L''), ∀ (f : MvPowerSeries (X.ZA j) Y.Kc) (g : ℝ),
      (∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
        Y.geC (MvPolynomial.coeff n (FormalGroupSystem.applyD (X.PI j I (fun _ => 0)) f)) g) →
      ∀ G ∈ (X.Pj j).HtupW La.2, Y.inLatC (j + 1) g L'
        ((∏ v : X.Pl, (p : X.G.Kf) ^ (FormalGroupSystem.Nprime (X.G.P.lam0 v) (X.w v) (j + 1) 0)) •
          Y.kerF j La (c', L'') (FormalGroupSystem.linSub (Y.bc j La (c', L'') φ) f) G) := by
  intro j hj La c' L' L'' hLa hL' hEq
  have e : L'' = L' := funext hEq
  subst e
  obtain ⟨φ, hφ⟩ := h j hj La (c', L'') hLa hL'
  refine ⟨φ, fun f g hI G hG => ?_⟩
  simp only [Nprime_zero, zpow_zero, Finset.prod_const_one, one_smul]
  refine hφ f g (fun I n => ?_) G hG
  have e2 : (shX X j).PI (rbX X j) (nuX X j) I = X.PI j I (fun _ => 0) := (PI_X X j I).symm
  rw [e2]
  exact hI I n

end G

theorem fact_gam_pf : fact_gam := by
  intro p hp
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (p : ℝ) ≠ 0 := by linarith
  have h3 : (p : ℝ) + 1 ≠ 0 := by linarith
  refine ⟨by unfold gam rho; ring, ?_, ?_⟩
  · have hlt : ((p : ℝ) ^ 2)⁻¹ < 1 := by
      apply inv_lt_one_of_one_lt₀
      nlinarith
    have hg := (hasSum_geometric_of_lt_one (r := ((p : ℝ) ^ 2)⁻¹) (by positivity) hlt).mul_left ((p : ℝ)⁻¹)
    have e1 : (fun e : ℕ => ((p : ℝ) ^ (2 * e + 1))⁻¹) = fun i => (p : ℝ)⁻¹ * ((p : ℝ) ^ 2)⁻¹ ^ i := by
      funext e
      rw [pow_succ, pow_mul, mul_inv, inv_pow]
      ring
    have e2 : gam p = (p : ℝ)⁻¹ * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
      unfold gam rho
      have h4 : (1 - ((p : ℝ) ^ 2)⁻¹) = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 := by
        field_simp
      rw [h4, inv_div]
      field_simp
    rw [e1, e2]
    exact hg
  · unfold gam rho
    have : (p : ℝ) ^ 2 - 1 = ((p : ℝ) - 1) * ((p : ℝ) + 1) := by ring
    rw [this]
    field_simp
    ring

end Formalism.MainNotions.KernelEntryData
