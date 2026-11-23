import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealEqMulDdConst
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

variable (d : IndexData)

def IsRatReal (x : ℝ) : Prop := ∃ q : ℚ, x = q

def IsRatWeight (lam : Weight d) : Prop := ∀ p, ∃ q : ℚ, lam p = q

def sumNorm (lam : Weight d) : ℝ := ∑ p, |lam p|

def degPolyR : LamPoly d := map (algebraMap ℚ ℝ) (degPoly d)

def degR (lam : Weight d) : ℝ := eval lam (degPolyR d)

def evalLS (Q : MvPolynomial (Option (Idx d)) ℝ) (lam : Weight d) (s : ℝ) : ℝ :=
  eval (fun o => Option.elim o s lam) Q

def etaConstant (η : Weight d) : ℝ := 2 * ‖η‖

structure VolumeSystem where

  vol : ℝ
  vol_pos : 0 < vol

  P : ℤ → LamPoly d

  Ps : ℤ → MvPolynomial (Option (Idx d)) ℝ
  C2 : ℝ
  second_volume_constant_nonneg : 0 ≤ C2
  P_homogeneous : ∀ B, (P B).IsHomogeneous (d.D + 1)
  Ps_totalDegree : ∀ B, (Ps B).totalDegree ≤ d.D + 1
  Ps_at_zero : ∀ B (lam : Weight d), evalLS d (Ps B) lam 0 = eval lam (P B)
  P_coeff : ∀ B : ℤ, 2 ≤ B → ∀ m, |coeff m (P B)| ≤ C2 * Real.log B
  Ps_coeff : ∀ B : ℤ, 2 ≤ B → ∀ m, |coeff m (Ps B)| ≤ C2 * Real.log B

  eta : Weight d
  s0 : ℝ
  one_le_localLevel : 0 < s0

  Mbar : ℤ → Weight d → ℝ → ℝ
  C3 : ℝ
  C3_nonneg : 0 ≤ C3
  agreement : ∀ (B : ℤ) (lam : Weight d) (s : ℝ), IsRatWeight d lam → IsRatReal s → ‖lam‖ ≤ 1 →
    0 < s → s ≤ s0 → IsDominant d (lam - s • eta) →
      |Mbar B lam s - evalLS d (Ps B) (lam - s • eta) s| ≤ C3 * s

  Nef : ℤ → Weight d → ℝ → Prop
  nef_of : ∀ (B : ℤ) (lam : Weight d) (s : ℝ), IsRatWeight d lam → IsRatReal s →
    sumNorm d lam ≤ d.n0 → 0 < s → s ≤ s0 → IsDominant d (lam - s • eta) →
    (∀ τ, 4 * (d.f : ℝ) * ‖lam - s • eta‖ ≤ ((B : ℝ) - 2) * gap d τ (lam - s • eta)) →
      Nef B lam s

  Comp : Type
  [compFintype : Fintype Comp]

  Pt : Comp → Type

  ZDense : (c : Comp) → Set (Pt c) → Prop
  zdense_nonempty : ∀ c S, ZDense c S → S.Nonempty

  height : ℤ → Weight d → ℝ → (c : Comp) → Pt c → ℝ

  MbarC : ℤ → Weight d → ℝ → Comp → ℝ

  MtopC : Weight d → ℝ → Comp → ℝ

  lower_of_height : ∀ (B : ℤ) (lam : Weight d) (s : ℝ) (c : Comp) (e : ℝ), Nef B lam s →
    (∀ y, e ≤ height B lam s c y) → ((d.D + 1 : ℕ) : ℝ) * e * MtopC lam s c ≤ MbarC B lam s c

  upper_of_height : ∀ (B : ℤ) (lam : Weight d) (s : ℝ) (c : Comp) (e : ℝ) (S : Set (Pt c)),
    Nef B lam s → ZDense c S → (∀ y ∈ S, height B lam s c y ≤ e) →
      MbarC B lam s c ≤ ((d.D + 1 : ℕ) : ℝ) * e * MtopC lam s c

  ta0 : ℝ → ℝ
  tauZero_pos : ∀ c0, 0 < c0 → 0 < ta0 c0
  tauZero_le : ∀ c0, 0 < c0 → ta0 c0 ≤ 1 / 2 ∧ 2 * etaConstant d eta * ta0 c0 ≤ 1 ∧
    2 * etaConstant d eta * ta0 c0 ^ 2 ≤ c0 ∧ ta0 c0 ^ 2 ≤ s0
  C4 : ℝ → ℝ
  C4_nonneg : ∀ c0, 0 ≤ C4 c0
  height_lower : ∀ (c0 : ℝ) (B : ℤ) (lam : Weight d) (ta s : ℝ), 2 ≤ B → IsRatWeight d lam →
    IsRatReal s → ‖lam‖ ≤ 1 → 0 < ta → ta ≤ ta0 c0 → (∀ τ, ta ≤ gap d τ lam) →
    (∀ (τ : Fin d.f) (a b : Fin d.N), IsCompactStep d a b → c0 ≤ lam (τ, a) - lam (τ, b)) →
    s = ta ^ 2 → ∀ c y, -(C4 c0 * Real.log (B / s)) ≤ height B lam s c y

  C5 : ℝ
  fifth_volume_constant_nonneg : 0 ≤ C5
  height_upper : ∀ (c0 : ℝ) (B : ℤ) (lam : Weight d) (ta s : ℝ), 2 ≤ B → IsRatWeight d lam →
    IsRatReal s → ‖lam‖ ≤ 1 → 0 < ta → ta ≤ ta0 c0 → (∀ τ, ta ≤ gap d τ lam) →
    (∀ (τ : Fin d.f) (a b : Fin d.N), IsCompactStep d a b → c0 ≤ lam (τ, a) - lam (τ, b)) →
    s = ta ^ 2 → ∀ c, ∃ S, ZDense c S ∧ ∀ y ∈ S, height B lam s c y ≤ C5 * Real.log B

  Mbar_sum : ∀ B lam s, Mbar B lam s = ∑ c, MbarC B lam s c

  Cl : Type
  [clGroup : AddCommGroup Cl]
  [clModule : Module ℝ Cl]

  inter : MultilinearMap ℝ (fun _ : Fin d.D => Cl) ℝ
  inter_symm : ∀ (v : Fin d.D → Cl) (σ : Equiv.Perm (Fin d.D)), inter (v ∘ σ) = inter v
  IsNef : Cl → Prop
  IsAmple : Cl → Prop
  IsEff : Cl → Prop
  nef_add : ∀ x y, IsNef x → IsNef y → IsNef (x + y)
  nef_smul : ∀ (t : ℝ) x, 0 ≤ t → IsNef x → IsNef (t • x)
  ample_nef : ∀ x, IsAmple x → IsNef x
  kleiman_nef : ∀ v : Fin d.D → Cl, (∀ i, IsNef (v i)) → 0 ≤ inter v
  kleiman_eff : ∀ (v : Fin d.D → Cl) (i0 : Fin d.D), IsEff (v i0) → (∀ i, i ≠ i0 → IsNef (v i)) →
    0 ≤ inter v

  L : Weight d → Cl

  A' : Cl

  bd : Cl
  L_nef : ∀ lam, IsDominant d lam → IsNef (L lam)
  A'_ample : IsAmple A'
  bd_eff : IsEff bd
  L_shift : ∀ (lam : Weight d) (s : ℝ), L (lam - s • eta) + s • A' = L lam - s • bd
  L_top : ∀ lam, inter (fun _ => L lam) = vol * degR d lam

  Mtop_sum : ∀ (lam : Weight d) (s : ℝ), inter (fun _ => L (lam - s • eta) + s • A') = ∑ c, MtopC lam s c

  hFl : LamPoly d
  hFl_homogeneous : hFl.IsHomogeneous (d.D + 1)
  hFl_wall : ∀ lam, IsDominant d lam → (∃ τ, gap d τ lam = 0) → eval lam hFl = 0
  hFl_nonneg : ∀ lam, IsDominant d lam → 0 ≤ eval lam hFl

  antisymmetry : ∀ (B : ℤ) (σ : Equiv.Perm (Idx d)), IsBlockSimpleSwap (Fin d.f) d.N d.j σ →
    rename σ (P B - vol • hFl) = -(P B - vol • hFl)

attribute [instance] VolumeSystem.compFintype VolumeSystem.clGroup VolumeSystem.clModule

namespace VolumeSystem

variable {d}
variable (VS : VolumeSystem d)

def lamPP (lam : Weight d) (s : ℝ) : Weight d := lam - s • VS.eta

def M (lam : Weight d) (s : ℝ) : VS.Cl := VS.L (VS.lamPP lam s) + s • VS.A'

def interPow (x : VS.Cl) : ℝ := VS.inter (fun _ => x)

def Mtop (lam : Weight d) (s : ℝ) : ℝ := VS.interPow (VS.M lam s)

def C7 : ℝ := etaConstant d VS.eta

def RB (B : ℤ) : LamPoly d := VS.P B - VS.vol • VS.hFl

def thresholdB (c0 : ℝ) : ℝ := 20 * (d.f : ℝ) * (1 + VS.C7) / (c0 * min (min (VS.ta0 c0) VS.s0) 1)

end VolumeSystem

def kaW : ℝ := 5 * (d.f : ℝ)

def taW (B : ℝ) : ℝ := kaW d / B

def wLam (τ0 : Fin d.f) (lam0 : Weight d) (ta : ℝ) : Weight d := lam0 + (2 * ta) • varpi d τ0

def n1 : ℕ := (d.n0 + 1 + (d.D + 1)).choose (d.D + 1)

def TheoremWSetting (VS : VolumeSystem d) (c0 : ℝ) (B : ℤ) (τ0 : Fin d.f) (lam0 : Weight d) : Prop :=
  IsRatReal c0 ∧ 0 < c0 ∧ c0 ≤ 1 ∧ lam0 ∈ KSet d τ0 c0 ∧ IsRatWeight d lam0 ∧ VS.thresholdB c0 ≤ B

def DegForm (c : ℚ) : Prop := 0 ≤ c ∧ degPoly d = C c * RestTerms.blockVandermonde d.f d.N

def VolumeSystem.constW {d : IndexData} (VS : VolumeSystem d) (c0 : ℝ) (c : ℚ) : ℝ :=
  ((d.D + 1 : ℕ) : ℝ) * max (3 * VS.C4 c0) VS.C5 * (VS.vol * c * 2 ^ d.D) * kaW d +
    VS.C3 * kaW d ^ 2 + (n1 d : ℝ) * VS.C2 * kaW d ^ 2 +
    (n1 d : ℝ) * ((d.D + 1 : ℕ) : ℝ) * VS.C2 * (2 * kaW d + VS.C7 * kaW d ^ 2)

def Step0Params.Statement : Prop :=
  ∀ (d : IndexData) (η lam : Weight d) (s : ℝ), 0 ≤ s →
    ‖(lam - s • η) - lam‖ ≤ etaConstant d η * s / 2 ∧
    (∀ τ, |gap d τ (lam - s • η) - gap d τ lam| ≤ etaConstant d η * s) ∧
    ∀ (τ : Fin d.f) (a b : Fin d.N), b.val = a.val + 1 →
      |((lam - s • η) (τ, a) - (lam - s • η) (τ, b)) - (lam (τ, a) - lam (τ, b))| ≤ etaConstant d η * s

def Gap1Norm.Statement : Prop :=
  ∀ (d : IndexData) (η : Weight d) (τ0 : Fin d.f) (c0 : ℝ) (lam0 : Weight d) (ta : ℝ),
    lam0 ∈ KSet d τ0 c0 → 0 ≤ ta →
      ‖wLam d τ0 lam0 ta‖ ≤ 1 / 2 + 2 * ta ∧
      (2 * ta + etaConstant d η * ta ^ 2 ≤ 1 / 2 →
        ‖wLam d τ0 lam0 ta‖ ≤ 1 ∧ ‖wLam d τ0 lam0 ta - ta ^ 2 • η‖ ≤ 1)

def Gap2Tau.Statement : Prop :=
  ∀ (d : IndexData) (τ0 : Fin d.f) (c0 : ℝ) (lam0 : Weight d) (ta : ℝ),
    lam0 ∈ KSet d τ0 c0 →
      gap d τ0 (wLam d τ0 lam0 ta) = 2 * ta ∧
      (∀ τ, τ ≠ τ0 → gap d τ (wLam d τ0 lam0 ta) = gap d τ lam0) ∧
      (∀ (τ : Fin d.f) (a b : Fin d.N), IsCompactStep d a b →
        wLam d τ0 lam0 ta (τ, a) - wLam d τ0 lam0 ta (τ, b) = lam0 (τ, a) - lam0 (τ, b)) ∧
      (0 ≤ ta → ta ≤ c0 → ∀ τ, ta ≤ gap d τ (wLam d τ0 lam0 ta))

def Gap3Dominant.Statement : Prop :=
  ∀ (d : IndexData) (η : Weight d) (τ0 : Fin d.f) (c0 : ℝ) (lam0 : Weight d) (ta : ℝ),
    lam0 ∈ KSet d τ0 c0 → 0 < c0 → 0 < ta → etaConstant d η * ta ≤ 1 → etaConstant d η * ta ^ 2 ≤ c0 / 2 →
      let mu := wLam d τ0 lam0 ta - ta ^ 2 • η
      IsDominant d mu ∧ ta ≤ gap d τ0 mu ∧ (∀ τ, τ ≠ τ0 → c0 / 2 ≤ gap d τ mu) ∧
        ∀ (τ : Fin d.f) (a b : Fin d.N), IsCompactStep d a b → c0 / 2 ≤ mu (τ, a) - mu (τ, b)

def Gap4Nef.Statement : Prop :=
  ∀ (d : IndexData) (mu : Weight d) (τ0 : Fin d.f) (c0 B : ℝ), 0 < c0 → 10 ≤ B →
    2 + 8 * (d.f : ℝ) / c0 ≤ B → 5 * (d.f : ℝ) / B ≤ gap d τ0 mu →
    (∀ τ, τ ≠ τ0 → c0 / 2 ≤ gap d τ mu) → ‖mu‖ ≤ 1 →
      ∀ τ, 4 * (d.f : ℝ) * ‖mu‖ ≤ (B - 2) * gap d τ mu

def Gap5Small.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (c0 B : ℝ), 0 < d.f → 0 < c0 → c0 ≤ 1 → VS.thresholdB c0 ≤ B →
    taW d B ≤ VS.ta0 c0 ∧ taW d B ^ 2 ≤ VS.s0

def ThresholdExists.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (c0 B : ℝ), 0 < d.f → 0 < c0 → c0 ≤ 1 → VS.thresholdB c0 ≤ B →
    let ta := taW d B
    0 < ta ∧ 2 * ta + VS.C7 * ta ^ 2 ≤ 1 / 2 ∧ ta ≤ c0 ∧ VS.C7 * ta ≤ 1 ∧ VS.C7 * ta ^ 2 ≤ c0 / 2 ∧
      10 ≤ B ∧ 2 + 8 * (d.f : ℝ) / c0 ≤ B ∧ ta ≤ VS.ta0 c0 ∧ ta ^ 2 ≤ VS.s0

def DegDifferenceNonneg.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (lam : Weight d) (s : ℝ), 0 ≤ s → IsDominant d lam →
    IsDominant d (VS.lamPP lam s) → VS.Mtop lam s ≤ VS.interPow (VS.L lam)

def MTopNonneg.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (lam : Weight d) (s : ℝ), 0 ≤ s →
    IsDominant d (VS.lamPP lam s) → 0 ≤ VS.Mtop lam s

def TopLeDeg.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (lam : Weight d) (s : ℝ), 0 ≤ s → IsDominant d lam →
    IsDominant d (VS.lamPP lam s) → VS.Mtop lam s ≤ VS.vol * degR d lam

def DegBoundByTau.Statement : Prop :=
  ∀ (d : IndexData) (c : ℚ), DegForm d c → ∀ (vol : ℝ), 0 ≤ vol →
    ∀ (lam : Weight d) (τ0 : Fin d.f) (ta : ℝ), 0 ≤ ta → ‖lam‖ ≤ 1 → gap d τ0 lam = 2 * ta →
      vol * degR d lam ≤ vol * c * 2 ^ d.D * ta

def ComponentLower.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (c0 : ℝ) (B : ℤ) (τ0 : Fin d.f) (lam0 : Weight d),
    TheoremWSetting d VS c0 B τ0 lam0 →
      let ta := taW d B
      let s := ta ^ 2
      let lam := wLam d τ0 lam0 ta
      ∀ c, ((d.D + 1 : ℕ) : ℝ) * (-(VS.C4 c0 * Real.log (B / s))) * VS.MtopC lam s c ≤
        VS.MbarC B lam s c

def ComponentUpper.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (c0 : ℝ) (B : ℤ) (τ0 : Fin d.f) (lam0 : Weight d),
    TheoremWSetting d VS c0 B τ0 lam0 →
      let ta := taW d B
      let s := ta ^ 2
      let lam := wLam d τ0 lam0 ta
      ∀ c, VS.MbarC B lam s c ≤ ((d.D + 1 : ℕ) : ℝ) * (VS.C5 * Real.log B) * VS.MtopC lam s c

def ComponentSum.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (c0 : ℝ) (B : ℤ) (τ0 : Fin d.f) (lam0 : Weight d),
    TheoremWSetting d VS c0 B τ0 lam0 →
      let ta := taW d B
      let s := ta ^ 2
      let lam := wLam d τ0 lam0 ta
      ((d.D + 1 : ℕ) : ℝ) * (-(VS.C4 c0 * Real.log (B / s))) * VS.Mtop lam s ≤ VS.Mbar B lam s ∧
        VS.Mbar B lam s ≤ ((d.D + 1 : ℕ) : ℝ) * (VS.C5 * Real.log B) * VS.Mtop lam s

def LogRatioBound.Statement : Prop :=
  ∀ (f : ℕ) (B : ℝ), 1 ≤ f → 1 ≤ B → Real.log (B / (5 * (f : ℝ) / B) ^ 2) ≤ 3 * Real.log B

def TopSqueeze.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (c0 : ℝ) (B : ℤ) (τ0 : Fin d.f) (lam0 : Weight d) (c : ℚ),
    TheoremWSetting d VS c0 B τ0 lam0 → DegForm d c →
      let ta := taW d B
      let s := ta ^ 2
      let lam := wLam d τ0 lam0 ta
      |VS.Mbar B lam s| ≤
        ((d.D + 1 : ℕ) : ℝ) * max (3 * VS.C4 c0) VS.C5 * (VS.vol * c * 2 ^ d.D) * kaW d *
          Real.log B / B

def AgreementStep.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (c0 : ℝ) (B : ℤ) (τ0 : Fin d.f) (lam0 : Weight d),
    TheoremWSetting d VS c0 B τ0 lam0 →
      let ta := taW d B
      let s := ta ^ 2
      let lam := wLam d τ0 lam0 ta
      |VS.Mbar B lam s - evalLS d (VS.Ps B) (VS.lamPP lam s) s| ≤ VS.C3 * s

def PolyShiftStep.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (B : ℤ), 2 ≤ B →
    ∀ (mu : Weight d) (s : ℝ), ‖mu‖ ≤ 1 → 0 ≤ s → s ≤ 1 →
      |evalLS d (VS.Ps B) mu s - eval mu (VS.P B)| ≤ (n1 d : ℝ) * VS.C2 * s * Real.log B

def MeanValueStep.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (B : ℤ), 2 ≤ B →
    ∀ a b : Weight d, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      |eval a (VS.P B) - eval b (VS.P B)| ≤
        (n1 d : ℝ) * ((d.D + 1 : ℕ) : ℝ) * VS.C2 * Real.log B * ‖a - b‖

def SumStep.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (c0 : ℝ) (B : ℤ) (τ0 : Fin d.f) (lam0 : Weight d) (c : ℚ),
    TheoremWSetting d VS c0 B τ0 lam0 → DegForm d c →
      |eval lam0 (VS.P B)| ≤ VS.constW c0 c * Real.log B / B

def TheoremW.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (c0 : ℚ), 0 < c0 → c0 ≤ 1 →
    ∃ CW B1 : ℝ, ∀ B : ℤ, B1 ≤ B → ∀ (τ0 : Fin d.f), ∀ lam0 ∈ KSet d τ0 c0,
      |eval lam0 (VS.P B)| ≤ CW * Real.log B / B

def IsComplementInV (V' : Submodule ℝ (LamPoly d)) : Prop :=
  V' ≤ vSpace d ∧ Disjoint (uSpace d) V' ∧ uSpace d ⊔ V' = vSpace d

def alBeForm (al be : Fin d.f → ℝ) : LamPoly d :=
  ∑ τ : Fin d.f, (C (al τ) * lowerSum d τ + C (be τ) * upperSum d τ)

def VolumeSystem.EB {d : IndexData} (VS : VolumeSystem d) (B : ℤ) (al be : Fin d.f → ℝ) : LamPoly d :=
  VS.P B - VS.vol • (VS.hFl + ((d.D + 1 : ℕ) : ℝ) • (degPolyR d * alBeForm d al be))

def RBInV.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (B : ℤ), VS.RB B ∈ vSpace d

def RBOnK.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d), ∃ CW B1 : ℝ, ∀ B : ℤ, B1 ≤ B →
    ∀ (τ : Fin d.f), ∀ lam ∈ KSet d τ (quarterInverseN d),
      eval lam VS.hFl = 0 ∧ |eval lam (VS.RB B)| ≤ CW * Real.log B / B

def RBOnTranslates.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (B : ℤ), ∀ σ ∈ weylL d, ∀ lam : Weight d,
    |eval (permAct d σ lam) (VS.RB B)| = |eval lam (VS.RB B)|

def RBSup.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d), ∃ CW B1 : ℝ,
    ∀ Om : Fin d.f → Fin d.N → Fin d.N → Set (Weight d),
      (∀ (τ : Fin d.f) (a b : Fin d.N), IsCross d a b →
        ∃ σ ∈ weylL d, Om τ a b = permAct d σ '' KSet d τ (quarterInverseN d)) →
      ∀ B : ℤ, B1 ≤ B → supOn d (wallUnion d Om) (VS.RB B) ≤ CW * Real.log B / B

def RBDecomposition.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (V' : Submodule ℝ (LamPoly d)), IsComplementInV d V' →
    ∃ C B1 : ℝ, ∀ B : ℤ, B1 ≤ B → ∃ l ∈ invForms d, ∃ E ∈ V',
      VS.RB B = antisymDelta (Fin d.f) d.N * l + E ∧ ∀ m, |coeff m E| ≤ C * Real.log B / B

def DefineAlBe.Statement : Prop :=
  ∀ (d : IndexData) (k : ℝ), k ≠ 0 → ∀ l ∈ invForms d,
    ∃! ab : (Fin d.f → ℝ) × (Fin d.f → ℝ), l = C k * alBeForm d ab.1 ab.2

set_option linter.dupNamespace false in

def TheoremB.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (V' : Submodule ℝ (LamPoly d)), IsComplementInV d V' →
    ∃ CB B1 : ℝ, ∀ B : ℤ, B1 ≤ B → ∃ al be : Fin d.f → ℝ,
      VS.EB B al be ∈ V' ∧ (∀ m, |coeff m (VS.EB B al be)| ≤ CB * Real.log B / B) ∧
        ∀ al' be' : Fin d.f → ℝ, VS.EB B al' be' ∈ V' → al' = al ∧ be' = be

def ComplementChange.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (V' V'' : Submodule ℝ (LamPoly d)),
    IsComplementInV d V' → IsComplementInV d V'' →
    ∃ C B1 : ℝ, ∀ B : ℤ, B1 ≤ B → ∀ al be al'' be'' : Fin d.f → ℝ,
      VS.EB B al be ∈ V' → VS.EB B al'' be'' ∈ V'' →
        ∀ τ, |al τ - al'' τ| ≤ C * Real.log B / B ∧ |be τ - be'' τ| ≤ C * Real.log B / B

def AlBeBound.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (V' : Submodule ℝ (LamPoly d)), IsComplementInV d V' →
    ∃ C B1 : ℝ, ∀ B : ℤ, B1 ≤ B → ∀ al be : Fin d.f → ℝ, VS.EB B al be ∈ V' →
      ∀ τ, |al τ| ≤ C * Real.log B ∧ |be τ| ≤ C * Real.log B

def intFlR : LamPoly d →ₗ[ℝ] ℝ :=
  (flagNormalisation d.f d.N : ℝ) • RestTerms.flagIntegralReal d.f d.N

def shiftFlR (τ : Fin d.f) (F : LamPoly d) : ℝ :=
  intFlR d (∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), pderiv (τ, i) F)

def upperFlR (τ : Fin d.f) (F : LamPoly d) : ℝ :=
  intFlR d (∑ i ∈ univ.filter (fun i : Fin d.N => d.j ≤ i.val), pderiv (τ, i) F)

def totalFlR (τ : Fin d.f) (F : LamPoly d) : ℝ :=
  intFlR d (∑ i : Fin d.N, pderiv (τ, i) F)

def corrFl (al be : Fin d.f → ℝ) (F : LamPoly d) : ℝ :=
  ∑ τ : Fin d.f, (al τ * shiftFlR d τ F + be τ * upperFlR d τ F)

def polarFunctional {σ : Type*} (n : ℕ) (P : MvPolynomial σ ℝ) : MvPolynomial σ ℝ →ₗ[ℝ] ℝ :=
  ∑ m ∈ P.support.filter (fun m => (m.sum fun _ e => e) = n),
    ((-1) ^ n * ((m.prod fun _ e => (e.factorial : ℝ)) / (n.factorial : ℝ)) * coeff m P) •
      lcoeff ℝ m

def VolumeSystem.PP {d : IndexData} (VS : VolumeSystem d) (B : ℤ) : LamPoly d →ₗ[ℝ] ℝ :=
  polarFunctional (d.D + 1) (VS.P B)

def VolumeSystem.hh {d : IndexData} (VS : VolumeSystem d) : LamPoly d →ₗ[ℝ] ℝ :=
  polarFunctional (d.D + 1) VS.hFl

def VolumeSystem.ee {d : IndexData} (VS : VolumeSystem d) (B : ℤ) (al be : Fin d.f → ℝ)
    (F : LamPoly d) : ℝ :=
  VS.PP B F - VS.vol * (VS.hh F - corrFl d al be F)

def powR (k : ℕ) (τ : Fin d.f) : LamPoly d := ∑ i : Fin d.N, X (τ, i) ^ k

def lowPowR (k : ℕ) (τ : Fin d.f) : LamPoly d :=
  ∑ i ∈ univ.filter (fun i : Fin d.N => i.val < d.j), X (τ, i) ^ k

def CorollaryBPrime.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (V' : Submodule ℝ (LamPoly d)), IsComplementInV d V' →
    ∃ CB B1 : ℝ, ∀ B : ℤ, B1 ≤ B → ∃ al be : Fin d.f → ℝ, VS.EB B al be ∈ V' ∧
      ∃ EE : LamPoly d →ₗ[ℝ] ℝ,
        (∀ F : LamPoly d, F.IsHomogeneous (d.D + 1) →
          VS.PP B F = VS.vol * (VS.hh F - corrFl d al be F) + EE F) ∧
        ∀ m : Idx d →₀ ℕ, (m.sum fun _ e => e) = d.D + 1 →
          |EE (monomial m 1)| ≤ CB * Real.log B / B

def CorollaryBPrimeMonomial.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (B : ℤ) (al be : Fin d.f → ℝ) (m : Idx d →₀ ℕ),
    (m.sum fun _ e => e) = d.D + 1 →
      VS.ee B al be (monomial m 1) =
        (-1) ^ (d.D + 1) * ((m.prod fun _ e => (e.factorial : ℝ)) / ((d.D + 1).factorial : ℝ)) *
          coeff m (VS.EB B al be)

def CorollaryBPrimeRow.Statement : Prop :=
  ∀ (d : IndexData) (al be : Fin d.f → ℝ) (F : LamPoly d),
    corrFl d al be F = ∑ τ : Fin d.f, ((al τ - be τ) * shiftFlR d τ F + be τ * totalFlR d τ F)

def CorollaryBSecondOne.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (B : ℤ) (al be : Fin d.f → ℝ) (τ : Fin d.f)
    (Q : LamPoly d), Q.IsHomogeneous d.D →
      VS.PP B (powR d 1 τ * Q) =
        VS.vol * VS.hh (powR d 1 τ * Q) -
          VS.vol * ((d.j : ℝ) * al τ + ((d.N : ℝ) - d.j) * be τ) * intFlR d Q +
          VS.ee B al be (powR d 1 τ * Q)

def CorollaryBSecondTwo.Statement : Prop :=
  ∀ (d : IndexData) (VS : VolumeSystem d) (B : ℤ) (al be : Fin d.f → ℝ) (τ : Fin d.f)
    (Q' : LamPoly d), Q'.IsHomogeneous (d.D - 1) →
      VS.PP B (powR d 2 τ * Q') =
        VS.vol * VS.hh (powR d 2 τ * Q') -
          2 * VS.vol * (al τ - be τ) * intFlR d (lowPowR d 1 τ * Q') +
          VS.ee B al be (powR d 2 τ * Q')

abbrev p0 : Idx d1 := (0, ⟨0, by norm_num⟩)

abbrev p1 : Idx d1 := (0, ⟨1, by norm_num⟩)

theorem polarPoly_coeff_eq {σ R : Type*} [CommRing R] [Fintype σ] (Φ : MvPolynomial σ R →ₗ[R] R)
    (n : ℕ) (m : σ →₀ ℕ) : coeff m (polarPoly Φ n) = Φ (coeff m ((-outerDot σ R) ^ n)) := by
  classical
  rw [polarPoly, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

theorem polarPoly_one {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]
    (Φ : MvPolynomial σ R →ₗ[R] R) : polarPoly Φ 1 = ∑ v : σ, C (Φ (-X v)) * X v := by
  ext m
  rw [polarPoly_coeff_eq, pow_one, coeff_sum]
  have hc : ∀ v : σ, (X v * C (X v) : MvPolynomial σ (MvPolynomial σ R)) = C (X v) * X v :=
    fun v => mul_comm _ _
  simp only [outerDot, hc, coeff_neg, coeff_sum, coeff_C_mul, coeff_X]
  rw [map_neg, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs <;> simp

theorem flagIntegral_X (f N : ℕ) (v : Fin f × Fin N) :
    RestTerms.flagIntegral f N (X v) = coeff (Finsupp.single v 1) (RestTerms.blockVandermonde f N) := by
  classical
  unfold RestTerms.flagIntegral
  rw [Finset.sum_eq_single (Finsupp.single v 1)]
  · simp [coeff_X, Finsupp.prod_single_index]
  · intro b _ hb
    rw [coeff_X, if_neg (Ne.symm hb), zero_mul, zero_mul]
  · intro h
    rw [notMem_support_iff.1 h]
    simp

theorem blockVandermonde_rankTwo :
    RestTerms.blockVandermonde d1.f d1.N = (X p0 - X p1 : XPoly d1) := by
  have h0 : Finset.Ioi (0 : Fin 2) = {1} := by decide
  have h1 : Finset.Ioi (1 : Fin 2) = ∅ := by decide
  simp [RestTerms.blockVandermonde, RestTerms.vandermondeOf, Fin.prod_univ_two, h0, h1]
  rfl

theorem flagNormalisation_rankTwo : flagNormalisation d1.f d1.N = -1 := by
  have h : ∏ i : Fin 2, ((i : ℕ).factorial : ℚ) = 1 := by simp [Fin.prod_univ_two]
  have hD : RestTerms.topDegree 1 2 = 1 := rfl
  show (-1) ^ RestTerms.topDegree 1 2 / (∏ i : Fin 2, ((i : ℕ).factorial : ℚ)) ^ 1 = -1
  rw [h, hD]
  norm_num

theorem intFl_X_of_two_variables (v : Idx d1) :
    intFl d1 (X v) = -coeff (Finsupp.single v 1) (X p0 - X p1 : XPoly d1) := by
  rw [intFl, LinearMap.smul_apply, flagNormalisation_rankTwo]
  show (-1 : ℚ) • RestTerms.flagIntegral d1.f d1.N (X v) = _
  rw [flagIntegral_X, blockVandermonde_rankTwo]
  simp

theorem degPoly_eq_sub_of_two_variables : degPoly d1 = (X p0 - X p1 : XPoly d1) := by
  have hD : d1.D = 1 := rfl
  rw [degPoly, hD, polarPoly_one]
  simp only [map_neg, intFl_X_of_two_variables, neg_neg, Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two]
  have hne : p1 ≠ p0 := by decide
  have e00 : coeff (Finsupp.single p0 1) (X p0 - X p1 : XPoly d1) = 1 := by
    simp [coeff_X, Finsupp.single_left_inj one_ne_zero, hne]
  have e01 : coeff (Finsupp.single p1 1) (X p0 - X p1 : XPoly d1) = -1 := by
    simp [coeff_X, Finsupp.single_left_inj one_ne_zero, hne.symm]
  have q0 : ((0 : Fin 1), (0 : Fin 2)) = p0 := rfl
  have q1 : ((0 : Fin 1), (1 : Fin 2)) = p1 := rfl
  rw [q0, q1, e00, e01]
  simp [sub_eq_add_neg]

theorem degForm_of_two_variables : DegForm d1 1 := by
  refine ⟨zero_le_one, ?_⟩
  rw [degPoly_eq_sub_of_two_variables, blockVandermonde_rankTwo, map_one, one_mul]

theorem degR_eq_sub_of_two_variables (lam : Weight d1) : degR d1 lam = lam p0 - lam p1 := by
  simp [degR, degPolyR, degPoly_eq_sub_of_two_variables]

theorem gap_eq_sub_of_two_variables (τ : Fin d1.f) (lam : Weight d1) : gap d1 τ lam = lam p0 - lam p1 := by
  have : τ = 0 := Subsingleton.elim _ _
  subst this
  rfl

theorem dominant_gap_nonneg_two_variables {lam : Weight d1} (h : IsDominant d1 lam) : 0 ≤ lam p0 - lam p1 :=
  h 0 ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ rfl

theorem lowerSum_rankTwo : lowerSum d1 0 = (X p0 : LamPoly d1) := by
  have h : (univ.filter fun i : Fin d1.N => i.val < d1.j) = {⟨0, by norm_num⟩} := by decide
  rw [lowerSum, h, Finset.sum_singleton]

theorem upperSum_rankTwo : upperSum d1 0 = (X p1 : LamPoly d1) := by
  have h : (univ.filter fun i : Fin d1.N => d1.j ≤ i.val) = {⟨1, by norm_num⟩} := by decide
  rw [upperSum, h, Finset.sum_singleton]

def sampleForm : LamPoly d1 := lowerSum d1 0 - upperSum d1 0

theorem sampleForm_mem : sampleForm ∈ invForms d1 :=
  Submodule.sub_mem _ (Submodule.subset_span (Or.inl ⟨0, rfl⟩))
    (Submodule.subset_span (Or.inr ⟨0, rfl⟩))

def sqPoly : LamPoly d1 := antisymDelta (Fin d1.f) d1.N * sampleForm

theorem sqPoly_eq : sqPoly = (X p0 - X p1 : LamPoly d1) ^ 2 := by
  rw [sqPoly, sampleForm, antisymDelta_rankTwo, lowerSum_rankTwo, upperSum_rankTwo, sq]
  rfl

theorem eval_sqPoly (lam : Weight d1) : eval lam sqPoly = (lam p0 - lam p1) ^ 2 := by
  rw [sqPoly_eq]; simp

theorem sqPoly_homogeneous : sqPoly.IsHomogeneous (d1.D + 1) := by
  rw [sqPoly_eq]
  exact ((isHomogeneous_X ℝ p0).sub (isHomogeneous_X ℝ p1)).pow 2

theorem sqPoly_ne_zero : sqPoly ≠ 0 := by
  intro h
  have := congrArg (eval (fun p => if p = p0 then (1 : ℝ) else 0)) h
  rw [eval_sqPoly] at this
  simp at this

def samplePoly (k : ℝ) : LamPoly d1 := C k * sqPoly

def samplePolyS (k : ℝ) : MvPolynomial (Option (Idx d1)) ℝ := rename some (samplePoly k)

def sampleBound (k : ℝ) : ℝ :=
  max (Classical.choose (exists_coeff_bound (samplePoly k)))
    (Classical.choose (exists_coeff_bound (samplePolyS k)))

theorem sampleBound_spec (k : ℝ) : (∀ m, |coeff m (samplePoly k)| ≤ sampleBound k) ∧
    (∀ m, |coeff m (samplePolyS k)| ≤ sampleBound k) ∧ 0 ≤ sampleBound k := by
  have h1 := Classical.choose_spec (exists_coeff_bound (samplePoly k))
  have h2 := Classical.choose_spec (exists_coeff_bound (samplePolyS k))
  refine ⟨fun m => (h1 m).trans (le_max_left _ _), fun m => (h2 m).trans (le_max_right _ _), ?_⟩
  exact (abs_nonneg _).trans ((h1 0).trans (le_max_left _ _))

theorem le_div_log_mul (M : ℝ) (hM : 0 ≤ M) (B : ℤ) (hB : 2 ≤ B) :
    M ≤ M / Real.log 2 * Real.log B := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hl : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hB'
  calc M = M / Real.log 2 * Real.log 2 := by field_simp
    _ ≤ M / Real.log 2 * Real.log B := mul_le_mul_of_nonneg_left hl (div_nonneg hM h2.le)

theorem eval_samplePoly (k : ℝ) (lam : Weight d1) :
    eval lam (samplePoly k) = k * (lam p0 - lam p1) ^ 2 := by
  rw [samplePoly, eval_mul, eval_C, eval_sqPoly]

theorem evalLS_samplePolyS (k : ℝ) (lam : Weight d1) (s : ℝ) :
    evalLS d1 (samplePolyS k) lam s = eval lam (samplePoly k) := by
  rw [evalLS, samplePolyS, eval_rename]
  rfl

theorem abs_sub_le_two (lam : Weight d1) (h : ‖lam‖ ≤ 1) : lam p0 - lam p1 ≤ 2 := by
  have a0 : |lam p0| ≤ 1 := (by simpa using norm_le_pi_norm lam p0 : ‖lam p0‖ ≤ ‖lam‖).trans h |>.trans_eq' (Real.norm_eq_abs _).symm
  have a1 : |lam p1| ≤ 1 := (by simpa using norm_le_pi_norm lam p1 : ‖lam p1‖ ≤ ‖lam‖).trans h |>.trans_eq' (Real.norm_eq_abs _).symm
  have := abs_le.1 a0
  have := abs_le.1 a1
  linarith

def sampleSystem (k : ℝ) (hk : 0 ≤ k) : VolumeSystem d1 where
  vol := 1
  vol_pos := one_pos
  P := fun _ => samplePoly k
  Ps := fun _ => samplePolyS k
  C2 := sampleBound k / Real.log 2
  second_volume_constant_nonneg := div_nonneg (sampleBound_spec k).2.2 (Real.log_pos (by norm_num)).le
  P_homogeneous := fun _ => sqPoly_homogeneous.C_mul k
  Ps_totalDegree := fun _ => (totalDegree_rename_le _ _).trans
    ((sqPoly_homogeneous.C_mul k).totalDegree_le)
  Ps_at_zero := fun _ lam => evalLS_samplePolyS k lam 0
  P_coeff := fun B hB m => ((sampleBound_spec k).1 m).trans
    (le_div_log_mul _ (sampleBound_spec k).2.2 B hB)
  Ps_coeff := fun B hB m => ((sampleBound_spec k).2.1 m).trans
    (le_div_log_mul _ (sampleBound_spec k).2.2 B hB)
  eta := 0
  s0 := 1
  one_le_localLevel := one_pos
  Mbar := fun _ lam _ => eval lam (samplePoly k)
  C3 := 0
  C3_nonneg := le_rfl
  agreement := by
    intro B lam s _ _ _ _ _ _
    rw [smul_zero, sub_zero, evalLS_samplePolyS, sub_self, abs_zero, zero_mul]
  Nef := fun _ lam s => IsDominant d1 (lam - s • (0 : Weight d1))
  nef_of := fun _ _ _ _ _ _ _ _ h _ => h
  Comp := Unit
  Pt := fun _ => Unit
  ZDense := fun _ S => S.Nonempty
  zdense_nonempty := fun _ _ h => h
  height := fun _ lam _ _ _ => k * (lam p0 - lam p1) / 2
  MbarC := fun _ lam _ _ => eval lam (samplePoly k)
  MtopC := fun lam _ _ => lam p0 - lam p1
  lower_of_height := by
    intro B lam s c e hN he
    have hg : 0 ≤ lam p0 - lam p1 := by simpa using dominant_gap_nonneg_two_variables hN
    have h1 := he ()
    rw [eval_samplePoly]
    have : ((d1.D + 1 : ℕ) : ℝ) = 2 := by norm_num [rankTwo_D]
    rw [this]
    nlinarith
  upper_of_height := by
    intro B lam s c e S hN hS hle
    have hg : 0 ≤ lam p0 - lam p1 := by simpa using dominant_gap_nonneg_two_variables hN
    obtain ⟨y, hy⟩ := hS
    have h1 := hle y hy
    rw [eval_samplePoly]
    have : ((d1.D + 1 : ℕ) : ℝ) = 2 := by norm_num [rankTwo_D]
    rw [this]
    nlinarith
  ta0 := fun _ => 1 / 2
  tauZero_pos := fun _ _ => by norm_num
  tauZero_le := fun c0 hc0 => by
    refine ⟨le_rfl, ?_, ?_, ?_⟩ <;> simp [etaConstant] <;> linarith
  C4 := fun _ => 0
  C4_nonneg := fun _ => le_rfl
  height_lower := by
    intro c0 B lam ta s _ _ _ _ hta _ hgap _ _ c y
    have hg : ta ≤ lam p0 - lam p1 := by simpa [gap_eq_sub_of_two_variables] using hgap 0
    simp only [zero_mul, neg_zero]
    have : 0 ≤ k * (lam p0 - lam p1) := mul_nonneg hk (by linarith)
    linarith
  C5 := k / Real.log 2
  fifth_volume_constant_nonneg := div_nonneg hk (Real.log_pos (by norm_num)).le
  height_upper := by
    intro c0 B lam ta s hB _ _ hn hta _ hgap _ _ c
    refine ⟨Set.univ, ⟨(), trivial⟩, fun y _ => ?_⟩
    have hg : ta ≤ lam p0 - lam p1 := by simpa [gap_eq_sub_of_two_variables] using hgap 0
    have h2 := abs_sub_le_two lam hn
    have hk2 : k * (lam p0 - lam p1) / 2 ≤ k := by nlinarith
    exact hk2.trans (le_div_log_mul k hk B hB)
  Mbar_sum := fun _ _ _ => by simp
  Cl := ℝ
  inter := MultilinearMap.mkPiAlgebra ℝ (Fin d1.D) ℝ
  inter_symm := fun v σ => by
    simp only [MultilinearMap.mkPiAlgebra_apply, Function.comp_apply]
    exact Equiv.prod_comp σ v
  IsNef := fun x => 0 ≤ x
  IsAmple := fun x => 0 ≤ x
  IsEff := fun x => 0 ≤ x
  nef_add := fun _ _ hx hy => add_nonneg hx hy
  nef_smul := fun t x ht hx => by simpa using mul_nonneg ht hx
  ample_nef := fun _ h => h
  kleiman_nef := fun v hv => by
    rw [MultilinearMap.mkPiAlgebra_apply]
    exact Finset.prod_nonneg (fun i _ => hv i)
  kleiman_eff := fun v i0 h0 hv => by
    rw [MultilinearMap.mkPiAlgebra_apply]
    refine Finset.prod_nonneg (fun i _ => ?_)
    by_cases hi : i = i0
    · subst hi; exact h0
    · exact hv i hi
  L := fun lam => degR d1 lam
  A' := 0
  bd := 0
  L_nef := fun lam h => by
    show 0 ≤ degR d1 lam
    rw [degR_eq_sub_of_two_variables]; exact dominant_gap_nonneg_two_variables h
  A'_ample := le_rfl
  bd_eff := le_rfl
  L_shift := fun lam s => by simp
  L_top := fun lam => by
    rw [MultilinearMap.mkPiAlgebra_apply, Fin.prod_const, rankTwo_D, pow_one, one_mul]
  Mtop_sum := fun lam s => by
    rw [MultilinearMap.mkPiAlgebra_apply, Fin.prod_const, rankTwo_D, pow_one]
    simp [degR_eq_sub_of_two_variables]
  hFl := sqPoly
  hFl_homogeneous := sqPoly_homogeneous
  hFl_wall := by
    rintro lam - ⟨τ, hτ⟩
    rw [gap_eq_sub_of_two_variables] at hτ
    rw [eval_sqPoly, hτ]; ring
  hFl_nonneg := fun lam _ => by rw [eval_sqPoly]; positivity
  antisymmetry := by
    rintro B σ ⟨τ, a, b, hab, hblk, -⟩
    exfalso
    have ha : a.val < 2 := a.isLt
    have hb : b.val < 2 := b.isLt
    have hblk' : b.val < 1 ∨ 1 ≤ a.val := hblk
    omega

theorem sampleSystem_zero (B : ℤ) : (sampleSystem 0 le_rfl).P B = 0 := by
  show C 0 * sqPoly = 0
  rw [C_0, zero_mul]

theorem sampleSystem_two (B : ℤ) :
    let VS := sampleSystem 2 (by norm_num)
    VS.P B = C 2 * (antisymDelta (Fin d1.f) d1.N * sampleForm) ∧
      VS.hFl = antisymDelta (Fin d1.f) d1.N * sampleForm ∧
      sampleForm ∈ invForms d1 ∧ sampleForm ≠ 0 ∧ VS.P B ≠ 0 ∧ VS.RB B ≠ 0 := by
  intro VS
  have hform : sampleForm ≠ 0 := by
    intro h
    have := congrArg (eval (fun p => if p = p0 then (1 : ℝ) else 0)) h
    simp [sampleForm, lowerSum_rankTwo, upperSum_rankTwo] at this
  have hRB : VS.RB B = sqPoly := by
    show C 2 * sqPoly - (1 : ℝ) • sqPoly = sqPoly
    rw [one_smul, C_mul', two_smul, add_sub_cancel_right]
  refine ⟨rfl, rfl, sampleForm_mem, hform, ?_, ?_⟩
  · show C 2 * sqPoly ≠ 0
    exact mul_ne_zero (by simp) sqPoly_ne_zero
  · rw [hRB]; exact sqPoly_ne_zero

theorem zero_mem_KSet_rankTwo_any (c0 : ℝ) : (0 : Weight d1) ∈ KSet d1 0 c0 := by
  refine ⟨by rw [norm_zero]; norm_num, by simp [gap], ?_, ?_⟩
  · intro τ hτ
    exact absurd (Subsingleton.elim τ 0) hτ
  · rintro τ a b ⟨hab, hbj⟩
    exfalso
    have hb : b.val < 2 := b.isLt
    have hbj' : b.val ≠ 1 := hbj
    omega

theorem isRatWeight_zero : IsRatWeight d (0 : Weight d) := fun _ => ⟨0, by simp⟩

theorem sampleSystem_two_B1W : (sampleSystem 2 (by norm_num)).thresholdB 1 = 40 := by
  simp only [VolumeSystem.thresholdB, VolumeSystem.C7, etaConstant]
  show 20 * ((1 : ℕ) : ℝ) * (1 + 2 * ‖(0 : Weight d1)‖) / (1 * min (min (1 / 2) 1) 1) = 40
  rw [norm_zero]
  norm_num

theorem TheoremWSetting.inhabited : TheoremWSetting d1 (sampleSystem 2 (by norm_num)) 1 40 0 0 :=
  ⟨⟨1, by norm_num⟩, one_pos, le_rfl, zero_mem_KSet_rankTwo_any 1, isRatWeight_zero d1,
    by rw [sampleSystem_two_B1W]; norm_num⟩

theorem Gap1Norm.hypotheses_inhabited :
    (0 : Weight d1) ∈ KSet d1 0 1 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 / 10 ∧
      2 * (1 / 10 : ℝ) + etaConstant d1 0 * (1 / 10) ^ 2 ≤ 1 / 2 ∧
      etaConstant d1 0 * (1 / 10 : ℝ) ≤ 1 ∧ etaConstant d1 0 * (1 / 10 : ℝ) ^ 2 ≤ 1 / 2 := by
  refine ⟨zero_mem_KSet_rankTwo_any 1, one_pos, by norm_num, ?_, ?_, ?_⟩ <;> norm_num [etaConstant]

def halfWeight : Weight d1 := fun p => if p = p0 then 1 / 2 else -1 / 2

theorem Gap4Nef.hypotheses_inhabited :
    (0 : ℝ) < 1 ∧ (10 : ℝ) ≤ 10 ∧ 2 + 8 * (d1.f : ℝ) / 1 ≤ 10 ∧
      5 * (d1.f : ℝ) / 10 ≤ gap d1 0 halfWeight ∧
      (∀ τ, τ ≠ 0 → (1 : ℝ) / 2 ≤ gap d1 τ halfWeight) ∧ ‖halfWeight‖ ≤ 1 := by
  have hne : p1 ≠ p0 := by decide
  refine ⟨one_pos, le_rfl, by norm_num, ?_, fun τ hτ => absurd (Subsingleton.elim τ 0) hτ, ?_⟩
  · rw [gap_eq_sub_of_two_variables]; simp [halfWeight, hne]; norm_num
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun p => ?_)
    unfold halfWeight
    split_ifs <;> norm_num

theorem ThresholdExists.hypotheses_inhabited :
    0 < d1.f ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ (sampleSystem 2 (by norm_num)).thresholdB 1 ≤ 40 := by
  refine ⟨by norm_num, one_pos, le_rfl, ?_⟩
  rw [sampleSystem_two_B1W]

theorem DegDifferenceNonneg.hypotheses_inhabited :
    (0 : ℝ) ≤ 0 ∧ IsDominant d1 (0 : Weight d1) ∧
      IsDominant d1 ((sampleSystem 2 (by norm_num)).lamPP 0 0) := by
  refine ⟨le_rfl, fun _ _ _ _ => by simp, fun _ _ _ _ => ?_⟩
  simp [VolumeSystem.lamPP]

theorem DegBoundByTau.hypotheses_inhabited :
    DegForm d1 1 ∧ (0 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 1 / 4 ∧ ‖(1 / 2 : ℝ) • halfWeight‖ ≤ 1 ∧
      gap d1 0 ((1 / 2 : ℝ) • halfWeight) = 2 * (1 / 4) := by
  have hne : p1 ≠ p0 := by decide
  refine ⟨degForm_of_two_variables, zero_le_one, by norm_num, ?_, ?_⟩
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun p => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, halfWeight]
    split_ifs <;> norm_num
  · rw [gap_eq_sub_of_two_variables]; simp [halfWeight, hne]; norm_num

theorem LogRatioBound.hypotheses_inhabited : 1 ≤ (1 : ℕ) ∧ (1 : ℝ) ≤ 1 := ⟨le_rfl, le_rfl⟩

theorem PolyShiftStep.hypotheses_inhabited :
    (2 : ℤ) ≤ 2 ∧ ‖(0 : Weight d1)‖ ≤ 1 ∧ (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := by
  refine ⟨le_rfl, by rw [norm_zero]; exact zero_le_one, le_rfl, zero_le_one⟩

theorem TopSqueeze.hypotheses_inhabited :
    TheoremWSetting d1 (sampleSystem 2 (by norm_num)) 1 40 0 0 ∧ DegForm d1 1 :=
  ⟨TheoremWSetting.inhabited, degForm_of_two_variables⟩

theorem TheoremW.hypotheses_inhabited : (0 : ℚ) < 1 ∧ (1 : ℚ) ≤ 1 := ⟨one_pos, le_rfl⟩

theorem IsComplementInV.inhabited : ∃ V' : Submodule ℝ (LamPoly d1), IsComplementInV d1 V' :=
  exists_complement_of_le uSpace_le_vSpace_rankTwo

theorem RBSup.hypotheses_inhabited :
    (1 : Equiv.Perm (Idx d1)) ∈ weylL d1 ∧
      ∀ (τ : Fin d1.f) (a b : Fin d1.N), IsCross d1 a b →
        ∃ σ ∈ weylL d1, (fun τ (_ _ : Fin d1.N) => KSet d1 τ (quarterInverseN d1)) τ a b =
          permAct d1 σ '' KSet d1 τ (quarterInverseN d1) := by
  have h1 : permAct d1 (1 : Equiv.Perm (Idx d1)) = id := by
    funext lam p; rfl
  refine ⟨Subgroup.one_mem _, fun τ a b _ => ⟨1, Subgroup.one_mem _, ?_⟩⟩
  rw [h1, Set.image_id]

theorem DefineAlBe.hypotheses_inhabited : (1 : ℝ) ≠ 0 ∧ sampleForm ∈ invForms d1 :=
  ⟨one_ne_zero, sampleForm_mem⟩

theorem CorollaryBPrimeMonomial.hypotheses_inhabited :
    ((Finsupp.single p0 2 : Idx d1 →₀ ℕ).sum fun _ e => e) = d1.D + 1 := by
  rw [Finsupp.sum_single_index rfl]
  rfl

theorem CorollaryBSecond.hypotheses_inhabited :
    (X p0 : LamPoly d1).IsHomogeneous d1.D ∧ (1 : LamPoly d1).IsHomogeneous (d1.D - 1) := by
  refine ⟨?_, ?_⟩
  · rw [rankTwo_D]; exact isHomogeneous_X ℝ p0
  · rw [rankTwo_D]; exact isHomogeneous_one _ _

end GroundTheory.Heights₂.Heights.TheoremB
