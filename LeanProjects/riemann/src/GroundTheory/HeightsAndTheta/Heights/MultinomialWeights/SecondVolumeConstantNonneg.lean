import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.TheoremB

open MvPolynomial GroundTheory.Heights₂.Heights

section Objects

variable {T : Type*} [Fintype T] [DecidableEq T] {N : ℕ}

def entry (lam : T × Fin N → ℝ) (τ : T) (i : ℕ) : ℝ :=
  if h : i < N then lam (τ, ⟨i, h⟩) else 0

def gapAtIndex (lam : T × Fin N → ℝ) (τ : T) (i : ℕ) : ℝ :=
  entry lam τ i - entry lam τ (i + 1)

def ncGap (j : ℕ) (lam : T × Fin N → ℝ) (τ : T) : ℝ :=
  gapAtIndex lam τ (j - 1)

def IsDominantWeight (lam : T × Fin N → ℝ) : Prop :=
  ∀ τ i, i + 1 < N → 0 ≤ gapAtIndex lam τ i

def IsRegularWeight (lam : T × Fin N → ℝ) : Prop :=
  ∀ τ i, i + 1 < N → 0 < gapAtIndex lam τ i

def varpiTau (j : ℕ) (τ : T) : T × Fin N → ℝ :=
  fun p => if p.1 = τ ∧ p.2.val < j then 1 else 0

def Kset (j : ℕ) (τ₀ : T) (c₀ : ℝ) : Set (T × Fin N → ℝ) :=
  {lam | ‖lam‖ ≤ 1 / 2 ∧ ncGap j lam τ₀ = 0 ∧ (∀ τ, τ ≠ τ₀ → c₀ ≤ ncGap j lam τ) ∧
    ∀ τ i, i + 1 < N → i + 1 ≠ j → c₀ ≤ gapAtIndex lam τ i}

def IsRatVec (lam : T × Fin N → ℝ) : Prop := ∀ p, ∃ q : ℚ, lam p = q

def IsRatNum (s : ℝ) : Prop := ∃ q : ℚ, s = q

def sumNorm (lam : T × Fin N → ℝ) : ℝ := ∑ p, |lam p|

def linForm (lam : T × Fin N → ℝ) : MvPolynomial (T × Fin N) ℝ :=
  -∑ p, lam p • X p

def evalS (lam : T × Fin N → ℝ) (s : ℝ) (Q : MvPolynomial (Option (T × Fin N)) ℝ) : ℝ :=
  eval (fun o => o.elim s lam) Q

variable (T N)

def fullAct (w : T → Equiv.Perm (Fin N)) (p : T × Fin N) : T × Fin N := (p.1, w p.1 p.2)

def fullSign (w : T → Equiv.Perm (Fin N)) : ℝ := ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ)

def basePoint : T × Fin N → ℝ := fun p => -(p.2.val : ℝ)

def flagDegree : MvPolynomial (T × Fin N) ℝ →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ antisymDegree T N / eval (basePoint T N) (antisymDelta T N)) •
    ∑ w : T → Equiv.Perm (Fin N), fullSign T N w •
      ((aeval fun p => basePoint T N (fullAct T N w p)).toLinearMap ∘ₗ
        homogeneousComponent (antisymDegree T N))

def degFl (lam : T × Fin N → ℝ) : ℝ := flagDegree T N (linForm lam ^ antisymDegree T N)

def cFl : ℝ := degFl T N (basePoint T N) / eval (basePoint T N) (antisymDelta T N)

def polar (k : ℕ) (P F : MvPolynomial (T × Fin N) ℝ) : ℝ :=
  ∑ m ∈ (homogeneousComponent k F).support, coeff m F *
    ((-1 : ℝ) ^ k * ((m.prod fun _ n => (n.factorial : ℝ)) / (k.factorial : ℝ)) * coeff m P)

def derivTerm (j : ℕ) (al be : T → ℝ) (F : MvPolynomial (T × Fin N) ℝ) : ℝ :=
  ∑ τ, flagDegree T N (∑ i : Fin N, (if i.val < j then al τ else be τ) • pderiv (τ, i) F)

def shPart (j : ℕ) (τ : T) (F : MvPolynomial (T × Fin N) ℝ) : ℝ :=
  flagDegree T N (∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < j), pderiv (τ, i) F)

def totPart (τ : T) (F : MvPolynomial (T × Fin N) ℝ) : ℝ :=
  flagDegree T N (∑ i : Fin N, pderiv (τ, i) F)

def powerSumRoots (k : ℕ) (τ : T) : MvPolynomial (T × Fin N) ℝ := ∑ i : Fin N, X (τ, i) ^ k

def firstPowerSum (j : ℕ) (τ : T) : MvPolynomial (T × Fin N) ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < j), X (τ, i)

def invForm (j : ℕ) (al be : T → ℝ) : MvPolynomial (T × Fin N) ℝ :=
  ∑ τ, (al τ • ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < j), X (τ, i) +
    be τ • ∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ i.val), X (τ, i))

def UDelInv (j : ℕ) : Submodule ℝ (MvPolynomial (T × Fin N) ℝ) :=
  (antisymInv T N j).map (LinearMap.mulLeft ℝ (antisymDelta T N))

def IsComplInV (j : ℕ) (V' : Submodule ℝ (MvPolynomial (T × Fin N) ℝ)) : Prop :=
  V' ≤ antisymSpace T N j ∧ Disjoint V' (UDelInv T N j) ∧ V' ⊔ UDelInv T N j = antisymSpace T N j

def blockTransl (j : ℕ) (τ : T) (a b : Fin N) (_ha : a.val < j) (hb : j ≤ b.val) :
    Equiv.Perm (T × Fin N) :=
  Equiv.swap (τ, ⟨j - 1, by have := b.isLt; omega⟩) (τ, a) *
    Equiv.swap (τ, ⟨j, by have := b.isLt; omega⟩) (τ, b)

def nMonomials : ℝ :=
  ((Fintype.card T * N + 1 + (antisymDegree T N + 1)).choose (antisymDegree T N + 1) : ℕ)

def kappa : ℝ := 5 * Fintype.card T

def tauB (B : ℕ) : ℝ := kappa T / B

def sB (B : ℕ) : ℝ := tauB T B ^ 2

variable {T N}

def lamB (j : ℕ) (lam₀ : T × Fin N → ℝ) (τ₀ : T) (B : ℕ) : T × Fin N → ℝ :=
  lam₀ + (2 * tauB T B) • varpiTau j τ₀

end Objects

structure VolumeSystem (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp]
    (Cl : Type) [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) where
  two_le_N : 2 ≤ N
  one_le_j : 1 ≤ j
  j_lt_N : j < N
  card_mul_gt : 2 < Fintype.card T * (N - 1)
  vol : ℝ
  vol_pos : 0 < vol
  P : ℕ → MvPolynomial (T × Fin N) ℝ
  Ps : ℕ → MvPolynomial (Option (T × Fin N)) ℝ
  C2 : ℝ
  second_volume_constant_nonneg : 0 ≤ C2
  P_homogeneous : ∀ B : ℕ, 2 ≤ B → (P B).IsHomogeneous (antisymDegree T N + 1)
  Ps_totalDegree : ∀ B : ℕ, 2 ≤ B → (Ps B).totalDegree ≤ antisymDegree T N + 1
  Ps_at_zero : ∀ B : ℕ, 2 ≤ B → ∀ lam, evalS lam 0 (Ps B) = eval lam (P B)
  P_coeff : ∀ B : ℕ, 2 ≤ B → ∀ m, |coeff m (P B)| ≤ C2 * Real.log B
  Ps_coeff : ∀ B : ℕ, 2 ≤ B → ∀ m, |coeff m (Ps B)| ≤ C2 * Real.log B
  w0 : T × Fin N → ℝ
  L : (T × Fin N → ℝ) →ₗ[ℝ] Cl
  A' : Cl
  bd' : Cl
  A'_eq : A' = L w0 - bd'
  nef : Set Cl
  ample : Set Cl
  effective : Set Cl
  nef_add : ∀ a ∈ nef, ∀ b ∈ nef, a + b ∈ nef
  nef_smul : ∀ t : ℝ, 0 ≤ t → ∀ a ∈ nef, t • a ∈ nef
  ample_subset_nef : ample ⊆ nef
  L_nef : ∀ lam, IsDominantWeight lam → L lam ∈ nef
  A'_ample : A' ∈ ample
  bd'_effective : bd' ∈ effective
  inter : Comp → MultilinearMap ℝ (fun _ : Fin (antisymDegree T N) => Cl) ℝ
  inter_symm : ∀ c v (σ : Equiv.Perm (Fin (antisymDegree T N))), inter c (v ∘ σ) = inter c v
  kleiman_nef : ∀ c v, (∀ i, v i ∈ nef) → 0 ≤ inter c v
  kleiman_effective : ∀ c v i₀, v i₀ ∈ effective → (∀ i, i ≠ i₀ → v i ∈ nef) → 0 ≤ inter c v
  inter_L : ∀ lam, ∑ c, inter c (fun _ => L lam) = vol * degFl T N lam
  Mbar : ℕ → (T × Fin N → ℝ) → ℝ → Comp → ℝ
  height : ℕ → (T × Fin N → ℝ) → ℝ → Pt → ℝ
  compOf : Pt → Comp
  zdense : Comp → Set Pt → Prop
  zdense_nonempty : ∀ c S, zdense c S → ∃ y ∈ S, compOf y = c
  zdense_mono : ∀ c S S', zdense c S → S ⊆ S' → zdense c S'
  arithNef : ℕ → (T × Fin N → ℝ) → ℝ → Prop
  s0 : ℝ
  one_le_localLevel : 0 < s0
  C3 : ℝ
  C3_nonneg : 0 ≤ C3
  agreement : ∀ B : ℕ, 2 ≤ B → ∀ lam s, IsRatVec lam → IsRatNum s → ‖lam‖ ≤ 1 → 0 < s → s ≤ s0 →
    IsDominantWeight (lam - s • w0) →
    |∑ c, Mbar B lam s c - evalS (lam - s • w0) s (Ps B)| ≤ C3 * s
  nefness : ∀ B : ℕ, 2 ≤ B → ∀ lam s, IsRatVec lam → IsRatNum s →
    sumNorm lam ≤ Fintype.card T * N → 0 < s → s ≤ s0 → IsDominantWeight (lam - s • w0) →
    (∀ τ, 4 * Fintype.card T * ‖lam - s • w0‖ ≤ ((B : ℝ) - 2) * ncGap j (lam - s • w0) τ) →
    arithNef B lam s
  moriwaki_lower : ∀ B : ℕ, 2 ≤ B → ∀ lam s c (e : ℝ), arithNef B lam s →
    (∀ y, compOf y = c → e ≤ height B lam s y) →
    (antisymDegree T N + 1 : ℝ) * e * inter c (fun _ => L lam - s • bd') ≤ Mbar B lam s c
  moriwaki_upper : ∀ B : ℕ, 2 ≤ B → ∀ lam s c (e : ℝ) S, arithNef B lam s → zdense c S →
    (∀ y ∈ S, height B lam s y ≤ e) →
    Mbar B lam s c ≤ (antisymDegree T N + 1 : ℝ) * e * inter c (fun _ => L lam - s • bd')
  ta0 : ℝ → ℝ
  C4 : ℝ → ℝ
  tauZero_pos : ∀ c₀, 0 < c₀ → c₀ ≤ 1 → 0 < ta0 c₀
  initial_radius_small : ∀ c₀, 0 < c₀ → c₀ ≤ 1 → ta0 c₀ ≤ 1 / 2 ∧ 2 * (2 * ‖w0‖) * ta0 c₀ ≤ 1 ∧
    2 * (2 * ‖w0‖) * ta0 c₀ ^ 2 ≤ c₀ ∧ ta0 c₀ ^ 2 ≤ s0
  C4_nonneg : ∀ c₀, 0 ≤ C4 c₀
  height_lower : ∀ B : ℕ, 2 ≤ B → ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 → ∀ lam ta, IsRatVec lam → ‖lam‖ ≤ 1 →
    0 < ta → ta ≤ ta0 c₀ → IsRatNum (ta ^ 2) → (∀ τ, ta ≤ ncGap j lam τ) →
    (∀ τ i, i + 1 < N → i + 1 ≠ j → c₀ ≤ gapAtIndex lam τ i) →
    ∀ y, -(C4 c₀ * Real.log (B / ta ^ 2)) ≤ height B lam (ta ^ 2) y
  C5 : ℝ
  fifth_volume_constant_nonneg : 0 ≤ C5
  height_upper : ∀ B : ℕ, 2 ≤ B → ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 → ∀ lam ta, IsRatVec lam → ‖lam‖ ≤ 1 →
    0 < ta → ta ≤ ta0 c₀ → IsRatNum (ta ^ 2) → (∀ τ, ta ≤ ncGap j lam τ) →
    (∀ τ i, i + 1 < N → i + 1 ≠ j → c₀ ≤ gapAtIndex lam τ i) →
    ∀ c, ∃ S, zdense c S ∧ ∀ y ∈ S, height B lam (ta ^ 2) y ≤ C5 * Real.log B
  hFl : MvPolynomial (T × Fin N) ℝ
  antisymmetry : ∀ B : ℕ, 2 ≤ B → ∀ σ, IsBlockSimpleSwap T N j σ →
    rename σ (P B - vol • hFl) = -(P B - vol • hFl)
  hFl_homogeneous : hFl.IsHomogeneous (antisymDegree T N + 1)
  hFl_wall : ∀ lam, IsDominantWeight lam → (∃ τ, ncGap j lam τ = 0) → eval lam hFl = 0
  hFl_nonneg : ∀ lam, IsDominantWeight lam → 0 ≤ eval lam hFl

namespace VolumeSystem

variable {T : Type} [Fintype T] [DecidableEq T] {N j : ℕ} {Comp : Type} [Fintype Comp]
  {Cl : Type} [AddCommGroup Cl] [Module ℝ Cl] {Pt : Type} (V : VolumeSystem T N j Comp Cl Pt)

def lamPP (lam : T × Fin N → ℝ) (s : ℝ) : T × Fin N → ℝ := lam - s • V.w0

def C7 : ℝ := 2 * ‖V.w0‖

def thresholdB (c₀ : ℝ) : ℝ := 20 * Fintype.card T * (1 + V.C7) / (c₀ * min (min (V.ta0 c₀) V.s0) 1)

def C8 : ℝ := V.vol * cFl T N * 2 ^ antisymDegree T N

def MTop (lam : T × Fin N → ℝ) (s : ℝ) (c : Comp) : ℝ := V.inter c (fun _ => V.L lam - s • V.bd')

def MbarTot (B : ℕ) (lam : T × Fin N → ℝ) (s : ℝ) : ℝ := ∑ c, V.Mbar B lam s c

def RB (B : ℕ) : MvPolynomial (T × Fin N) ℝ := V.P B - V.vol • V.hFl

def PP (B : ℕ) (F : MvPolynomial (T × Fin N) ℝ) : ℝ := polar T N (antisymDegree T N + 1) (V.P B) F

def hh (F : MvPolynomial (T × Fin N) ℝ) : ℝ := polar T N (antisymDegree T N + 1) V.hFl F

def alBeScale : ℝ := cFl T N * V.vol * (antisymDegree T N + 1)

def IsThmBError (B : ℕ) (al be : T → ℝ) (E : MvPolynomial (T × Fin N) ℝ) : Prop :=
  ∀ lam, eval lam E = eval lam (V.P B) - V.vol * (eval lam V.hFl +
    (antisymDegree T N + 1 : ℝ) * degFl T N lam * eval lam (invForm T N j al be))

def TheoremWSetting (c₀ : ℝ) (τ₀ : T) (lam₀ : T × Fin N → ℝ) (B : ℕ) : Prop :=
  IsRatNum c₀ ∧ 0 < c₀ ∧ c₀ ≤ 1 ∧ IsRatVec lam₀ ∧ lam₀ ∈ Kset j τ₀ c₀ ∧ V.thresholdB c₀ ≤ B

end VolumeSystem

set_option linter.dupNamespace false

section Statements

variable {T : Type} [Fintype T] [DecidableEq T] {N j : ℕ} {Comp : Type} [Fintype Comp]
  {Cl : Type} [AddCommGroup Cl] [Module ℝ Cl] {Pt : Type} (V : VolumeSystem T N j Comp Cl Pt)

def Step0Params.intersectionNumber_baseChange : Prop :=
  ∀ (lam₀ : T × Fin N → ℝ) (τ₀ : T) (B : ℕ), 0 < B →
    ‖V.lamPP (lamB j lam₀ τ₀ B) (sB T B) - lamB j lam₀ τ₀ B‖ ≤ V.C7 * sB T B / 2 ∧
    ∀ τ i, i + 1 < N → |gapAtIndex (V.lamPP (lamB j lam₀ τ₀ B) (sB T B)) τ i - gapAtIndex (lamB j lam₀ τ₀ B) τ i| ≤ V.C7 * sB T B

def Gap1Norm.intersectionNumber_baseChange : Prop :=
  ∀ (lam₀ : T × Fin N → ℝ) (τ₀ : T) (c₀ : ℝ) (B : ℕ), 0 < B → lam₀ ∈ Kset j τ₀ c₀ →
    ‖lamB j lam₀ τ₀ B‖ ≤ 1 / 2 + 2 * tauB T B ∧
    (2 * tauB T B + V.C7 * sB T B ≤ 1 / 2 → ‖lamB j lam₀ τ₀ B‖ ≤ 1 ∧ ‖V.lamPP (lamB j lam₀ τ₀ B) (sB T B)‖ ≤ 1)

def Gap2Tau.intersectionNumber_baseChange (_V : VolumeSystem T N j Comp Cl Pt) : Prop :=
  ∀ (lam₀ : T × Fin N → ℝ) (τ₀ : T) (c₀ : ℝ) (B : ℕ), 0 < B → lam₀ ∈ Kset j τ₀ c₀ →
    ncGap j (lamB j lam₀ τ₀ B) τ₀ = 2 * tauB T B ∧
    (∀ τ, τ ≠ τ₀ → ncGap j (lamB j lam₀ τ₀ B) τ = ncGap j lam₀ τ) ∧
    (∀ τ i, i + 1 < N → i + 1 ≠ j → gapAtIndex (lamB j lam₀ τ₀ B) τ i = gapAtIndex lam₀ τ i) ∧
    (tauB T B ≤ c₀ → ∀ τ, tauB T B ≤ ncGap j (lamB j lam₀ τ₀ B) τ)

def Gap3Dominant.intersectionNumber_baseChange : Prop :=
  ∀ (lam₀ : T × Fin N → ℝ) (τ₀ : T) (c₀ : ℝ) (B : ℕ), 0 < B → 0 < c₀ → lam₀ ∈ Kset j τ₀ c₀ →
    V.C7 * tauB T B ≤ 1 → V.C7 * sB T B ≤ c₀ / 2 →
    IsDominantWeight (V.lamPP (lamB j lam₀ τ₀ B) (sB T B)) ∧ tauB T B ≤ ncGap j (V.lamPP (lamB j lam₀ τ₀ B) (sB T B)) τ₀ ∧
    (∀ τ, τ ≠ τ₀ → c₀ / 2 ≤ ncGap j (V.lamPP (lamB j lam₀ τ₀ B) (sB T B)) τ) ∧
    (∀ τ i, i + 1 < N → i + 1 ≠ j → c₀ / 2 ≤ gapAtIndex (V.lamPP (lamB j lam₀ τ₀ B) (sB T B)) τ i)

def Gap4Nef.intersectionNumber_baseChange : Prop :=
  ∀ (lam₀ : T × Fin N → ℝ) (τ₀ : T) (c₀ : ℝ) (B : ℕ), 0 < c₀ → lam₀ ∈ Kset j τ₀ c₀ →
    (10 : ℝ) ≤ B → 2 + 8 * Fintype.card T / c₀ ≤ B →
    2 * tauB T B + V.C7 * sB T B ≤ 1 / 2 → V.C7 * tauB T B ≤ 1 → V.C7 * sB T B ≤ c₀ / 2 →
    ∀ τ, 4 * Fintype.card T * ‖V.lamPP (lamB j lam₀ τ₀ B) (sB T B)‖ ≤ ((B : ℝ) - 2) * ncGap j (V.lamPP (lamB j lam₀ τ₀ B) (sB T B)) τ

def Gap5Small.intersectionNumber_baseChange : Prop :=
  ∀ (c₀ : ℝ) (B : ℕ), 0 < c₀ → c₀ ≤ 1 → V.thresholdB c₀ ≤ B → tauB T B ≤ V.ta0 c₀ ∧ sB T B ≤ V.s0

def ThresholdExists.intersectionNumber_baseChange : Prop :=
  ∀ (c₀ : ℝ) (B : ℕ), 0 < c₀ → c₀ ≤ 1 → V.thresholdB c₀ ≤ B →
    2 * tauB T B + V.C7 * sB T B ≤ 1 / 2 ∧ tauB T B ≤ c₀ ∧ V.C7 * tauB T B ≤ 1 ∧
    V.C7 * sB T B ≤ c₀ / 2 ∧ (10 : ℝ) ≤ B ∧ 2 + 8 * Fintype.card T / c₀ ≤ B ∧
    tauB T B ≤ V.ta0 c₀ ∧ sB T B ≤ V.s0

def DegDifferenceNonneg.intersectionNumber_baseChange : Prop :=
  ∀ (lam : T × Fin N → ℝ) (s : ℝ), IsDominantWeight lam → IsDominantWeight (V.lamPP lam s) → 0 ≤ s →
    ∑ c, V.MTop lam s c ≤ ∑ c, V.inter c (fun _ => V.L lam)

def MTopNonneg.intersectionNumber_baseChange : Prop :=
  ∀ (lam : T × Fin N → ℝ) (s : ℝ), IsDominantWeight (V.lamPP lam s) → 0 ≤ s → 0 ≤ ∑ c, V.MTop lam s c

def TopLeDeg.intersectionNumber_baseChange : Prop :=
  ∀ (lam : T × Fin N → ℝ) (s : ℝ), IsDominantWeight lam → IsDominantWeight (V.lamPP lam s) → 0 ≤ s →
    ∑ c, V.MTop lam s c ≤ V.vol * degFl T N lam

def DegBoundByTau.intersectionNumber_baseChange : Prop :=
  ∀ (lam₀ : T × Fin N → ℝ) (τ₀ : T) (c₀ : ℝ) (B : ℕ), 0 < B → 0 < c₀ → lam₀ ∈ Kset j τ₀ c₀ →
    ‖lamB j lam₀ τ₀ B‖ ≤ 1 → V.vol * degFl T N (lamB j lam₀ τ₀ B) ≤ V.C8 * tauB T B

def ComponentLower.intersectionNumber_baseChange : Prop :=
  ∀ B : ℕ, 2 ≤ B → ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 → ∀ lam ta, IsRatVec lam → ‖lam‖ ≤ 1 →
    0 < ta → ta ≤ V.ta0 c₀ → IsRatNum (ta ^ 2) → (∀ τ, ta ≤ ncGap j lam τ) →
    (∀ τ i, i + 1 < N → i + 1 ≠ j → c₀ ≤ gapAtIndex lam τ i) → V.arithNef B lam (ta ^ 2) →
    ∀ c, (antisymDegree T N + 1 : ℝ) * (-(V.C4 c₀ * Real.log (B / ta ^ 2))) * V.MTop lam (ta ^ 2) c ≤
      V.Mbar B lam (ta ^ 2) c

def ComponentUpper.intersectionNumber_baseChange : Prop :=
  ∀ B : ℕ, 2 ≤ B → ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 → ∀ lam ta, IsRatVec lam → ‖lam‖ ≤ 1 →
    0 < ta → ta ≤ V.ta0 c₀ → IsRatNum (ta ^ 2) → (∀ τ, ta ≤ ncGap j lam τ) →
    (∀ τ i, i + 1 < N → i + 1 ≠ j → c₀ ≤ gapAtIndex lam τ i) → V.arithNef B lam (ta ^ 2) →
    ∀ c, V.Mbar B lam (ta ^ 2) c ≤ (antisymDegree T N + 1 : ℝ) * (V.C5 * Real.log B) * V.MTop lam (ta ^ 2) c

def ComponentSum.intersectionNumber_baseChange : Prop :=
  ∀ B : ℕ, 2 ≤ B → ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 → ∀ lam ta, IsRatVec lam → ‖lam‖ ≤ 1 →
    0 < ta → ta ≤ V.ta0 c₀ → IsRatNum (ta ^ 2) → (∀ τ, ta ≤ ncGap j lam τ) →
    (∀ τ i, i + 1 < N → i + 1 ≠ j → c₀ ≤ gapAtIndex lam τ i) → V.arithNef B lam (ta ^ 2) →
    (antisymDegree T N + 1 : ℝ) * (-(V.C4 c₀ * Real.log (B / ta ^ 2))) * ∑ c, V.MTop lam (ta ^ 2) c ≤
      V.MbarTot B lam (ta ^ 2) ∧
    V.MbarTot B lam (ta ^ 2) ≤ (antisymDegree T N + 1 : ℝ) * (V.C5 * Real.log B) * ∑ c, V.MTop lam (ta ^ 2) c

def TopSqueeze.intersectionNumber_baseChange : Prop :=
  ∀ (c₀ : ℝ) (τ₀ : T) (lam₀ : T × Fin N → ℝ) (B : ℕ), V.TheoremWSetting c₀ τ₀ lam₀ B →
    |V.MbarTot B (lamB j lam₀ τ₀ B) (sB T B)| ≤
      (antisymDegree T N + 1 : ℝ) * max (3 * V.C4 c₀) V.C5 * V.C8 * kappa T * Real.log B / B

def AgreementStep.intersectionNumber_baseChange : Prop :=
  ∀ (c₀ : ℝ) (τ₀ : T) (lam₀ : T × Fin N → ℝ) (B : ℕ), V.TheoremWSetting c₀ τ₀ lam₀ B →
    |V.MbarTot B (lamB j lam₀ τ₀ B) (sB T B) - evalS (V.lamPP (lamB j lam₀ τ₀ B) (sB T B)) (sB T B) (V.Ps B)| ≤ V.C3 * sB T B

def PolyShiftStep.intersectionNumber_baseChange : Prop :=
  ∀ B : ℕ, 2 ≤ B → ∀ (mu : T × Fin N → ℝ) (s : ℝ), ‖mu‖ ≤ 1 → 0 ≤ s → s ≤ 1 →
    |evalS mu s (V.Ps B) - eval mu (V.P B)| ≤ nMonomials T N * V.C2 * s * Real.log B

def MeanValueStep.intersectionNumber_baseChange : Prop :=
  ∀ B : ℕ, 2 ≤ B → ∀ a b : T × Fin N → ℝ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
    |eval a (V.P B) - eval b (V.P B)| ≤ nMonomials T N * (antisymDegree T N + 1 : ℝ) * V.C2 * Real.log B * ‖a - b‖

def SumStep.intersectionNumber_baseChange : Prop :=
  ∀ (c₀ : ℝ) (τ₀ : T) (lam₀ : T × Fin N → ℝ) (B : ℕ), V.TheoremWSetting c₀ τ₀ lam₀ B →
    |eval lam₀ (V.P B)| ≤
      ((antisymDegree T N + 1 : ℝ) * max (3 * V.C4 c₀) V.C5 * V.C8 * kappa T + V.C3 * kappa T ^ 2 +
        nMonomials T N * V.C2 * kappa T ^ 2 +
        nMonomials T N * (antisymDegree T N + 1 : ℝ) * V.C2 * (2 * kappa T + V.C7 * kappa T ^ 2)) * Real.log B / B

def TheoremW.intersectionNumber_baseChange : Prop :=
  ∀ c₀ : ℝ, IsRatNum c₀ → 0 < c₀ → c₀ ≤ 1 → ∃ CW B₁ : ℝ, ∀ B : ℕ, B₁ ≤ B →
    ∀ τ₀ : T, ∀ lam₀ ∈ Kset j τ₀ c₀, |eval lam₀ (V.P B)| ≤ CW * Real.log B / B

def RBInV.intersectionNumber_baseChange : Prop :=
  ∀ B : ℕ, 2 ≤ B → V.RB B ∈ antisymSpace T N j

def RBOnK.intersectionNumber_baseChange : Prop :=
  ∀ (B : ℕ) (τ : T), ∀ lam ∈ Kset j τ (1 / (4 * N)), eval lam (V.RB B) = eval lam (V.P B)

def RBOnTranslates.intersectionNumber_baseChange : Prop :=
  ∀ B : ℕ, 2 ≤ B → ∀ (τ : T) (a b : Fin N) (ha : a.val < j) (hb : j ≤ b.val),
    blockTransl T N j τ a b ha hb ∈ antisymWeyl T N j ∧
    ∀ lam ∈ Kset j τ (1 / (4 * N)), lam ∘ blockTransl T N j τ a b ha hb ∈ diagHyperplane T N τ a b ∧
      |eval (lam ∘ blockTransl T N j τ a b ha hb) (V.RB B)| = |eval lam (V.RB B)|

def RBSup.intersectionNumber_baseChange : Prop :=
  ∃ CW B₁ : ℝ, ∀ B : ℕ, B₁ ≤ B → ∀ (τ : T) (a b : Fin N) (ha : a.val < j) (hb : j ≤ b.val),
    ∀ lam ∈ Kset j τ (1 / (4 * N)),
      |eval (lam ∘ blockTransl T N j τ a b ha hb) (V.RB B)| ≤ CW * Real.log B / B

def RBDecomposition.intersectionNumber_baseChange : Prop :=
  ∀ V' : Submodule ℝ (MvPolynomial (T × Fin N) ℝ), IsComplInV T N j V' →
    ∃ C B₁ : ℝ, ∀ B : ℕ, B₁ ≤ B → ∃ l ∈ antisymInv T N j, ∃ E ∈ V',
      V.RB B = antisymDelta T N * l + E ∧ ∀ m, |coeff m E| ≤ C * Real.log B / B

def DefineAlBe.intersectionNumber_baseChange : Prop :=
  ∀ l ∈ antisymInv T N j, ∃! ab : (T → ℝ) × (T → ℝ), l = V.alBeScale • invForm T N j ab.1 ab.2

def TheoremB.intersectionNumber_baseChange : Prop :=
  ∀ V' : Submodule ℝ (MvPolynomial (T × Fin N) ℝ), IsComplInV T N j V' →
    ∃ CB B₁ : ℝ, ∀ B : ℕ, B₁ ≤ B → ∃ al be : T → ℝ,
      V.RB B - antisymDelta T N * (V.alBeScale • invForm T N j al be) ∈ V' ∧
      (∃ E, V.IsThmBError B al be E ∧ ∀ m, |coeff m E| ≤ CB * Real.log B / B)

def ComplementChange.intersectionNumber_baseChange : Prop :=
  ∀ V' V'' : Submodule ℝ (MvPolynomial (T × Fin N) ℝ), IsComplInV T N j V' → IsComplInV T N j V'' →
    ∃ C B₁ : ℝ, ∀ B : ℕ, B₁ ≤ B → ∀ al be al'' be'' : T → ℝ,
      V.RB B - antisymDelta T N * (V.alBeScale • invForm T N j al be) ∈ V' →
      V.RB B - antisymDelta T N * (V.alBeScale • invForm T N j al'' be'') ∈ V'' →
      ∀ τ, |al τ - al'' τ| ≤ C * Real.log B / B ∧ |be τ - be'' τ| ≤ C * Real.log B / B

def AlBeBound.intersectionNumber_baseChange : Prop :=
  ∀ V' : Submodule ℝ (MvPolynomial (T × Fin N) ℝ), IsComplInV T N j V' →
    ∃ C B₁ : ℝ, ∀ B : ℕ, B₁ ≤ B → ∀ al be : T → ℝ,
      V.RB B - antisymDelta T N * (V.alBeScale • invForm T N j al be) ∈ V' →
      ∀ τ, |al τ| ≤ C * Real.log B ∧ |be τ| ≤ C * Real.log B

def CorollaryBPrime.intersectionNumber_baseChange : Prop :=
  ∃ CB B₁ : ℝ, ∀ B : ℕ, B₁ ≤ B → ∃ al be : T → ℝ, (∃ E, V.IsThmBError B al be E ∧ ∀ m, |coeff m E| ≤ CB * Real.log B / B) ∧
    ∃ EE : MvPolynomial (T × Fin N) ℝ →ₗ[ℝ] ℝ,
      (∀ F : MvPolynomial (T × Fin N) ℝ, F.IsHomogeneous (antisymDegree T N + 1) →
        V.PP B F = V.vol * (V.hh F - derivTerm T N j al be F) + EE F) ∧
      ∀ m : T × Fin N →₀ ℕ, m.degree = antisymDegree T N + 1 →
        |EE (monomial m 1)| ≤ CB * Real.log B / B

def CorollaryBPrimeMonomial.intersectionNumber_baseChange : Prop :=
  ∀ (B : ℕ), 2 ≤ B → ∀ (al be : T → ℝ) (E : MvPolynomial (T × Fin N) ℝ) (C : ℝ),
    V.IsThmBError B al be E → (∀ m, |coeff m E| ≤ C) →
    ∀ m : T × Fin N →₀ ℕ, m.degree = antisymDegree T N + 1 →
      |V.PP B (monomial m 1) - V.vol * (V.hh (monomial m 1) - derivTerm T N j al be (monomial m 1))| ≤ C

def CorollaryBSecondOne.intersectionNumber_baseChange : Prop :=
  ∃ CB B₁ : ℝ, ∀ B : ℕ, B₁ ≤ B → ∃ al be : T → ℝ, (∃ E, V.IsThmBError B al be E ∧ ∀ m, |coeff m E| ≤ CB * Real.log B / B) ∧
    ∃ EE : MvPolynomial (T × Fin N) ℝ →ₗ[ℝ] ℝ,
      (∀ F : MvPolynomial (T × Fin N) ℝ, F.IsHomogeneous (antisymDegree T N + 1) →
        V.PP B F = V.vol * (V.hh F - derivTerm T N j al be F) + EE F) ∧
      (∀ m : T × Fin N →₀ ℕ, m.degree = antisymDegree T N + 1 →
        |EE (monomial m 1)| ≤ CB * Real.log B / B) ∧
      ∀ (τ : T) (Q : MvPolynomial (T × Fin N) ℝ), Q.IsHomogeneous (antisymDegree T N) →
        V.PP B (powerSumRoots T N 1 τ * Q) = V.vol * V.hh (powerSumRoots T N 1 τ * Q) -
          V.vol * (j * al τ + ((N : ℝ) - j) * be τ) * flagDegree T N Q + EE (powerSumRoots T N 1 τ * Q)

def CorollaryBSecondTwo.intersectionNumber_baseChange : Prop :=
  ∃ CB B₁ : ℝ, ∀ B : ℕ, B₁ ≤ B → ∃ al be : T → ℝ, (∃ E, V.IsThmBError B al be E ∧ ∀ m, |coeff m E| ≤ CB * Real.log B / B) ∧
    ∃ EE : MvPolynomial (T × Fin N) ℝ →ₗ[ℝ] ℝ,
      (∀ F : MvPolynomial (T × Fin N) ℝ, F.IsHomogeneous (antisymDegree T N + 1) →
        V.PP B F = V.vol * (V.hh F - derivTerm T N j al be F) + EE F) ∧
      (∀ m : T × Fin N →₀ ℕ, m.degree = antisymDegree T N + 1 →
        |EE (monomial m 1)| ≤ CB * Real.log B / B) ∧
      ∀ (τ : T) (Q' : MvPolynomial (T × Fin N) ℝ), Q'.IsHomogeneous (antisymDegree T N - 1) →
        V.PP B (powerSumRoots T N 2 τ * Q') = V.vol * V.hh (powerSumRoots T N 2 τ * Q') -
          2 * V.vol * (al τ - be τ) * flagDegree T N (firstPowerSum T N j τ * Q') +
          EE (powerSumRoots T N 2 τ * Q')

end Statements

def Step0Params.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    Step0Params.intersectionNumber_baseChange V

def Gap1Norm.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    Gap1Norm.intersectionNumber_baseChange V

def Gap2Tau.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    Gap2Tau.intersectionNumber_baseChange V

def Gap3Dominant.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    Gap3Dominant.intersectionNumber_baseChange V

def Gap4Nef.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    Gap4Nef.intersectionNumber_baseChange V

def Gap5Small.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    Gap5Small.intersectionNumber_baseChange V

def ThresholdExists.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    ThresholdExists.intersectionNumber_baseChange V

def DegDifferenceNonneg.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    DegDifferenceNonneg.intersectionNumber_baseChange V

def MTopNonneg.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    MTopNonneg.intersectionNumber_baseChange V

def TopLeDeg.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    TopLeDeg.intersectionNumber_baseChange V

def DegBoundByTau.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    DegBoundByTau.intersectionNumber_baseChange V

def ComponentLower.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    ComponentLower.intersectionNumber_baseChange V

def ComponentUpper.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    ComponentUpper.intersectionNumber_baseChange V

def ComponentSum.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    ComponentSum.intersectionNumber_baseChange V

def TopSqueeze.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    TopSqueeze.intersectionNumber_baseChange V

def AgreementStep.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    AgreementStep.intersectionNumber_baseChange V

def PolyShiftStep.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    PolyShiftStep.intersectionNumber_baseChange V

def MeanValueStep.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    MeanValueStep.intersectionNumber_baseChange V

def SumStep.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    SumStep.intersectionNumber_baseChange V

def LogRatioBound.Statement : Prop :=
  ∀ (T : Type) [Fintype T], Nonempty T → ∀ B : ℕ, 1 ≤ B →
    Real.log (B / sB T B) = Real.log ((B : ℝ) ^ 3 / kappa T ^ 2) ∧
      Real.log (B / sB T B) ≤ 3 * Real.log B

def TheoremW.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    TheoremW.intersectionNumber_baseChange V

def RBInV.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    RBInV.intersectionNumber_baseChange V

def RBOnK.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    RBOnK.intersectionNumber_baseChange V

def RBOnTranslates.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    RBOnTranslates.intersectionNumber_baseChange V

def RBSup.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    RBSup.intersectionNumber_baseChange V

def RBDecomposition.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    RBDecomposition.intersectionNumber_baseChange V

def DefineAlBe.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    DefineAlBe.intersectionNumber_baseChange V

def TheoremB.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    TheoremB.intersectionNumber_baseChange V

def ComplementChange.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    ComplementChange.intersectionNumber_baseChange V

def AlBeBound.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    AlBeBound.intersectionNumber_baseChange V

def CorollaryBPrime.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    CorollaryBPrime.intersectionNumber_baseChange V

def CorollaryBPrimeRow.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (al be : T → ℝ) (F : MvPolynomial (T × Fin N) ℝ),
    derivTerm T N j al be F = ∑ τ, (al τ - be τ) * shPart T N j τ F + ∑ τ, be τ * totPart T N τ F

def CorollaryBPrimeMonomial.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    CorollaryBPrimeMonomial.intersectionNumber_baseChange V

def CorollaryBSecondOne.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    CorollaryBSecondOne.intersectionNumber_baseChange V

def CorollaryBSecondTwo.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (Comp : Type) [Fintype Comp] (Cl : Type)
    [AddCommGroup Cl] [Module ℝ Cl] (Pt : Type) (V : VolumeSystem T N j Comp Cl Pt),
    CorollaryBSecondTwo.intersectionNumber_baseChange V

section Inhabitants

theorem dim_three : antisymDegree (Fin 3) 2 = 3 := by decide

theorem sum_pi_fin_succ {α : Type} [Fintype α] {n : ℕ} (F : (Fin (n + 1) → α) → ℝ) :
    ∑ w, F w = ∑ a, ∑ v : Fin n → α, F (Fin.cons a v) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem univ_perm_two : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
  decide

theorem sum_perm_two (F : Equiv.Perm (Fin 2) → ℝ) : ∑ w, F w = F 1 + F (Equiv.swap 0 1) := by
  rw [univ_perm_two, Finset.sum_pair (by decide)]

theorem flagDegree_apply {T : Type} [Fintype T] [DecidableEq T] {N : ℕ}
    (G : MvPolynomial (T × Fin N) ℝ) :
    flagDegree T N G = (-1 : ℝ) ^ antisymDegree T N / eval (basePoint T N) (antisymDelta T N) *
      ∑ w : T → Equiv.Perm (Fin N), fullSign T N w *
        eval (fun p => basePoint T N (fullAct T N w p)) (homogeneousComponent (antisymDegree T N) G) := by
  simp [flagDegree, LinearMap.sum_apply, smul_eq_mul]

theorem Ioi_one_fin_two_eq_empty : Finset.Ioi (1 : Fin 2) = ∅ := by decide

theorem cons_three_two {α : Type} (a : α) (v : Fin 2 → α) : (Fin.cons a v : Fin 3 → α) 2 = v 1 := rfl

def gap2 (v : Fin 3 × Fin 2 → ℝ) (τ : Fin 3) : ℝ := v (τ, 0) - v (τ, 1)

theorem flagDegree_three (u v w : Fin 3 × Fin 2 → ℝ) :
    flagDegree (Fin 3) 2 (linForm u * linForm v * linForm w) =
      gap2 u 0 * gap2 v 1 * gap2 w 2 + gap2 u 0 * gap2 v 2 * gap2 w 1 +
      gap2 u 1 * gap2 v 0 * gap2 w 2 + gap2 u 1 * gap2 v 2 * gap2 w 0 +
      gap2 u 2 * gap2 v 0 * gap2 w 1 + gap2 u 2 * gap2 v 1 * gap2 w 0 := by
  have hl : ∀ x : Fin 3 × Fin 2 → ℝ, linForm x ∈ homogeneousSubmodule (Fin 3 × Fin 2) ℝ 1 := by
    intro x
    unfold linForm
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ ?_)
    exact isHomogeneous_X ℝ p
  have hp : linForm u * linForm v * linForm w ∈ homogeneousSubmodule (Fin 3 × Fin 2) ℝ 3 :=
    ((hl u).mul (hl v)).mul (hl w)
  have hΔ : eval (basePoint (Fin 3) 2) (antisymDelta (Fin 3) 2) = 1 := by
    simp [antisymDelta, basePoint, Fin.prod_univ_three, Fin.prod_univ_two, Ioi_one_fin_two_eq_empty]
  rw [flagDegree_apply, dim_three, homogeneousComponent_of_mem hp, if_pos rfl, hΔ, sum_pi_fin_succ]
  simp_rw [sum_pi_fin_succ, sum_perm_two, Fintype.sum_unique]
  simp [fullSign, fullAct, basePoint, linForm, Fin.prod_univ_three, Fintype.sum_prod_type,
    Fin.sum_univ_three, Fin.sum_univ_two, gap2, cons_three_two, Equiv.Perm.sign_swap']
  ring

def ellPoly : MvPolynomial (Fin 3 × Fin 2) ℝ := ∑ τ : Fin 3, (X (τ, 0) - X (τ, 1))

theorem eval_ellPoly (x : Fin 3 × Fin 2 → ℝ) : eval x ellPoly = gap2 x 0 + gap2 x 1 + gap2 x 2 := by
  simp [ellPoly, Fin.sum_univ_three, gap2]
  ring

theorem eval_antisymDelta_three (x : Fin 3 × Fin 2 → ℝ) :
    eval x (antisymDelta (Fin 3) 2) = gap2 x 0 * gap2 x 1 * gap2 x 2 := by
  simp [antisymDelta, Fin.prod_univ_three, Fin.prod_univ_two, Ioi_one_fin_two_eq_empty, gap2]

theorem antisymDelta_three : antisymDelta (Fin 3) 2 =
    (X (0, 0) - X (0, 1)) * (X (1, 0) - X (1, 1)) * (X (2, 0) - X (2, 1)) := by
  simp [antisymDelta, Fin.prod_univ_three, Fin.prod_univ_two, Ioi_one_fin_two_eq_empty]

theorem sub_X_homogeneous (p q : Fin 3 × Fin 2) :
    (X p - X q : MvPolynomial (Fin 3 × Fin 2) ℝ).IsHomogeneous 1 :=
  (isHomogeneous_X ℝ p).sub (isHomogeneous_X ℝ q)

theorem delta_ell_homogeneous (c : ℝ) :
    (c • (antisymDelta (Fin 3) 2 * ellPoly)).IsHomogeneous (antisymDegree (Fin 3) 2 + 1) := by
  rw [dim_three]
  have hΔ : (antisymDelta (Fin 3) 2).IsHomogeneous 3 := by
    rw [antisymDelta_three]
    exact ((sub_X_homogeneous _ _).mul (sub_X_homogeneous _ _)).mul (sub_X_homogeneous _ _)
  have hℓ : ellPoly.IsHomogeneous 1 := by
    unfold ellPoly
    exact IsHomogeneous.sum _ _ _ fun τ _ => sub_X_homogeneous _ _
  have h := hΔ.mul hℓ
  rw [← mem_homogeneousSubmodule] at h ⊢
  exact Submodule.smul_mem _ c h

theorem ncGap_two (x : Fin 3 × Fin 2 → ℝ) (τ : Fin 3) : ncGap 1 x τ = gap2 x τ := by
  simp [ncGap, gapAtIndex, entry, gap2]

theorem isDominant_two (x : Fin 3 × Fin 2 → ℝ) : IsDominantWeight x ↔ ∀ τ, 0 ≤ gap2 x τ := by
  constructor
  · intro h τ
    have := h τ 0 (by norm_num)
    simpa [gapAtIndex, entry, gap2] using this
  · intro h τ i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simpa [gapAtIndex, entry, gap2] using h τ

theorem no_simple_swap (σ : Equiv.Perm (Fin 3 × Fin 2)) : ¬ IsBlockSimpleSwap (Fin 3) 2 1 σ := by
  rintro ⟨τ, a, b, hab, hblk, -⟩
  have := a.isLt
  have := b.isLt
  omega

def linFormL : (Fin 3 × Fin 2 → ℝ) →ₗ[ℝ] MvPolynomial (Fin 3 × Fin 2) ℝ where
  toFun := linForm
  map_add' := by
    intro a b
    simp only [linForm, Pi.add_apply, add_smul, Finset.sum_add_distrib, neg_add]
  map_smul' := by
    intro c a
    simp only [linForm, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, smul_neg,
      RingHom.id_apply]

def sampleInter : MultilinearMap ℝ (fun _ : Fin (antisymDegree (Fin 3) 2) => Fin 3 × Fin 2 → ℝ) ℝ :=
  (flagDegree (Fin 3) 2).compMultilinearMap
    ((MultilinearMap.mkPiAlgebra ℝ (Fin (antisymDegree (Fin 3) 2)) (MvPolynomial (Fin 3 × Fin 2) ℝ)).compLinearMap
      fun _ => linFormL)

theorem sampleInter_apply (v : Fin (antisymDegree (Fin 3) 2) → Fin 3 × Fin 2 → ℝ) :
    sampleInter v = flagDegree (Fin 3) 2 (∏ i, linForm (v i)) := by
  simp [sampleInter, linFormL]
  rfl

theorem sampleInter_symm (v : Fin (antisymDegree (Fin 3) 2) → Fin 3 × Fin 2 → ℝ)
    (σ : Equiv.Perm (Fin (antisymDegree (Fin 3) 2))) : sampleInter (v ∘ σ) = sampleInter v := by
  have h1 := sampleInter_apply (v ∘ σ)
  have h2 := sampleInter_apply v
  rw [h1, h2]
  exact congrArg _ (Equiv.prod_comp σ (fun i => linForm (v i)))

theorem six_terms_nonneg (u v w : Fin 3 × Fin 2 → ℝ) (hu : ∀ τ, 0 ≤ gap2 u τ) (hv : ∀ τ, 0 ≤ gap2 v τ)
    (hw : ∀ τ, 0 ≤ gap2 w τ) :
    0 ≤ gap2 u 0 * gap2 v 1 * gap2 w 2 + gap2 u 0 * gap2 v 2 * gap2 w 1 +
      gap2 u 1 * gap2 v 0 * gap2 w 2 + gap2 u 1 * gap2 v 2 * gap2 w 0 +
      gap2 u 2 * gap2 v 0 * gap2 w 1 + gap2 u 2 * gap2 v 1 * gap2 w 0 := by
  apply_rules [add_nonneg, mul_nonneg]

theorem sampleInter_nonneg (v : Fin (antisymDegree (Fin 3) 2) → Fin 3 × Fin 2 → ℝ)
    (hv : ∀ i, IsDominantWeight (v i)) : 0 ≤ sampleInter v := by
  rw [sampleInter_apply, ← Fin.prod_congr' (fun i => linForm (v i)) dim_three.symm,
    Fin.prod_univ_three, flagDegree_three]
  exact six_terms_nonneg _ _ _ ((isDominant_two _).1 (hv _)) ((isDominant_two _).1 (hv _))
    ((isDominant_two _).1 (hv _))

theorem degFl_three (x : Fin 3 × Fin 2 → ℝ) :
    degFl (Fin 3) 2 x = 6 * (gap2 x 0 * gap2 x 1 * gap2 x 2) := by
  rw [degFl, dim_three, show linForm x ^ 3 = linForm x * linForm x * linForm x by ring,
    flagDegree_three]
  ring

theorem sampleInter_const (x : Fin 3 × Fin 2 → ℝ) :
    sampleInter (fun _ => x) = 6 * (gap2 x 0 * gap2 x 1 * gap2 x 2) := by
  rw [sampleInter_apply, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← degFl_three]
  rfl

def coeffSum {σ : Type} (Q : MvPolynomial σ ℝ) : ℝ := ∑ m ∈ Q.support, |coeff m Q|

theorem coeffSum_nonneg {σ : Type} (Q : MvPolynomial σ ℝ) : 0 ≤ coeffSum Q :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_coeff_le_coeffSum {σ : Type} (Q : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    |coeff m Q| ≤ coeffSum Q := by
  by_cases h : m ∈ Q.support
  · exact Finset.single_le_sum (f := fun m => |coeff m Q|) (fun _ _ => abs_nonneg _) h
  · have h0 : coeff m Q = 0 := by
      by_contra h'
      exact h (mem_support_iff.2 h')
    rw [h0, abs_zero]
    exact coeffSum_nonneg Q

theorem abs_coeff_le_log {σ : Type} (Q : MvPolynomial σ ℝ) (K : ℝ) (hK : coeffSum Q ≤ K)
    (B : ℕ) (hB : 2 ≤ B) (m : σ →₀ ℕ) : |coeff m Q| ≤ K / Real.log 2 * Real.log B := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hB' : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) (by exact_mod_cast hB)
  have hK0 : 0 ≤ K := (coeffSum_nonneg Q).trans hK
  calc |coeff m Q| ≤ K := (abs_coeff_le_coeffSum Q m).trans hK
    _ = K / Real.log 2 * Real.log 2 := by rw [div_mul_cancel₀ _ h2.ne']
    _ ≤ K / Real.log 2 * Real.log B := mul_le_mul_of_nonneg_left hB' (div_nonneg hK0 h2.le)

def samplePoly (a : ℝ) : MvPolynomial (Fin 3 × Fin 2) ℝ := (6 * a / 25) • (antisymDelta (Fin 3) 2 * ellPoly)

theorem eval_samplePoly (a : ℝ) (x : Fin 3 × Fin 2 → ℝ) :
    eval x (samplePoly a) = 6 * a / 25 * ((gap2 x 0 * gap2 x 1 * gap2 x 2) * (gap2 x 0 + gap2 x 1 + gap2 x 2)) := by
  simp [samplePoly, eval_antisymDelta_three, eval_ellPoly]

theorem isDominant_add (x y : Fin 3 × Fin 2 → ℝ) (hx : IsDominantWeight x) (hy : IsDominantWeight y) :
    IsDominantWeight (x + y) := by
  rw [isDominant_two] at hx hy ⊢
  intro τ
  have := hx τ
  have := hy τ
  simp only [gap2, Pi.add_apply] at *
  linarith

theorem isDominant_smul (t : ℝ) (ht : 0 ≤ t) (x : Fin 3 × Fin 2 → ℝ) (hx : IsDominantWeight x) :
    IsDominantWeight (t • x) := by
  rw [isDominant_two] at hx ⊢
  intro τ
  have := mul_nonneg ht (hx τ)
  simp only [gap2, Pi.smul_apply, smul_eq_mul] at *
  linarith

theorem isDominant_zero : IsDominantWeight (0 : Fin 3 × Fin 2 → ℝ) := by
  rw [isDominant_two]
  intro τ
  simp [gap2]

theorem abs_le_of_norm {x : Fin 3 × Fin 2 → ℝ} (hx : ‖x‖ ≤ 1) (p : Fin 3 × Fin 2) : |x p| ≤ 1 := by
  have := (norm_le_pi_norm x p).trans hx
  rwa [Real.norm_eq_abs] at this

theorem gap_le_two_of_norm_le_one {x : Fin 3 × Fin 2 → ℝ} (hx : ‖x‖ ≤ 1) (τ : Fin 3) : gap2 x τ ≤ 2 := by
  have h1 := abs_le.1 (abs_le_of_norm hx (τ, 0))
  have h2 := abs_le.1 (abs_le_of_norm hx (τ, 1))
  simp only [gap2]
  linarith [h1.2, h2.1]

def sampleSystem (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    VolumeSystem (Fin 3) 2 1 Unit (Fin 3 × Fin 2 → ℝ) Unit where
  two_le_N := le_rfl
  one_le_j := le_rfl
  j_lt_N := by norm_num
  card_mul_gt := by simp
  vol := 1
  vol_pos := one_pos
  P := fun _ => samplePoly a
  Ps := fun _ => rename some (samplePoly a)
  C2 := (coeffSum (samplePoly a) + coeffSum (rename some (samplePoly a))) / Real.log 2
  second_volume_constant_nonneg := div_nonneg (add_nonneg (coeffSum_nonneg _) (coeffSum_nonneg _))
    (Real.log_nonneg (by norm_num))
  P_homogeneous := fun _ _ => delta_ell_homogeneous _
  Ps_totalDegree := fun _ _ =>
    (totalDegree_rename_le _ _).trans (delta_ell_homogeneous _).totalDegree_le
  Ps_at_zero := by
    intro B _ lam
    simp [evalS, eval_rename, Function.comp_def]
  P_coeff := fun B hB m => abs_coeff_le_log _ _ (le_add_of_nonneg_right (coeffSum_nonneg _)) B hB m
  Ps_coeff := fun B hB m => abs_coeff_le_log _ _ (le_add_of_nonneg_left (coeffSum_nonneg _)) B hB m
  w0 := 0
  L := LinearMap.id
  A' := 0
  bd' := 0
  A'_eq := by simp
  nef := {v | IsDominantWeight v}
  ample := {v | IsDominantWeight v}
  effective := {v | IsDominantWeight v}
  nef_add := fun x hx y hy => isDominant_add x y hx hy
  nef_smul := fun t ht x hx => isDominant_smul t ht x hx
  ample_subset_nef := subset_rfl
  L_nef := fun _ h => h
  A'_ample := isDominant_zero
  bd'_effective := isDominant_zero
  inter := fun _ => sampleInter
  inter_symm := fun _ v σ => sampleInter_symm v σ
  kleiman_nef := fun _ v hv => sampleInter_nonneg v hv
  kleiman_effective := by
    intro _ v i₀ h₀ hv
    refine sampleInter_nonneg v fun i => ?_
    by_cases hi : i = i₀
    · subst hi
      exact h₀
    · exact hv i hi
  inter_L := by
    intro lam
    simp only [Finset.univ_unique, Finset.sum_singleton, LinearMap.id_apply, one_mul]
    rw [sampleInter_const, degFl_three]
  Mbar := fun _ lam _ _ => eval lam (samplePoly a)
  height := fun _ lam _ _ => a * eval lam ellPoly / 100
  compOf := fun _ => ()
  zdense := fun _ S => S.Nonempty
  zdense_nonempty := fun _ _ ⟨y, hy⟩ => ⟨y, hy, rfl⟩
  zdense_mono := fun _ _ _ h hS => h.mono hS
  arithNef := fun _ lam _ => IsDominantWeight lam
  s0 := 1
  one_le_localLevel := one_pos
  C3 := 0
  C3_nonneg := le_rfl
  agreement := by
    intro B _ lam s _ _ _ _ _ _
    simp [evalS, eval_rename, Function.comp_def]
  nefness := by
    intro B _ lam s _ _ _ _ _ h _
    simpa using h
  moriwaki_lower := by
    intro B _ lam s c e h he
    have he' := he () rfl
    rw [isDominant_two] at h
    simp only [smul_zero, sub_zero, LinearMap.id_apply]
    rw [sampleInter_const, eval_samplePoly, dim_three]
    rw [eval_ellPoly] at he'
    have hG : 0 ≤ gap2 lam 0 * gap2 lam 1 * gap2 lam 2 :=
      mul_nonneg (mul_nonneg (h 0) (h 1)) (h 2)
    have := mul_le_mul_of_nonneg_right he' hG
    push_cast
    nlinarith
  moriwaki_upper := by
    intro B _ lam s c e S h hS he
    obtain ⟨y, hy⟩ := hS
    have he' := he y hy
    rw [isDominant_two] at h
    simp only [smul_zero, sub_zero, LinearMap.id_apply]
    rw [sampleInter_const, eval_samplePoly, dim_three]
    rw [eval_ellPoly] at he'
    have hG : 0 ≤ gap2 lam 0 * gap2 lam 1 * gap2 lam 2 :=
      mul_nonneg (mul_nonneg (h 0) (h 1)) (h 2)
    have := mul_le_mul_of_nonneg_right he' hG
    push_cast
    nlinarith
  ta0 := fun _ => 1 / 2
  C4 := fun _ => 0
  tauZero_pos := fun _ _ _ => by norm_num
  initial_radius_small := fun c₀ hc _ => by
    refine ⟨le_rfl, by simp, by simp [hc.le], by norm_num⟩
  C4_nonneg := fun _ => le_rfl
  height_lower := by
    intro B _ c₀ _ _ lam ta _ _ hta _ _ hg _ y
    have h := fun τ => (hta.le.trans (hg τ))
    simp only [ncGap_two] at h
    rw [eval_ellPoly]
    have := add_nonneg (add_nonneg (h 0) (h 1)) (h 2)
    simp only [zero_mul, neg_zero]
    positivity
  C5 := 1
  fifth_volume_constant_nonneg := zero_le_one
  height_upper := by
    intro B hB c₀ _ _ lam ta _ hl _ _ _ _ _ c
    refine ⟨Set.univ, Set.univ_nonempty, fun y _ => ?_⟩
    rw [eval_ellPoly, one_mul]
    have h2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
    have hB' : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) (by exact_mod_cast hB)
    have g0 := gap_le_two_of_norm_le_one hl 0
    have g1 := gap_le_two_of_norm_le_one hl 1
    have g2 := gap_le_two_of_norm_le_one hl 2
    have : a * (gap2 lam 0 + gap2 lam 1 + gap2 lam 2) ≤ 6 := by nlinarith
    linarith
  hFl := a • (antisymDelta (Fin 3) 2 * ellPoly)
  antisymmetry := fun _ _ σ hσ => absurd hσ (no_simple_swap σ)
  hFl_homogeneous := delta_ell_homogeneous a
  hFl_wall := by
    intro lam _ ⟨τ, hτ⟩
    rw [ncGap_two] at hτ
    show eval lam (a • (antisymDelta (Fin 3) 2 * ellPoly)) = 0
    simp only [smul_eval, map_mul, eval_antisymDelta_three]
    fin_cases τ <;> simp_all
  hFl_nonneg := by
    intro lam h
    rw [isDominant_two] at h
    show 0 ≤ eval lam (a • (antisymDelta (Fin 3) 2 * ellPoly))
    simp only [smul_eval, map_mul, eval_antisymDelta_three, eval_ellPoly]
    have := h 0
    have := h 1
    have := h 2
    positivity

def zeroSystem : VolumeSystem (Fin 3) 2 1 Unit (Fin 3 × Fin 2 → ℝ) Unit :=
  sampleSystem 0 le_rfl zero_le_one

theorem zeroSystem_P (B : ℕ) : zeroSystem.P B = 0 := by
  show samplePoly 0 = 0
  simp [samplePoly]

def oneSystem : VolumeSystem (Fin 3) 2 1 Unit (Fin 3 × Fin 2 → ℝ) Unit :=
  sampleSystem 1 zero_le_one le_rfl

theorem oneSystem_P_ne_zero (B : ℕ) : oneSystem.P B ≠ 0 ∧ oneSystem.hFl ≠ 0 := by
  have hb : ∀ τ, gap2 (basePoint (Fin 3) 2) τ = 1 := by
    intro τ
    simp [gap2, basePoint]
  constructor
  · intro h
    have h' := congrArg (eval (basePoint (Fin 3) 2)) h
    change eval (basePoint (Fin 3) 2) (samplePoly 1) = eval (basePoint (Fin 3) 2) 0 at h'
    rw [eval_samplePoly, hb, hb, hb] at h'
    norm_num at h'
  · intro h
    have h' := congrArg (eval (basePoint (Fin 3) 2)) h
    change eval (basePoint (Fin 3) 2) ((1 : ℝ) • (antisymDelta (Fin 3) 2 * ellPoly)) =
      eval (basePoint (Fin 3) 2) 0 at h'
    rw [smul_eval, map_mul, eval_antisymDelta_three, eval_ellPoly, hb, hb, hb] at h'
    norm_num at h'

def lamK : Fin 3 × Fin 2 → ℝ := fun p => if p.1 ≠ 0 ∧ p.2 = 0 then 1 / 4 else 0

theorem gap_sample_weight_eq (τ : Fin 3) : gap2 lamK τ = if τ = 0 then 0 else 1 / 4 := by
  fin_cases τ <;> simp [gap2, lamK]

theorem lamK_mem : lamK ∈ Kset 1 (0 : Fin 3) (1 / 8) ∧ IsRatVec lamK := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun p => ?_
    rw [Real.norm_eq_abs]
    simp only [lamK]
    split_ifs <;> norm_num
  · rw [ncGap_two, gap_sample_weight_eq]
    simp
  · intro τ hτ
    rw [ncGap_two, gap_sample_weight_eq, if_neg hτ]
    norm_num
  · intro τ i hi hij
    omega
  · intro p
    simp only [lamK]
    split_ifs
    · exact ⟨1 / 4, by push_cast; ring⟩
    · exact ⟨0, by simp⟩

theorem lamK_mem_quarter : lamK ∈ Kset 1 (0 : Fin 3) (1 / (4 * ((2 : ℕ) : ℝ))) := by
  have h : (1 / (4 * ((2 : ℕ) : ℝ)) : ℝ) = 1 / 8 := by norm_num
  rw [h]
  exact lamK_mem.1

theorem sample_satisfies_W_setting (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    (sampleSystem a ha₀ ha₁).TheoremWSetting (1 / 8) 0 lamK 1000 := by
  refine ⟨⟨1 / 8, by push_cast; ring⟩, by norm_num, by norm_num, lamK_mem.2, lamK_mem.1, ?_⟩
  show 20 * (Fintype.card (Fin 3) : ℝ) * (1 + 2 * ‖(0 : Fin 3 × Fin 2 → ℝ)‖) /
      (1 / 8 * min (min (1 / 2) 1) 1) ≤ ((1000 : ℕ) : ℝ)
  norm_num

theorem sample_gap_hypotheses (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    let V := sampleSystem a ha₀ ha₁
    (0 : ℝ) < 1 / 8 ∧ lamK ∈ Kset 1 (0 : Fin 3) (1 / 8) ∧ (10 : ℝ) ≤ ((1000 : ℕ) : ℝ) ∧
      2 + 8 * (Fintype.card (Fin 3) : ℝ) / (1 / 8) ≤ ((1000 : ℕ) : ℝ) ∧
      2 * tauB (Fin 3) 1000 + V.C7 * sB (Fin 3) 1000 ≤ 1 / 2 ∧ V.C7 * tauB (Fin 3) 1000 ≤ 1 ∧
      V.C7 * sB (Fin 3) 1000 ≤ 1 / 8 / 2 := by
  intro V
  have hC : V.C7 = 0 := by
    show 2 * ‖(0 : Fin 3 × Fin 2 → ℝ)‖ = 0
    simp
  refine ⟨by norm_num, lamK_mem.1, by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
    simp [hC, tauB, kappa] <;> norm_num

def lamG : Fin 3 × Fin 2 → ℝ := fun p => if p.2 = 0 then 1 / 4 else 0

theorem sample_height_hypotheses (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    let V := sampleSystem a ha₀ ha₁
    IsRatVec lamG ∧ ‖lamG‖ ≤ 1 ∧ (0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) ≤ V.ta0 1 ∧ IsRatNum ((1 / 4 : ℝ) ^ 2) ∧
      (∀ τ, (1 / 4 : ℝ) ≤ ncGap 1 lamG τ) ∧
      (∀ τ i, i + 1 < 2 → i + 1 ≠ 1 → (1 : ℝ) ≤ gapAtIndex lamG τ i) ∧ V.arithNef 2 lamG ((1 / 4) ^ 2) := by
  intro V
  have hg : ∀ τ, gap2 lamG τ = 1 / 4 := by
    intro τ
    simp [gap2, lamG]
  refine ⟨?_, ?_, by norm_num, ?_, ⟨1 / 16, by push_cast; norm_num⟩, ?_, ?_, ?_⟩
  · intro p
    simp only [lamG]
    split_ifs
    · exact ⟨1 / 4, by push_cast; ring⟩
    · exact ⟨0, by simp⟩
  · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun p => ?_
    rw [Real.norm_eq_abs]
    simp only [lamG]
    split_ifs <;> norm_num
  · show (1 / 4 : ℝ) ≤ 1 / 2
    norm_num
  · intro τ
    rw [ncGap_two, hg]
  · intro τ i hi hij
    omega
  · show IsDominantWeight lamG
    rw [isDominant_two]
    intro τ
    rw [hg]
    norm_num

theorem UDelInv_le_sample : UDelInv (Fin 3) 2 1 ≤ antisymSpace (Fin 3) 2 1 := by
  rintro _ ⟨l, hl, rfl⟩
  refine ⟨?_, fun σ hσ => absurd hσ (no_simple_swap σ)⟩
  rw [LinearMap.mulLeft_apply, mem_homogeneousSubmodule, dim_three]
  have hΔ : (antisymDelta (Fin 3) 2).IsHomogeneous 3 := by
    rw [antisymDelta_three]
    exact ((sub_X_homogeneous _ _).mul (sub_X_homogeneous _ _)).mul (sub_X_homogeneous _ _)
  exact hΔ.mul ((mem_homogeneousSubmodule _ _).1 hl.1)

theorem exists_complement_sample : ∃ V', IsComplInV (Fin 3) 2 1 V' := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (UDelInv (Fin 3) 2 1)
  refine ⟨W ⊓ antisymSpace (Fin 3) 2 1, inf_le_right, hW.disjoint.symm.mono_left inf_le_left, ?_⟩
  rw [sup_comm, ← sup_inf_assoc_of_le W UDelInv_le_sample, hW.sup_eq_top, top_inf_eq]

theorem sample_thmBError (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (B : ℕ) :
    (sampleSystem a ha₀ ha₁).IsThmBError B 0 0 (samplePoly a - a • (antisymDelta (Fin 3) 2 * ellPoly)) := by
  intro lam
  show _ = eval lam (samplePoly a) - 1 * (eval lam (a • (antisymDelta (Fin 3) 2 * ellPoly)) + _)
  simp [invForm]

theorem sample_degrees : (Finsupp.single ((0 : Fin 3), (0 : Fin 2)) 4).degree = antisymDegree (Fin 3) 2 + 1 ∧
    (X ((0 : Fin 3), (0 : Fin 2)) ^ 3 : MvPolynomial (Fin 3 × Fin 2) ℝ).IsHomogeneous (antisymDegree (Fin 3) 2) := by
  rw [dim_three]
  exact ⟨by simp, (isHomogeneous_X ℝ _).pow 3⟩

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.TheoremB
