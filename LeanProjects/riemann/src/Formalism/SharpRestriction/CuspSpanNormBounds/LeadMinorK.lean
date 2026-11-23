import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.S.ThB

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.BasicNotions

abbrev Mx (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def IsCloud {n k : ℕ} (u : Fin k → ℝ) (lam : Fin n → ℝ) (s : Fin n) : Prop :=
  (∃ i, lam s < u i) ∧ (∃ i, u i < lam s)

def ShapeS {n k : ℕ} (u : Fin k → ℝ) (lam : Fin n → ℝ) (bv : ℝ) : Prop :=
  ∀ s, (IsCloud u lam s → 0 ≤ lam s ∧ lam s ≤ bv / 8) ∧
    (¬ IsCloud u lam s → -2 * bv ≤ lam s ∧ lam s ≤ -bv)

def AllGaps {n : ℕ} (lam : Fin n → ℝ) (g : ℝ) : Prop := ∀ s s', s ≠ s' → g ≤ |lam s - lam s'|

def HasSeparatingGap {n k : ℕ} (u : Fin k → ℝ) (lam : Fin n → ℝ) (L : ℝ) : Prop :=
  ∃ (l : ℕ) (h : l + 1 < k), L ≤ u ⟨l, by omega⟩ - u ⟨l + 1, h⟩ ∧
    (∃ s, IsCloud u lam s ∧ u ⟨l, by omega⟩ ≤ lam s) ∧ (∃ s, IsCloud u lam s ∧ lam s ≤ u ⟨l + 1, h⟩)

def HasCut {k : ℕ} (u u' : Fin k → ℝ) (L : ℝ) : Prop :=
  ∃ a b : ℝ, IsCutS u u' (Set.Icc a b) ∧ L ≤ b - a

def StdHyp (Ch Cg : ℝ) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (lam : Fin (2 * r + k + 1) → ℝ) (u u' : Fin k → ℝ) (T T' ka b : ℝ) : Prop :=
  IsHCParam lam ∧ InterlaceS (by omega) u lam ∧ InterlaceS (by omega) u' lam ∧
  0 < ka ∧ ka ≤ b ^ Ch ∧ ka⁻¹ ≤ b ^ Ch ∧
  1 ≤ T ∧ 1 ≤ T' ∧ T ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ)) ∧ T' ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ)) ∧
  (∀ s, |lam s| ≤ b) ∧ (∀ i, |u i| ≤ b) ∧ (∀ i, |u' i| ≤ b) ∧
  AllGaps lam (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ 3) ∧
  GapAtLeast ε lam (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
    (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ∧
  (∃ bv : ℝ, Cg * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 ≤ bv ∧ ShapeS u lam bv) ∧
  ((u = u' ∧ HasSeparatingGap u lam (2 * (Cg * ((r : ℝ) + 1) ^ 2) + 1)) ∨ (u ≠ u' ∧ HasCut u u' (Cg * ((r : ℝ) + 1) ^ 2)))

def StdHyp0 (Ch Cg : ℝ) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (lam : Fin (2 * r + k + 1) → ℝ) (u u' : Fin k → ℝ) (T T' ka b : ℝ) : Prop :=
  IsHCParam lam ∧ InterlaceS (by omega) u lam ∧ InterlaceS (by omega) u' lam ∧
  0 < ka ∧ ka ≤ b ^ Ch ∧ ka⁻¹ ≤ b ^ Ch ∧
  1 ≤ T ∧ 1 ≤ T' ∧ T ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ)) ∧ T' ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ)) ∧
  (∀ s, |lam s| ≤ b) ∧ (∀ i, |u i| ≤ b) ∧ (∀ i, |u' i| ≤ b) ∧
  AllGaps lam (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ 3) ∧
  GapAtLeast ε lam (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
    (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ∧
  (∃ bv : ℝ, Cg * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 ≤ bv ∧ ShapeS u lam bv) ∧
  (u = u' → HasSeparatingGap u lam (2 * (Cg * ((r : ℝ) + 1) ^ 2) + 1))

theorem StdHyp.to0 {Ch Cg : ℝ} {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {u u' : Fin k → ℝ} {T T' ka b : ℝ} (h : StdHyp Ch Cg k r ε lam u u' T T' ka b) :
    StdHyp0 Ch Cg k r ε lam u u' T T' ka b := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, fun e => ?_⟩
  rcases h17 with h | h
  · exact h.2
  · exact absurd e h.1

def LocOk (D : D7) (Ch Cg : ℝ) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (ka b κ : ℝ) : Prop :=
  1 ≤ D.R.k ∧ L.ε = epsSH D.R ∧ L.c = cOfDpsi (κ : ℂ) ∧ 0 < L.κN ∧ L.κN ≠ ⊤ ∧
    StdHyp Ch Cg D.R.k D.R.rS L.ε lam0 L.u L.u' (Tz D.R.k D.R.rS L.z * (κ / ka) ^ (2 * D.R.rS))
      (Tz D.R.k D.R.rS L.z' * (κ / ka) ^ (2 * D.R.rS)) ka b ∧
    1 ≤ Tz D.R.k D.R.rS L.z * κ ^ (2 * D.R.rS) ∧ 1 ≤ Tz D.R.k D.R.rS L.z' * κ ^ (2 * D.R.rS)

def LocOk0 (D : D7) (Ch Cg : ℝ) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (ka b κ : ℝ) : Prop :=
  1 ≤ D.R.k ∧ L.ε = epsSH D.R ∧ L.c = cOfDpsi (κ : ℂ) ∧ 0 < L.κN ∧ L.κN ≠ ⊤ ∧
    StdHyp0 Ch Cg D.R.k D.R.rS L.ε lam0 L.u L.u' (Tz D.R.k D.R.rS L.z * (κ / ka) ^ (2 * D.R.rS))
      (Tz D.R.k D.R.rS L.z' * (κ / ka) ^ (2 * D.R.rS)) ka b ∧
    1 ≤ Tz D.R.k D.R.rS L.z * κ ^ (2 * D.R.rS) ∧ 1 ≤ Tz D.R.k D.R.rS L.z' * κ ^ (2 * D.R.rS)

theorem LocOk.to0 {D : D7} {Ch Cg : ℝ} {L : LocBessel D.R.k D.R.rS} {lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ}
    {ka b κ : ℝ} (h : LocOk D Ch Cg L lam0 ka b κ) : LocOk0 D Ch Cg L lam0 ka b κ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1.to0, h.2.2.2.2.2.2⟩

def jNorm2 {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ENNReal :=
  jNormSq k r (Tz k r L.z) (Tz k r L.z') (fun p => Real.sqrt (hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))))

def jNorm2W {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (φ : (Fin r → ℂ) × ℂ → ℂ) : ENNReal :=
  jNormSq k r (Tz k r L.z) (Tz k r L.z') (fun p => ‖φ p‖ * Real.sqrt (hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))))

def Dbig {r : ℕ} (l : ℕ) (p : (Fin r → ℂ) × ℂ) : ℂ :=
  (∏ a : Fin r, if a.val < l then p.1 a else 1) * (if r < l then p.2 else 1)

def Dpow {r : ℕ} (α : Fin (r + 1) → ℕ) (p : (Fin r → ℂ) × ℂ) : ℂ := ∏ l : Fin (r + 1), Dbig (l.val + 1) p ^ α l

def Gpt {r : ℕ} (T T' : ℝ) (γ : Point ℂ (r + 1)) : ℝ :=
  Complex.normSq (leadMinor (ptMat γ) (r + 1) le_rfl) -
    T * T' * Complex.normSq (leadMinor (ptMat γ) r (Nat.le_succ r))

def orbSq {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)) : ENNReal :=
  ⨆ (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r))
    (_ : IsPtRep L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g μR ∧ IsOrbQuot L g μR ν),
    ENNReal.ofReal (hsNormSq (OrbInt L F g ν))

def hNC {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : ℝ :=
  sInf {x | ∃ a b : Fin n, ε a ≠ ε b ∧ x = |lam a - lam b|}

def cloudGap {n k : ℕ} (u : Fin k → ℝ) (lam : Fin n → ℝ) : ℝ :=
  sInf {x | ∃ a b : Fin n, a ≠ b ∧ IsCloud u lam a ∧ IsCloud u lam b ∧ x = |lam a - lam b|}

def q0 {n k : ℕ} (Cq : ℝ) (m : ℕ) (ε : Fin n → Bool) (u : Fin k → ℝ) (lam : Fin n → ℝ) : ℝ :=
  min (hNC ε lam / (Cq * Real.sqrt m)) (cloudGap u lam) / Cq

def l1 {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ a, |x a - y a|

def shell {k r : ℕ} (L : LocBessel k r) (P : Mx k r) (j : ℕ) : Submodule ℂ L.Hs :=
  Submodule.span ℂ {v | ∃ (Λ' ν : Fin (2 * r + k + 1) → ℝ) (S : Submodule ℂ L.Hs),
    IsKTypeOf L.ε (fun g => L.σ (P⁻¹ * g * P)) Λ' S ∧ v ∈ S ∧
      IsWtOn (Formalism.REAL.Kset L.ε) (fun g => L.σ (P⁻¹ * g * P)) ν v ∧
      l1 Λ' (lowK L.ε L.lam) ≤ j ∧ l1 ν (lowK L.ε L.lam) ≤ j}

def Emom {k r : ℕ} (L : LocBessel k r) (Bf : L.Hs → L.Wp) (νq : Measure (Mt k r)) (w : L.Hs)
    (X : Mx k r → ENNReal) : ENNReal :=
  (ENNReal.ofReal (‖w‖ ^ 2))⁻¹ * ∫⁻ x, X (Matrix.of x) * (‖Bf (L.σ (Matrix.of x) w)‖₊ : ENNReal) ^ 2 ∂νq

def frob {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j))

section Glob

variable (D : D7)

def leadMinorK {K : Type*} [CommRing K] {N : ℕ} (A : Matrix (Fin N) (Fin N) K) (l : ℕ) (hl : l ≤ N) : K :=
  (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def blockEnds : ℕ → List (D.host.E × ℕ) → List ℕ
  | _, [] => []
  | acc, (_, s) :: bs => (acc + s) :: blockEnds (acc + s) bs

def ptLoc (v : D.what₂.Tau) {i : ℕ} (γ : Point D.host.E i) : Point ℂ i :=
  ptLocS D (rhoReal D) (rhoReal_ne D) v γ

def Gglob (T T' : ℕ) (γ : Point D.host.E (D.R.rS + 1)) : D.host.E :=
  leadMinorK (ptMat γ) (D.R.rS + 1) le_rfl * D.host.conj (leadMinorK (ptMat γ) (D.R.rS + 1) le_rfl) -
    (T : D.host.E) * (T' : D.host.E) *
      (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _) * D.host.conj (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _)))

def IsBPt (T T' : ℕ) (γ : Point D.host.E (D.R.rS + 1)) : Prop :=
  (∃ Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, (∀ i j, IsIntegral ℤ (Z i j)) ∧ IsInCell Z γ) ∧
    Gglob D T T' γ ≠ 0 ∧ IsIntegral ℤ (Gglob D T T' γ)

def absV (v : D.what₂.Tau) (x : D.host.E) : ℝ := ‖plEmb D v x‖

def wPt (γ : Point D.host.E (D.R.rS + 1)) : ℝ :=
  ((blockEnds D 0 γ.1).map fun l =>
    if hl : l ≤ D.R.rS + 1 then ∏ v, (1 + absV D v (leadMinorK (ptMat γ) l hl) ^ 2) ^ 2 else 1).prod

def NE (x : D.host.E) : ℝ := ∏ v, absV D v x ^ 2

def NF (x : D.host.E) : ℝ := ∏ v, absV D v x

def normWt (T T' : ℕ) (γ : Point D.host.E (D.R.rS + 1)) : ℝ :=
  NF D (Gglob D T T' γ) * ((blockEnds D 0 γ.1).map fun l =>
    if hl : l ≤ D.R.rS + 1 then NE D (leadMinorK (ptMat γ) l hl) else 1).prod

def kaRe : ℝ := D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))

structure BData (Ch Cg : ℝ) (T T' : ℕ) (b dist : ℝ) where
  L : D.what₂.Tau → LocBessel D.R.k D.R.rS
  f : ∀ v, Mx D.R.k D.R.rS → ((L v).Wq →L[ℂ] (L v).Wp)
  μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ
  hL : ∀ v, LocOk D Ch Cg (L v) (lamSH D.R (D.hc v)) (kaRe D) b (kaRe D)
  hnear : ∀ v, l1 (L v).lam (lamSH D.R (D.hc v)) ≤ dist
  hcoef : ∀ v, IsKFinCoefH (L v).σ (f v)
  hsec : ∀ v, IsSection D.R.k D.R.rS (L v).z (L v).z' (μsec v)
  hT : ∀ v, Tz D.R.k D.R.rS (L v).z = T ∧ Tz D.R.k D.R.rS (L v).z' = T'

def JSq {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist)
    (γ : Point D.host.E (D.R.rS + 1)) : ENNReal :=
  ∏ v, orbSq (X.L v) (X.f v) (ptLoc D v γ)

def jSqG {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist) : ENNReal :=
  ∏ v, jNorm2 (X.L v) (X.f v) (X.μsec v)

end Glob

structure TensorDS (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) where
  Sm : Finset (Fin n)
  Hs : Fin n → Type
  [nH : ∀ s, NormedAddCommGroup (Hs s)]
  [iH : ∀ s, InnerProductSpace ℂ (Hs s)]
  [cH : ∀ s, CompleteSpace (Hs s)]
  σs : ∀ s, Matrix (Fin n) (Fin n) ℂ → (Hs s →L[ℂ] Hs s)
  ds : ∀ s ∈ Sm, IsHCParam (μ + Pi.single s 1) ∧ IsDS ε (μ + Pi.single s 1) (σs s)
  inequiv : ∀ s ∈ Sm, ∀ s' ∈ Sm, s ≠ s' → ¬ ∃ U : Hs s ≃ₗᵢ[ℂ] Hs s',
    ∀ g ∈ UJset ε, ∀ x, U (σs s g x) = σs s' g (U x)
  toSum : ∀ (v w : H) (x y : Fin n → ℂ), IsKFin ε σ v → IsKFin ε σ w →
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, Hs (sI i)),
      (∀ i, sI i ∈ Sm ∧ IsKFin ε (σs (sI i)) (vI i) ∧ IsKFin ε (σs (sI i)) (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ g v⟫_ℂ * (star y ⬝ᵥ (g *ᵥ x)) = ∑ i, ⟪wI i, σs (sI i) g (vI i)⟫_ℂ
  ofSum : ∀ s ∈ Sm, ∀ v w : Hs s, IsKFin ε (σs s) v → IsKFin ε (σs s) w →
    ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → H) (xI yI : ι → Fin n → ℂ),
      (∀ i, IsKFin ε σ (vI i) ∧ IsKFin ε σ (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σs s g v⟫_ℂ = ∑ i, ⟪wI i, σ g (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (g *ᵥ xI i))

attribute [instance] TensorDS.nH TensorDS.iH TensorDS.cH

def BpIneq (D : D7) (Cb : ℝ) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (b : ℝ) (γ : Point ℂ (D.R.rS + 1)) : Prop :=
  ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ) * orbSq L f γ ≤
    ENNReal.ofReal (b ^ (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4) *
        (max 1 (1 / Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ)) ^ (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2)) *
      jNorm2 L f μsec

def BSum (D : D7) {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist)
    (W : Point D.host.E (D.R.rS + 1) → ℝ) : ENNReal :=
  ∑' γ : {γ : Point D.host.E (D.R.rS + 1) // IsBPt D T T' γ},
    ENNReal.ofReal (wPt D γ.1 * ptWeightG D (rhoReal D) T T' γ.1.1 * W γ.1) * JSq D X γ.1

end Formalism.MainNotions.S.ThB
