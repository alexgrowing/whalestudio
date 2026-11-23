import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Formalism.SharpRestriction.CuspSpanNormBounds.RotatedWeightedBound
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.OnePlaceEstimates

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions

theorem cOfDpsi_one : cOfDpsi ((1 : ℝ) : ℂ) = cStd := by
  simp [cOfDpsi, cStd]

def TheoremBPrimePointwise (D : D7) (Ch Cg Cb : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ),
    LocOk D Ch Cg L L.lam ka b 1 → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ

def RotatedSumBound (D : D7) (Ch Cg Cb : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b 0),
    BSumRot D X (fun _ => 1) ≤
      ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        jSqG D X

def PathWeightComponents (D : D7) (C : ℝ) : Prop :=
  ∀ T T' : ℕ, 1 ≤ T → 1 ≤ T' →
    ∑' γ : {γ : Point D.host.E (D.R.rS + 1) // IsBPt D T T' γ}, ENNReal.ofReal (wPt D γ.1)⁻¹ ≤
      ENNReal.ofReal (C ^ (Fintype.card D.what₂.Tau * (D.R.rS + 1)))

def ConclusionB3 (D : D7) (Aw Ch Cg Cb : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b 0),
    (∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) →
    BSumRot D X (fun γ => normWt D T T' γ ^ (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) ≤
      ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        jSqG D X

def FormalDegreeRatioAlt (_D : D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : TensorDS n ε μ H σ),
    IsHCParam μ → IsDS ε μ σ →
    (∀ v w : H, IsKFin ε σ v → IsKFin ε σ w →
      MemLp (fun g : Formalism.REAL.UJ ε => (frob (umat g) : ℂ) * coefOn σ v w g) 2 (Formalism.REAL.muG ε)) →
    ∀ s ∈ X.Sm, ∀ (v : H) (vs : X.Hs s), v ≠ 0 → vs ≠ 0 →
      fdegOf (Formalism.REAL.muG ε) (X.σs s) vs / fdegOf (Formalism.REAL.muG ε) σ v =
        ∏ s' ∈ Finset.univ.erase s, (μ s + 1 - μ s') / (μ s - μ s')

def BesselLeadingMinorBound (D : D7) (Ch Cg Cq Cb : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ)
    (ka b κ : ℝ), (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L lam0 ka b κ →
    l1 L.lam lam0 + (((D.R.rS + 1) * (D.R.rS + 2) : ℕ) : ℝ) ≤ q0 Cq (2 * D.R.rS + 2) L.ε L.u lam0 →
    IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ l ≤ D.R.rS + 1, jNorm2W L f μsec (Dbig l) ≤
      ENNReal.ofReal (b ^ (2 * Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2)) * jNorm2 L f μsec

def GapAndSizeRange (D : D7) (Cg Cq : ℝ) (L : LocBessel D.R.k D.R.rS) (p : ℕ) : Prop :=
  AllGaps L.lam (Cg * p * ((2 * D.R.rS + 2 : ℕ) : ℝ)) ∧
    (((D.R.rS + 1) * (p + D.R.rS + 2) : ℕ) : ℝ) ≤ q0 Cq (2 * D.R.rS + 2) L.ε L.u L.lam

def BesselDerivativeIteration (D : D7) (Ch Cg Cq Cb : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L L.lam ka b κ → GapAndSizeRange D Cg Cq L p →
    IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ α : Fin (D.R.rS + 1) → ℕ, ∑ l, α l ≤ p →
      jNorm2W L f μsec (Dpow α) ≤
        ENNReal.ofReal (b ^ (2 * Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 * (∑ l, α l : ℕ))) * jNorm2 L f μsec

def InBig {k r : ℕ} (L : LocBessel k r) (q : (Fin r → ℂ) × ℂ) : Prop :=
  (∀ i, q.1 i ≠ 0) ∧ Tz k r L.z * Tz k r L.z' < Complex.normSq q.2

def BesselExpansionCoefficientSum (D : D7) (Ch Cg Cq Cb : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ)
    (Hν : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Type) [∀ ν, NormedAddCommGroup (Hν ν)]
    [∀ ν, InnerProductSpace ℂ (Hν ν)] [∀ ν, CompleteSpace (Hν ν)]
    (σν : ∀ ν, Mx D.R.k D.R.rS → (Hν ν →L[ℂ] Hν ν)) (fν : ∀ _ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ,
      Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L L.lam ka b κ → GapAndSizeRange D Cg Cq L p →
    IsSection D.R.k D.R.rS L.z L.z' μsec →
    (∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
      IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) (σν ν) ∧ IsKFinCoefH (σν ν) (fν ν) ∧
      (jNorm2 L (fν ν) μsec = 1 ∨
        ((∀ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q → L.J (fν ν) (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0) ∧
          ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH (σν ν) f' →
            ∀ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q → L.J f' (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0))) →
    jNorm2 L (fν 0) μsec = 1 →
    ∀ α : Fin (D.R.rS + 1) → ℕ, ∑ l, α l ≤ p →
      ∃ a : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℂ, (Function.support a).Finite ∧
        (∀ ν, a ν ≠ 0 → ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * ∑ l, α l : ℕ)) ∧
        ∑' ν, ‖a ν‖ ≤ b ^ (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 * (∑ l, α l : ℕ)) ∧
        ∀ q : (Fin D.R.rS → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) →
          Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z' < Complex.normSq q.2 →
          Dpow α q • L.J (fν 0) (bigCell D.R.k D.R.rS q.1 (μsec q.2)) =
            ∑' ν, a ν • L.J (fν ν) (bigCell D.R.k D.R.rS q.1 (μsec q.2))

def RngU (D : D7) (Cu Cg' : ℝ) (lam' lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) : Prop :=
  AllGaps lam0 (Cg' * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) ∧
    l1 lam' lam0 ≤ Cu * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3

def UniformityTheoremBPrime (D : D7) (Ch Cu Cg Cg' Cb : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ)
    (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → RngU D Cu Cg' L.lam lam0 →
    IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → jNorm2 L f μsec ≠ 0 →
    ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ

def UniformityTheoremB (D : D7) (Aw Ch Cu Cg Cg' Cb : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b (Cu * D.R.k * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3)),
    (∀ v, RngU D Cu Cg' (X.L v).lam (lamSH D.R (D.hc v))) → (∀ v, jNorm2 (X.L v) (X.f v) (X.μsec v) ≠ 0) →
    BSumRot D X (fun _ => 1) ≤
      ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        jSqG D X ∧
    ((∀ v, AllGaps (lamSH D.R (D.hc v)) (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) →
      BSumRot D X (fun γ => normWt D T T' γ ^ (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) ≤
        ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
          jSqG D X)

def Dpt {r : ℕ} (γ : Point ℂ (r + 1)) (l : Fin (r + 1)) : ℂ := leadMinor (ptMat γ) (l.val + 1) (by omega)

def DpowPt {r : ℕ} (α : Fin (r + 1) → ℕ) (γ : Point ℂ (r + 1)) : ℂ := ∏ l : Fin (r + 1), Dpt γ l ^ α l

def BesselExpansionCoefficients (D : D7) (Ch Cg Cq Cb : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ)
    (Hν : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Type) [∀ ν, NormedAddCommGroup (Hν ν)]
    [∀ ν, InnerProductSpace ℂ (Hν ν)] [∀ ν, CompleteSpace (Hν ν)]
    (σν : ∀ ν, Mx D.R.k D.R.rS → (Hν ν →L[ℂ] Hν ν)) (fν : ∀ _ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ,
      Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L L.lam ka b κ → GapAndSizeRange D Cg Cq L p →
    IsSection D.R.k D.R.rS L.z L.z' μsec →
    (∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
      IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) (σν ν) ∧ IsKFinCoefH (σν ν) (fν ν) ∧
      (jNorm2 L (fν ν) μsec = 1 ∨
        ((∀ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q → L.J (fν ν) (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0) ∧
          ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH (σν ν) f' →
            ∀ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q → L.J f' (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0))) →
    jNorm2 L (fν 0) μsec = 1 →
    ∀ α β : Fin (D.R.rS + 1) → ℕ, ∑ l, α l + ∑ l, β l ≤ p →
      ∃ a : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℂ, (Function.support a).Finite ∧
        (∀ ν, a ν ≠ 0 → ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * (∑ l, α l + ∑ l, β l) : ℕ)) ∧
        ∑' ν, ‖a ν‖ ≤ b ^ (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 * (∑ l, α l + ∑ l, β l : ℕ)) ∧
        (∀ q : (Fin D.R.rS → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) →
          Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z' < Complex.normSq q.2 →
          (Dpow α q * star (Dpow β q)) • L.J (fν 0) (bigCell D.R.k D.R.rS q.1 (μsec q.2)) =
            ∑' ν, a ν • L.J (fν ν) (bigCell D.R.k D.R.rS q.1 (μsec q.2))) ∧
        (LocOk D Ch Cg L L.lam ka b κ →
          ((D.R.rS + 1 : ℕ) : ℝ) * (((D.R.rS + 1) * p : ℕ) : ℝ) ≤
            hNC L.ε L.lam / (Cq * Real.sqrt ((2 * D.R.rS + 2 : ℕ) : ℝ)) →
        ∀ (γ : Point ℂ (D.R.rS + 1)) (g : Mx D.R.k D.R.rS) (μR : Measure (Mt D.R.k D.R.rS))
          (νm : Measure (PairSp D.R.k D.R.rS)),
          Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → IsPtRep L γ g → IsRelStab L g →
          IsRootMeas L γ g μR → IsOrbQuot L g μR νm →
          (DpowPt α γ * star (DpowPt β γ)) • OrbInt L (fν 0) g νm = ∑' ν, a ν • OrbInt L (fν ν) g νm)

def BesselRangeNearParameter (D : D7) (Cg Cq : ℝ) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (p : ℕ) : Prop :=
  AllGaps lam0 (Cg * p * ((2 * D.R.rS + 2 : ℕ) : ℝ)) ∧
    l1 L.lam lam0 + (((D.R.rS + 1) * (p + D.R.rS + 2) : ℕ) : ℝ) ≤ q0 Cq (2 * D.R.rS + 2) L.ε L.u lam0

private theorem lOne_self_lemma {n : ℕ} (x : Fin n → ℝ) : l1 x x = 0 := by
  simp [l1]

theorem GapAndSizeRange.toC {D : D7} {Cg Cq : ℝ} {L : LocBessel D.R.k D.R.rS} {p : ℕ} (h : GapAndSizeRange D Cg Cq L p) :
    BesselRangeNearParameter D Cg Cq L L.lam p := by
  exact ⟨h.1, by rw [lOne_self_lemma, zero_add]; exact h.2⟩

def BesselIterationNearParameter (D : D7) (Ch Cg Cq Cb : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L lam0 ka b κ → BesselRangeNearParameter D Cg Cq L lam0 p →
    IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ α : Fin (D.R.rS + 1) → ℕ, ∑ l, α l ≤ p →
      jNorm2W L f μsec (Dpow α) ≤
        ENNReal.ofReal (b ^ (2 * Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 * (∑ l, α l : ℕ))) * jNorm2 L f μsec

def BesselExpansionNearParameter (D : D7) (Ch Cg Cq Cb : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ)
    (Hν : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Type) [∀ ν, NormedAddCommGroup (Hν ν)]
    [∀ ν, InnerProductSpace ℂ (Hν ν)] [∀ ν, CompleteSpace (Hν ν)]
    (σν : ∀ ν, Mx D.R.k D.R.rS → (Hν ν →L[ℂ] Hν ν)) (fν : ∀ _ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ,
      Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L lam0 ka b κ → BesselRangeNearParameter D Cg Cq L lam0 p →
    IsSection D.R.k D.R.rS L.z L.z' μsec →
    (∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
      IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) (σν ν) ∧ IsKFinCoefH (σν ν) (fν ν) ∧
      (jNorm2 L (fν ν) μsec = 1 ∨
        ((∀ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q → L.J (fν ν) (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0) ∧
          ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH (σν ν) f' →
            ∀ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q → L.J f' (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0))) →
    jNorm2 L (fν 0) μsec = 1 →
    ∀ α : Fin (D.R.rS + 1) → ℕ, ∑ l, α l ≤ p →
      ∃ a : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℂ, (Function.support a).Finite ∧
        (∀ ν, a ν ≠ 0 → ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * ∑ l, α l : ℕ)) ∧
        ∑' ν, ‖a ν‖ ≤ b ^ (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 * (∑ l, α l : ℕ)) ∧
        ∀ q : (Fin D.R.rS → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) →
          Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z' < Complex.normSq q.2 →
          Dpow α q • L.J (fν 0) (bigCell D.R.k D.R.rS q.1 (μsec q.2)) =
            ∑' ν, a ν • L.J (fν ν) (bigCell D.R.k D.R.rS q.1 (μsec q.2))

def BesselConjugatesEveryCell (D : D7) (Ch Cg Cq Cb : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b κ : ℝ) (p : ℕ)
    (Hν : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → Type) [∀ ν, NormedAddCommGroup (Hν ν)]
    [∀ ν, InnerProductSpace ℂ (Hν ν)] [∀ ν, CompleteSpace (Hν ν)]
    (σν : ∀ ν, Mx D.R.k D.R.rS → (Hν ν →L[ℂ] Hν ν)) (fν : ∀ _ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ,
      Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)),
    (κ = 1 ∨ κ = ka) → LocOk0 D Ch Cg L lam0 ka b κ → BesselRangeNearParameter D Cg Cq L lam0 p →
    IsSection D.R.k D.R.rS L.z L.z' μsec →
    (∀ ν : Fin (2 * D.R.rS + D.R.k + 1) → ℤ, ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * p : ℕ) →
      IsDSHpk D.R.k D.R.rS L.ε (L.lam + fun a => (ν a : ℝ)) (σν ν) ∧ IsKFinCoefH (σν ν) (fν ν) ∧
      (jNorm2 L (fν ν) μsec = 1 ∨
        ((∀ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q → L.J (fν ν) (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0) ∧
          ∀ f' : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp), IsKFinCoefH (σν ν) f' →
            ∀ q : (Fin D.R.rS → ℂ) × ℂ, InBig L q → L.J f' (bigCell D.R.k D.R.rS q.1 (μsec q.2)) = 0))) →
    jNorm2 L (fν 0) μsec = 1 →
    ∀ α β : Fin (D.R.rS + 1) → ℕ, ∑ l, α l + ∑ l, β l ≤ p →
      ∃ a : (Fin (2 * D.R.rS + D.R.k + 1) → ℤ) → ℂ, (Function.support a).Finite ∧
        (∀ ν, a ν ≠ 0 → ∑ s, |(ν s : ℝ)| ≤ ((D.R.rS + 1) * (∑ l, α l + ∑ l, β l) : ℕ)) ∧
        ∑' ν, ‖a ν‖ ≤ b ^ (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 * (∑ l, α l + ∑ l, β l : ℕ)) ∧
        (∀ q : (Fin D.R.rS → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) →
          Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z' < Complex.normSq q.2 →
          (Dpow α q * star (Dpow β q)) • L.J (fν 0) (bigCell D.R.k D.R.rS q.1 (μsec q.2)) =
            ∑' ν, a ν • L.J (fν ν) (bigCell D.R.k D.R.rS q.1 (μsec q.2))) ∧
        (LocOk D Ch Cg L lam0 ka b κ →
          ((D.R.rS + 1 : ℕ) : ℝ) * (l1 L.lam lam0 + (((D.R.rS + 1) * p : ℕ) : ℝ)) ≤
            hNC L.ε lam0 / (Cq * Real.sqrt ((2 * D.R.rS + 2 : ℕ) : ℝ)) →
        ∀ (γ : Point ℂ (D.R.rS + 1)) (g : Mx D.R.k D.R.rS) (μR : Measure (Mt D.R.k D.R.rS))
          (νm : Measure (PairSp D.R.k D.R.rS)),
          Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → IsPtRep L γ g → IsRelStab L g →
          IsRootMeas L γ g μR → IsOrbQuot L g μR νm →
          (DpowPt α γ * star (DpowPt β γ)) • OrbInt L (fν 0) g νm = ∑' ν, a ν • OrbInt L (fν ν) g νm)

theorem bessel_iteration_of_near {D : D7} {Ch Cg Cq Cb : ℝ} (h : BesselIterationNearParameter D Ch Cg Cq Cb) : BesselDerivativeIteration D Ch Cg Cq Cb := by
  intro L f μsec ka b κ p hκ hL hR hf hs α hα
  exact h L L.lam f μsec ka b κ p hκ hL hR.toC hf hs α hα

theorem bessel_expansion_coeff_of_near {D : D7} {Ch Cg Cq Cb : ℝ} (h : BesselExpansionNearParameter D Ch Cg Cq Cb) : BesselExpansionCoefficientSum D Ch Cg Cq Cb := by
  intro L μsec ka b κ p Hν _ _ _ σν fν hκ hL hR hs hν h0 α hα
  exact h L L.lam μsec ka b κ p Hν σν fν hκ hL hR.toC hs hν h0 α hα

theorem bessel_expansion_of_near {D : D7} {Ch Cg Cq Cb : ℝ} (h : BesselConjugatesEveryCell D Ch Cg Cq Cb) : BesselExpansionCoefficients D Ch Cg Cq Cb := by
  intro L μsec ka b κ p Hν _ _ _ σν fν hκ hL hR hs hν h0 α β hαβ
  obtain ⟨a, h1, h2, h3, h4, h5⟩ := h L L.lam μsec ka b κ p Hν σν fν hκ hL hR.toC hs hν h0 α β hαβ
  refine ⟨a, h1, h2, h3, h4, fun hL' hh => h5 hL' ?_⟩
  rwa [lOne_self_lemma, zero_add]

def scaleBlocks (κ τ : ℝ) (r : ℕ) : ℕ → List (ℂ × ℕ) → List (ℂ × ℕ)
  | _, [] => []
  | acc, (t, s) :: bs =>
    (((τ ^ 2 * κ ^ (2 * (r + 1 - (acc + s)) + (s - 1)) : ℝ) : ℂ) * t, s) :: scaleBlocks κ τ r (acc + s) bs

def FrameBesselBound (D : D7) (Cgf Cf : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (κ₀ κ τ : ℝ),
    0 < κ₀ → 0 < κ → 0 < τ → L.c = cOfDpsi (κ₀ : ℂ) → 0 < L.κN → L.κN ≠ ⊤ → L.ε = epsSH D.R →
    GapAtLeast L.ε L.lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) →
    IsKFinCoefH L.σ f →
    ∃ (L₁ : LocBessel D.R.k D.R.rS) (f₁ : Mx D.R.k D.R.rS → (L₁.Wq →L[ℂ] L₁.Wp)),
      L₁.ε = L.ε ∧ L₁.lam = L.lam ∧ L₁.u = L.u ∧ L₁.u' = L.u' ∧ L₁.c = cOfDpsi ((κ * κ₀ : ℝ) : ℂ) ∧
      0 < L₁.κN ∧ L₁.κN ≠ ⊤ ∧
      Tz D.R.k D.R.rS L₁.z = τ ^ 2 * Tz D.R.k D.R.rS L.z ∧ Tz D.R.k D.R.rS L₁.z' = τ ^ 2 * Tz D.R.k D.R.rS L.z' ∧
      IsKFinCoefH L₁.σ f₁ ∧
      ∀ μsec, IsSection D.R.k D.R.rS L.z L.z' μsec → ∃ μsec₁, IsSection D.R.k D.R.rS L₁.z L₁.z' μsec₁ ∧
        ∃ K₁ : ℝ, 0 < K₁ ∧ jNorm2 L₁ f₁ μsec₁ = ENNReal.ofReal K₁ * jNorm2 L f μsec ∧
        ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 →
          ∃ γ₁ : Point ℂ (D.R.rS + 1), γ₁.1 = scaleBlocks κ τ D.R.rS 0 γ.1 ∧
            Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') γ₁ =
              κ ^ (2 * D.R.rS * (D.R.rS + 1)) * τ ^ (4 * (D.R.rS + 1)) *
                Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ∧
            ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') γ₁) * orbSq L₁ f₁ γ₁ ≤
              ENNReal.ofReal (K₁ * (max κ κ⁻¹ ^ (Cf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) *
                  max τ τ⁻¹ ^ (Cf * ((2 * D.R.rS + 2 : ℕ) : ℝ)))) *
                (ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ) * orbSq L f γ) ∧
            ENNReal.ofReal K₁ *
                (ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ) * orbSq L f γ) ≤
              ENNReal.ofReal (max κ κ⁻¹ ^ (Cf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2) *
                  max τ τ⁻¹ ^ (Cf * ((2 * D.R.rS + 2 : ℕ) : ℝ))) *
                (ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') γ₁) *
                  orbSq L₁ f₁ γ₁)

def blockHeads {K : Type*} : ℕ → List (K × ℕ) → List (ℕ × K)
  | _, [] => []
  | acc, (t, s) :: bs => (acc, t) :: blockHeads (acc + s) bs

def TheoremBIntegralityAtEnds (D : D7) : Prop :=
  ∀ (T T' : ℕ) (γ : Point D.host.E (D.R.rS + 1)), IsBPt D T T' γ →
    (∀ l ∈ blockEnds D 0 γ.1, ∀ hl : l ≤ D.R.rS + 1,
      IsIntegral ℤ (leadMinorK (ptMat γ) l hl) ∧ leadMinorK (ptMat γ) l hl ≠ 0) ∧
    ∀ p ∈ blockHeads 0 γ.1, ∀ hl : p.1 ≤ D.R.rS + 1, IsIntegral ℤ (leadMinorK (ptMat γ) p.1 hl * p.2)

def SubmultiplicativeLocalNorm (D : D7) (Ch Cg Cq C1 C2 : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b bv : ℝ) (Bf : L.Hs → L.Wp)
    (μG μS νq : Measure (Mt D.R.k D.R.rS)) (P : Mx D.R.k D.R.rS) (w : L.Hs) (j : ℕ),
    LocOk0 D Ch Cg L lam0 ka b ka →
    Cg * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 ≤ bv → ShapeS L.u lam0 bv →
    IsBesselMapSm L.z (psi D.R.k D.R.rS L.z L.c) L.σ L.π Bf →
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → IsHaarOn (Sset D.R.k D.R.rS L.z) μS → IsQuotMeas μG μS νq →
    (∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) L.σ, l2SG νq (fun g => Bf (L.σ g v)) = (‖v‖₊ : ENNReal) ^ 2) →
    IsCayleyU D.R.k D.R.rS L.ε P →
    (w ∈ shell L P j ∨ (j = 0 ∧ w ∈ lowKSub L.ε L.lam (fun g => L.σ (P⁻¹ * g * P)))) → w ≠ 0 →
    let m : ℕ := 2 * D.R.rS + 2
    let n : ℕ := 2 * D.R.rS + D.R.k + 1
    let H1 : ℝ := b ^ (C2 * m) * (1 + 1 / ka) ^ m
    let Q0 : ℝ := q0 Cq m L.ε L.u lam0
    let la := fun (a : Fin (D.R.rS + 1)) (g : Mx D.R.k D.R.rS) => lA D.R.k D.R.rS L.z g a
    (∀ q : ℕ, l1 L.lam lam0 + (q : ℝ) ≤ Q0 → (j : ℝ) + 2 * q ≤ bv / (C1 * n ^ 2) →
      Emom L Bf νq w (fun g => ENNReal.ofReal (la 0 g ^ (2 * q))) ≤ ENNReal.ofReal (H1 ^ (2 * q))) ∧
    (l1 L.lam lam0 ≤ Q0 → ∀ (q : ℕ) (a : ℕ) (ha : a < D.R.rS),
      Emom L Bf νq w (fun g => ENNReal.ofReal ((la ⟨a + 1, by omega⟩ g / la ⟨a, by omega⟩ g) ^ (2 * q))) ≤
        ENNReal.ofReal ((C1 * n ^ 2 * (b + j + q) / ka) ^ (2 * q))) ∧
    (∀ g ∈ UH (Hpk D.R.k D.R.rS), Tz D.R.k D.R.rS L.z ≤ la (Fin.last D.R.rS) g ^ 2) ∧
    (∀ q : ℕ, l1 L.lam lam0 + ((m * q : ℕ) : ℝ) ≤ Q0 → ((m * q + j : ℕ) : ℝ) ≤ bv / (C1 * n ^ 4) →
      (∀ a : Fin (D.R.rS + 1),
        Emom L Bf νq w (fun g => ENNReal.ofReal (la a g ^ (2 * q))) ≤ ENNReal.ofReal (H1 ^ (2 * q)) ∧
        Emom L Bf νq w (fun g => ENNReal.ofReal ((la a g)⁻¹ ^ (2 * q))) ≤ ENNReal.ofReal (H1 ^ (2 * q))) ∧
      ∀ lam' : ℝ, 0 < lam' →
        Emom L Bf νq w (Set.indicator {g | ∃ a : Fin (D.R.rS + 1), lam' * H1 ≤ max (la a g) (la a g)⁻¹} 1) ≤
          ENNReal.ofReal (2 * m * lam' ^ (-(2 * (q : ℝ)))))

end Formalism.MainNotions.OnePlaceEstimates

namespace Formalism.MainNotions.OnePlaceEstimates

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.S.TopsChoicePartA
open scoped ContDiff

section Cells71

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def endsC : ℕ → List (ℂ × ℕ) → List ℕ
  | _, [] => []
  | acc, (_, s) :: bs => (acc + s) :: endsC (acc + s) bs

abbrev minorsNe (Lt : Lev) (E : List ℕ) : Set (Mat Lt.k0 Lt.r) := GramWordSpace.minorsNe Lt E

abbrev IsCellOpAt (Lt : Lev) (E : List ℕ) (o : ℕ) (dP : ℝ) (Θ : Lt.GF → Lt.GF) : Prop := GramWordSpace.IsCellOpAt Lt E o dP Θ

def FrameIntegrationFormula (D : D7) (CV : ℝ) : Prop :=
  ∀ (k0 : ℕ) (_hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS) (μsec : GramWordSpace.Sec k0),
    L.c = cStd → L.κN ≠ ⊤ → IsSection (k0 + 1) D.R.rS L.z L.z' μsec →
    ∀ (γ : Point ℂ (D.R.rS + 1)) (o : ℕ) (dP : ℝ) (Θ : GramWordSpace.GFn L → GramWordSpace.GFn L),
      IsCellOpAt (GramWordSpace.levOf L μsec) (endsC 0 γ.1) o dP Θ → GramWordSpace.RadZeroC (GramWordSpace.levOf L μsec) o Θ →
      ∀ A : ℝ,
        (D.R.rS : ℝ) * (CV * ((D.R.rS : ℝ) ^ 3 * D.R.r + (D.R.r : ℝ) ^ 2 + (D.R.rS : ℝ) ^ 4)) ≤
          A - dP - 3 * ((D.R.rS : ℝ) + 1) * (CV * ((D.R.rS : ℝ) ^ 2 + 1) + o) →
        CV * ((D.R.rS : ℝ) + 1) ^ 2 * ((o : ℝ) + (D.R.rS : ℝ) * D.R.r + 1) ≤ A - 3 * ((D.R.rS : ℝ) + 1) * o →
        ∀ F : GramWordSpace.GFn L, (∀ mm : ℕ, IsCC (k0 + 1) D.R.rS (A - 3 * ((D.R.rS : ℝ) + 1) * mm) mm F) → ∀ ε : ℝ, 0 < ε →
          SuppGe (GramWordSpace.levOf L μsec) ε F →
        ∀ (g : Mx (k0 + 1) D.R.rS) (μR : Measure (Mt (k0 + 1) D.R.rS)) (ν : Measure (PairSp (k0 + 1) D.R.rS)),
          0 < Gpt (Tz (k0 + 1) D.R.rS L.z) (Tz (k0 + 1) D.R.rS L.z') γ →
          IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν → OrbInt L (Θ F) g ν = 0

def PositivityTheoremP (D : D7) (CB : ℝ) : Prop :=
  ∀ (k0 : ℕ) (_hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS) (μsec : GramWordSpace.Sec k0),
    L.c = cStd → L.κN ≠ ⊤ → IsSection (k0 + 1) D.R.rS L.z L.z' μsec →
    ∀ (A : ℝ) (mm : ℕ), Big CB (GramWordSpace.levOf L μsec) 0 A mm →
    ∀ F : GramWordSpace.GFn L, IsCC (k0 + 1) D.R.rS A mm F → ∀ ε : ℝ, 0 < ε → SuppGe (GramWordSpace.levOf L μsec) ε F →
      (∀ q : (Fin D.R.rS → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) →
        Tz (k0 + 1) D.R.rS L.z * Tz (k0 + 1) D.R.rS L.z' < Complex.normSq q.2 →
        L.J F (bigCell (k0 + 1) D.R.rS q.1 (μsec q.2)) = 0) →
      ∀ (γ : Point ℂ (D.R.rS + 1)) (g : Mx (k0 + 1) D.R.rS) (μR : Measure (Mt (k0 + 1) D.R.rS))
        (ν : Measure (PairSp (k0 + 1) D.R.rS)),
        0 < Gpt (Tz (k0 + 1) D.R.rS L.z) (Tz (k0 + 1) D.R.rS L.z') γ →
        IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν → OrbInt L F g ν = 0

def SliceBoundC (D : D7) (CB : ℝ) : Prop :=
  ∀ (k0 : ℕ) (_hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS) (μsec : GramWordSpace.Sec k0),
    L.c = cStd → IsSection (k0 + 1) D.R.rS L.z L.z' μsec →
    ∀ (j0 s : ℕ), 1 ≤ s → ∀ hj : j0 + s ≤ D.R.rS, ∃ e : ℂ, (e = 1 ∨ e = -1) ∧
      ∀ (sg : Bool) (Y : ℝ) (Θj Θi : AuxiliarySlotStates [((sg, Y) : Letter)].length → GramWordSpace.GFn L → GramWordSpace.GFn L),
        GramWordSpace.IsLetters (GramWordSpace.levOf L μsec) (j0 + s) hj [(sg, Y)] Θj →
        GramWordSpace.IsLetters (GramWordSpace.levOf L μsec) j0 (by show j0 ≤ D.R.rS; omega) [(sg, Y)] Θi →
        ∀ (A : ℝ) (mm : ℕ), Big CB (GramWordSpace.levOf L μsec) 1 A mm →
        ∀ F : GramWordSpace.GFn L, (∀ mm' : ℕ, IsCC (k0 + 1) D.R.rS (A - 3 * ((D.R.rS : ℝ) + 1) * mm') mm' F) → ∀ ε : ℝ, 0 < ε →
          SuppGe (GramWordSpace.levOf L μsec) ε F →
        ∀ (γ : Point ℂ (D.R.rS + 1)) (hb rest : List (ℂ × ℕ)) (t : ℂ),
          γ.1 = hb ++ (t, s) :: rest → (hb.map Prod.snd).sum = j0 →
          ∀ (g : Mx (k0 + 1) D.R.rS) (μR : Measure (Mt (k0 + 1) D.R.rS)) (ν : Measure (PairSp (k0 + 1) D.R.rS)),
            0 < Gpt (Tz (k0 + 1) D.R.rS L.z) (Tz (k0 + 1) D.R.rS L.z') γ →
            IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
            OrbInt L (Θj (fun _ => 1) F) g ν =
              (e * (if sg then t else star t)⁻¹) • OrbInt L (Θi (fun _ => 0) F) g ν

def adm12 (D : D7) (CB : ℝ) : Prop := FrameIntegrationFormula D CB ∧ PositivityTheoremP D CB ∧ SliceBoundC D CB

end Cells71

structure TensorDSd (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) where
  Sm : Finset (Fin n)
  Hs : Fin n → Type
  [nH : ∀ s, NormedAddCommGroup (Hs s)]
  [iH : ∀ s, InnerProductSpace ℂ (Hs s)]
  [cH : ∀ s, CompleteSpace (Hs s)]
  σs : ∀ s, Matrix (Fin n) (Fin n) ℂ → (Hs s →L[ℂ] Hs s)
  ds : ∀ s ∈ Sm, IsHCParam (μ - Pi.single s 1) ∧ IsDS ε (μ - Pi.single s 1) (σs s)
  inequiv : ∀ s ∈ Sm, ∀ s' ∈ Sm, s ≠ s' → ¬ ∃ U : Hs s ≃ₗᵢ[ℂ] Hs s',
    ∀ g ∈ UJset ε, ∀ x, U (σs s g x) = σs s' g (U x)
  toSum : ∀ (v w : H) (x y : Fin n → ℂ), IsKFin ε σ v → IsKFin ε σ w →
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, Hs (sI i)),
      (∀ i, sI i ∈ Sm ∧ IsKFin ε (σs (sI i)) (vI i) ∧ IsKFin ε (σs (sI i)) (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ g v⟫_ℂ * (star y ⬝ᵥ (g⁻¹ *ᵥ x)) = ∑ i, ⟪wI i, σs (sI i) g (vI i)⟫_ℂ
  ofSum : ∀ s ∈ Sm, ∀ v w : Hs s, IsKFin ε (σs s) v → IsKFin ε (σs s) w →
    ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → H) (xI yI : ι → Fin n → ℂ),
      (∀ i, IsKFin ε σ (vI i) ∧ IsKFin ε σ (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σs s g v⟫_ℂ = ∑ i, ⟪wI i, σ g (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (g⁻¹ *ᵥ xI i))

attribute [instance] TensorDSd.nH TensorDSd.iH TensorDSd.cH

def DualTranslationPrinciple (_D : D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∀ s : Fin n, IsHCParam (μ - Pi.single s 1)) →
      ∃ X : TensorDSd n ε μ H σ, ∀ s, s ∈ X.Sm ↔ IsHCParam (μ - Pi.single s 1)

def FormalDegreeRatioDual (_D : D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : TensorDSd n ε μ H σ),
    IsHCParam μ → IsDS ε μ σ →
    (∀ v w : H, IsKFin ε σ v → IsKFin ε σ w →
      MemLp (fun g : Formalism.REAL.UJ ε => (frob (umat g) : ℂ) * coefOn σ v w g) 2 (Formalism.REAL.muG ε)) →
    ∀ s ∈ X.Sm, ∀ (v : H) (vs : X.Hs s), v ≠ 0 → vs ≠ 0 →
      fdegOf (Formalism.REAL.muG ε) (X.σs s) vs / fdegOf (Formalism.REAL.muG ε) σ v =
        ∏ s' ∈ Finset.univ.erase s, (μ s - 1 - μ s') / (μ s - μ s')

def muSof {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) :=
  (μW.prod μN).map (fun p => fun i j => (Matrix.of p.1 * Matrix.of p.2) i j)

def atFormAtPoint {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  ∃ l : H → Wp, IsBesselMapSm z (psi k r z c) σ π l ∧
    (∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H, IsKFinHpk (k := k) (r := r) σ v →
      Integrable (fun p : Mt k r × Mt k r =>
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹)
        (μW.prod μN) ∧
      ∫ p : Mt k r × Mt k r,
        (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹
        ∂(μW.prod μN) = (innerSL ℂ (l v)).smulRight (l w)) ∧
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, w ≠ 0 → ∀ v : H, IsKFinHpk (k := k) (r := r) σ v →
      ENNReal.ofReal (‖l v‖ ^ 2) * l2SG νq (fun g => l (σ g w)) =
        ENNReal.ofReal (‖w‖ ^ 2 * ‖l v‖ ^ 2 / fdegH μG σ w)

def NearbyChamberParameters (D : D7) (Ch Cg Cq : ℝ) (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (ka b κ : ℝ) : Prop :=
  (κ = 1 ∨ κ = ka) ∧ LocOk0 D Ch Cg L lam0 ka b κ ∧ IsHCParam μ ∧
    l1 μ lam0 ≤ q0 Cq (2 * D.R.rS + 2) L.ε L.u lam0

def adm22 (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG νq νq' : Measure (Mt D.R.k D.R.rS)),
    NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ → IsDSHpk D.R.k D.R.rS L.ε μ σ →
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → IsQuotMeas μG (muSof L.μW L.μN) νq → IsQuotMeas μG (muSof L.μW' L.μN) νq' →
      atFormAtPoint L.z L.c L.π L.μW L.μN μG νq σ ∧ atFormAtPoint L.z' L.c L.π' L.μW' L.μN μG νq' σ

def trBP {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (B : H → Wp) (P : H →L[ℂ] Wp) : ℂ :=
  ∑ i, ⟪stdOrthonormalBasis ℂ Wp i, B (ContinuousLinearMap.adjoint P (stdOrthonormalBasis ℂ Wp i))⟫_ℂ

def trBQ {H Wq : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (B' : H → Wq) (Q : Wq →L[ℂ] H) : ℂ :=
  ∑ i, ⟪stdOrthonormalBasis ℂ Wq i, B' (Q (stdOrthonormalBasis ℂ Wq i))⟫_ℂ

def PieriNormPairing (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (μG νq νq' : Measure (Mt D.R.k D.R.rS)),
    IsSection D.R.k D.R.rS L.z L.z' μsec →
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → IsQuotMeas μG (muSof L.μW L.μN) νq → IsQuotMeas μG (muSof L.μW' L.μN) νq' →
    ∃ c : ℝ, 0 < c ∧
      ∀ (μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (B : H → L.Wp) (B' : H → L.Wq)
        (P : H →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] H) (w0 : H),
        NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ → IsDSHpk D.R.k D.R.rS L.ε μ σ →
        IsBesselMapSm L.z (psi D.R.k D.R.rS L.z L.c) σ L.π B →
        IsBesselMapSm L.z' (psi D.R.k D.R.rS L.z' L.c) σ L.π' B' →
        (∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) σ, l2SG νq (fun g => B (σ g v)) = (‖v‖₊ : ENNReal) ^ 2) →
        (∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) σ, l2SG νq' (fun g => B' (σ g v)) = (‖v‖₊ : ENNReal) ^ 2) →
        (∀ x, IsKFinHpk (k := D.R.k) (r := D.R.rS) σ (ContinuousLinearMap.adjoint P x)) →
        (∀ x, IsKFinHpk (k := D.R.k) (r := D.R.rS) σ (Q x)) → w0 ≠ 0 →
        jNorm2 L (fun g => P.comp ((σ g).comp Q)) μsec =
          ENNReal.ofReal (c * ‖trBP B P‖ ^ 2 * ‖trBQ B' Q‖ ^ 2 / fdegH μG σ w0 ^ 3)

end Formalism.MainNotions.OnePlaceEstimates

section ShortGrids

open Filter Topology NumberField
open scoped ContDiff ComplexOrder nonZeroDivisors

namespace Formalism.MainNotions.OnePlaceEstimates

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

def NS (D : D7) : ℕ := 3 * (D.R.rS + 1)

def StdShort {D : D7} {k0 : ℕ} (X : GramWordSpace.Dat D k0) (CB : ℝ) : Prop :=
  ∀ v,
    (X.B v).c = cStd ∧
    IsSection (k0 + 1) D.R.rS (X.B v).z (X.B v).z' (X.μsec v) ∧
    IsCutS (X.B v).u (X.B v).u' (X.I v) ∧
    ((X.B v).u (X.l v) ≠ (X.B v).u' (X.l v) ∧
      min (-(X.B v).u (X.l v)) (-(X.B v).u' (X.l v)) + 2 ≤ X.a v ∧ X.a v ≤ X.b v ∧
      X.b v ≤ max (-(X.B v).u (X.l v)) (-(X.B v).u' (X.l v)) - 2) ∧
    (∃ ρ : Fin k0 → ℝ, Interlace (X.B v).u ρ ∧ Interlace (X.B v).u' ρ) ∧
    30 * ((D.R.rS : ℝ) + 1) ^ 2 + 2 ≤ X.b v - X.a v ∧
    1 ≤ X.T v ∧ 1 ≤ X.T' v ∧
    (∃ (A : ℝ) (mm : ℕ), Big CB (GramWordSpace.levOf (X.B v) (X.μsec v)) (NS D) A mm ∧
      ∀ mm' : ℕ, IsCC (k0 + 1) D.R.rS (A - 3 * ((D.R.rS : ℝ) + 1) * mm') mm' (X.f v)) ∧
    (∀ (j : ℕ) (hj : j ≤ D.R.rS), GramWordSpace.IsRadQQd (X.lv v j hj) (X.R v j hj)) ∧
    ∀ (j : ℕ) (hj : j ≤ D.R.rS) (w : Word), GramWordSpace.IsLetters (GramWordSpace.levOf (X.B v) (X.μsec v)) j hj w (X.Th v j hj w)

def GridOK {D : D7} {k0 : ℕ} (X : GramWordSpace.Dat D k0) (y0 : D.what₂.Tau → ℝ) : Prop :=
  ∀ v, X.a v + 2 ≤ y0 v ∧ y0 v + 30 * ((D.R.rS : ℝ) + 1) ^ 2 - 2 ≤ X.b v

theorem GridOK.exists {D : D7} {k0 : ℕ} (X : GramWordSpace.Dat D k0)
    (h : ∀ v, 30 * ((D.R.rS : ℝ) + 1) ^ 2 + 2 ≤ X.b v - X.a v) : ∃ y0, GridOK X y0 := by
  exact ⟨fun v => X.a v + 2, fun v => ⟨le_refl _, by have := h v; linarith⟩⟩

def GridWd (r : ℕ) (y0 : ℝ) (w : Word) : Prop :=
  w.length ≤ 3 * (r + 1) ∧ ∀ (a : ℕ) (l : Letter), w.reverse[a]? = some l →
    ∃ n : ℕ, a * (2 * r + 2) ≤ n ∧ n < (a + 1) * (2 * r + 2) ∧ l.2 = y0 + 5 * (n : ℝ) + (if l.1 then 0 else 1)

def GridW {D : D7} {k0 : ℕ} (X : GramWordSpace.Dat D k0) (y0 : D.what₂.Tau → ℝ) (w : GramWordSpace.GWord D) : Prop :=
  ∀ v, Admissible (X.I v) (w v) ∧ GridWd D.R.rS (y0 v) (w v)

theorem gridWd_adm {r : ℕ} {y0 a b : ℝ} {w : Word} (h : GridWd r y0 w) (ha : a ≤ y0)
    (hb : y0 + 30 * ((r : ℝ) + 1) ^ 2 - 4 ≤ b) : Admissible (Set.Icc a b) w := by
  obtain ⟨hlen, hw⟩ := h
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_reverse.mpr hl)
    obtain ⟨n, -, hn2, hy⟩ := hw i l hi
    have hil : i < w.length := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      simpa using this
    have hn : n + 1 ≤ 6 * (r + 1) ^ 2 := by
      have h1 : (i + 1) * (2 * r + 2) ≤ (3 * (r + 1)) * (2 * r + 2) := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    have hnR : (n : ℝ) + 1 ≤ 6 * ((r : ℝ) + 1) ^ 2 := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [Set.mem_Icc, hy]
    constructor <;> split_ifs <;> nlinarith
  · apply List.pairwise_reverse.mp
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    obtain ⟨n, hn1, hn2, hy⟩ := hw i _ (List.getElem?_eq_getElem hi)
    obtain ⟨n', hn1', hn2', hy'⟩ := hw j _ (List.getElem?_eq_getElem hj)
    have hlt : n < n' := by
      have : (i + 1) * (2 * r + 2) ≤ j * (2 * r + 2) := Nat.mul_le_mul_right _ hij
      omega
    have hltR : (n : ℝ) + 1 ≤ n' := by exact_mod_cast hlt
    refine lt_abs.mpr (Or.inl ?_)
    rw [hy, hy']
    split_ifs <;> linarith

theorem gridW_nil {D : D7} {k0 : ℕ} (X : GramWordSpace.Dat D k0) (y0 : D.what₂.Tau → ℝ) : GridW X y0 (fun _ => []) := by
  intro v
  refine ⟨⟨fun l hl => absurd hl List.not_mem_nil, List.Pairwise.nil⟩, ⟨by simp, fun a l h => by simp at h⟩⟩

section Raw

variable {D : D7} {k0 : ℕ} (Gm : GramWordSpace.GramMap k0 D.R.rS) (X : GramWordSpace.Dat D k0) (Pst : D.what₂.Tau → ℝ → ℝ)

def brkS (w : GramWordSpace.GWord D) : ℝ := ∏ v, ((w v).map fun l => Pst v l.2).prod

def normalisedGramSum (j0 : ℕ) (w : GramWordSpace.GWord D) (χ : ℝ → ℝ) (ε : ℝ) {Hd : Type} [Fintype Hd] (hd : Hd → GramWordSpace.Head D j0)
    (κ : Hd → Hd → ℂ) : ℂ :=
  (∑ h, ∑ h', κ h h' * ∏ v, GramWordSpace.gram Gm X v j0 (w v) (X.Fv χ ε v) (hd h v) (hd h' v)) / (brkS Pst w : ℂ)

def Nss (j0 s : ℕ) (w : GramWordSpace.GWord D) (χ : ℝ → ℝ) (ε : ℝ) {Hd : Type} [Fintype Hd] (hd : Hd → GramWordSpace.Head D j0)
    (κ : Hd → Hd → ℂ) (t t' : D.what₂.Tau → ℂ) : ℂ :=
  ((∏ v, X.wt v j0 s (t v) * X.wt v j0 s (t' v) : ℝ) : ℂ) *
    (∑ h, ∑ h', κ h h' * ∏ v, GramWordSpace.gramS Gm X v j0 s (w v) (X.Fv χ ε v) (hd h v) (hd h' v) (t v) (t' v)) /
      (brkS Pst w : ℂ)

def Ntrs (j0 : ℕ) (w : GramWordSpace.GWord D) (χ : ℝ → ℝ) (ε : ℝ) {Hd : Type} [Fintype Hd] (hd : Hd → GramWordSpace.Head D j0)
    (κ : Hd → Hd → ℂ) (σ : D.what₂.Tau → ℂ) : ℂ :=
  ∫ t : D.what₂.Tau → ℂ, Nss Gm X Pst j0 1 w χ ε hd κ t t * ∏ v, fsC (σ v) (t v)

def qR (v : D.what₂.Tau) (Y : ℝ) : ℝ := (qPoly (X.T v) (X.T' v) (X.B v).u (X.B v).u' (Y : ℂ)).re

def IsGramThreshold (Cs : ℝ) (Λ : D.what₂.Tau → ℝ) : Prop :=
  ∀ v, ∀ Y ∈ X.I v,
    ((NS D : ℕ) : ℝ) ^ Cs *
      max 1 (max (Real.sqrt (Pst v Y * Pst v (Y + 1) / qR X v Y)) (Pst v Y / Real.sqrt (qR X v Y))) ≤ Λ v

def blockThresholdAtLevel (Λ : D.what₂.Tau → ℝ) (j0 s : ℕ) (v : D.what₂.Tau) : ℝ := if j0 + s ≤ D.R.rS then Λ v else 2 * Λ v

def PatS (Λ : D.what₂.Tau → ℝ) (j0 s : ℕ) (p : D.what₂.Tau → Option Bool) (t t' : D.what₂.Tau → ℂ) : Prop :=
  (∀ v, (p v).isSome ↔ blockThresholdAtLevel Λ j0 s v < ‖GramWordSpace.oDiff t t' v‖) ∧
    (j0 + s ≤ D.R.rS → ∀ v, p v ≠ some false) ∧
    (∀ v, p v = some true → j0 + s = D.R.rS + 1 → ‖GramWordSpace.oDiff t t' v‖ / 2 ≤ ‖t v‖⁻¹) ∧
    (∀ v, p v = some false → ‖GramWordSpace.oDiff t t' v‖ / 2 ≤ ‖t' v‖⁻¹)

end Raw

def PosN {D : D7} (Pst : D.what₂.Tau → ℝ → ℝ) : Prop := ∀ v Y, 0 < Pst v Y

def ShortGridGramBound (D : D7) (Gm : ∀ k0 r : ℕ, GramWordSpace.GramMap k0 r) (CB Cs : ℝ) : Prop :=
  ∀ (k0 : ℕ) (X : GramWordSpace.Dat D k0), StdShort X CB → ∀ y0 : D.what₂.Tau → ℝ, GridOK X y0 →
    ∀ j0 : ℕ, j0 ≤ D.R.rS → ∀ w : GramWordSpace.GWord D, GridW X y0 w → (∀ v, (w v).length + 3 ≤ NS D) →
    (∀ Pst : D.what₂.Tau → ℝ → ℝ, PosN Pst → ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ ε : ℝ, 0 < ε →
      ∀ (Hd : Type) [Fintype Hd] (hd : Hd → GramWordSpace.Head D j0) (κ : Hd → Hd → ℂ), PSDK κ →
        (∃ φ : (D.what₂.Tau → ℂ) → ℂ, Continuous φ ∧
          (∀ t, (∀ v, t v ≠ 0) → φ t = Nss (Gm k0 D.R.rS) X Pst j0 1 w χ ε hd κ t t) ∧
          ∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C * ∏ v, (1 + ‖t v‖) ^ (-(3 : ℝ))) ∧
        Ntrs (Gm k0 D.R.rS) X Pst j0 w χ ε hd κ 0 = normalisedGramSum (Gm k0 D.R.rS) X Pst j0 w χ ε hd κ) ∧
    ∃ θ : Set D.what₂.Tau → (GramWordSpace.GWord D →₀ ℝ),
      (∀ A, GramWordSpace.IsProb (θ A) ∧ ∀ w' ∈ (θ A).support, GramWordSpace.ExtAt 3 A w w' ∧ GridW X y0 w') ∧
      ∀ Pst : D.what₂.Tau → ℝ → ℝ, PosN Pst → ∀ Λ : D.what₂.Tau → ℝ, IsGramThreshold X Pst Cs Λ →
      ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ ε : ℝ, 0 < ε →
        ∀ (Hd : Type) [Fintype Hd] (hd : Hd → GramWordSpace.Head D j0) (κ : Hd → Hd → ℂ), PSDK κ →
        ∀ σ : D.what₂.Tau → ℂ,
          ‖Ntrs (Gm k0 D.R.rS) X Pst j0 w χ ε hd κ σ‖ ≤
            (∏ v, minFac (Λ v) ‖σ v‖ 3) *
              (θ {v | Λ v < ‖σ v‖}).sum (fun w' c => c * (normalisedGramSum (Gm k0 D.R.rS) X Pst j0 w' χ ε hd κ).re)

def LiftGridGramBound (D : D7) (Gm : ∀ k0 r : ℕ, GramWordSpace.GramMap k0 r) (CB Cs : ℝ) : Prop :=
  ∀ (k0 : ℕ) (X : GramWordSpace.Dat D k0), StdShort X CB → ∀ y0 : D.what₂.Tau → ℝ, GridOK X y0 →
    ∀ j0 s : ℕ, 1 ≤ s → (j0 + s ≤ D.R.rS ∨ (2 ≤ s ∧ j0 + s = D.R.rS + 1)) →
    ∀ w : GramWordSpace.GWord D, GridW X y0 w → (∀ v, (w v).length + 3 ≤ NS D) →
    ∃ θ : (D.what₂.Tau → Option Bool) → (GramWordSpace.GWord D × GramWordSpace.GWord D →₀ ℝ),
      (∀ p, GramWordSpace.IsProb (θ p) ∧
        ∀ q ∈ (θ p).support, GramWordSpace.ChargedPairs 3 j0 s w p q ∧ GridW X y0 q.1 ∧ GridW X y0 q.2) ∧
      ∀ Pst : D.what₂.Tau → ℝ → ℝ, PosN Pst → ∀ Λ : D.what₂.Tau → ℝ, IsGramThreshold X Pst Cs Λ →
      ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ ε : ℝ, 0 < ε →
        ∀ (Hd : Type) [Fintype Hd] (hd : Hd → GramWordSpace.Head D j0)
          (K : Hd × (D.what₂.Tau → ℂ) → Hd × (D.what₂.Tau → ℂ) → ℂ),
          PSDK K → ∀ t t' : D.what₂.Tau → ℂ, (∀ v, t v ≠ 0) → (∀ v, t' v ≠ 0) →
            ∃ p, PatS Λ j0 s p t t' ∧
              ‖Nss (Gm k0 D.R.rS) X Pst j0 s w χ ε hd (fun h h' => K (h, t) (h', t')) t t'‖ ≤
                (∏ v, minFac (blockThresholdAtLevel Λ j0 s v) ‖GramWordSpace.oDiff t t' v‖ 3) *
                  (θ p).sum (fun q c => c *
                    (((Nss (Gm k0 D.R.rS) X Pst j0 s q.1 χ ε hd (fun h h' => K (h, t) (h', t)) t t).re +
                      (Nss (Gm k0 D.R.rS) X Pst j0 s q.2 χ ε hd (fun h h' => K (h, t') (h', t')) t' t').re) / 2))

def LargeBlockGridBound (D : D7) (Gm : ∀ k0 r : ℕ, GramWordSpace.GramMap k0 r) (CB Cs C₃ : ℝ) : Prop :=
  ∀ (k0 : ℕ) (X : GramWordSpace.Dat D k0), StdShort X CB → ∀ y0 : D.what₂.Tau → ℝ, GridOK X y0 →
    ∀ j0 s : ℕ, 2 ≤ s → j0 + s ≤ D.R.rS + 1 →
    ∀ w : GramWordSpace.GWord D, GridW X y0 w → (∀ v, (w v).length + 3 * s ≤ NS D) →
    ∃ θ : GramWordSpace.GWord D →₀ ℝ, GramWordSpace.IsProb θ ∧
      (∀ w' ∈ θ.support, GramWordSpace.ExtAt (3 * s) Set.univ w w' ∧ GridW X y0 w') ∧
      ∀ Pst : D.what₂.Tau → ℝ → ℝ, PosN Pst → ∀ Λ : D.what₂.Tau → ℝ, IsGramThreshold X Pst Cs Λ →
      ∀ (aa : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (a : D.what₂.Tau → ℂ), (∀ v, a v ≠ 0) →
        1 ≤ ((FractionalIdeal.absNorm aa : ℚ) : ℝ) →
      ∀ (La : AddSubgroup (D.what₂.Tau → ℂ)) (κL : ℝ), GramWordSpace.IsLat D La κL → GramWordSpace.dualS D La ⊆ GramWordSpace.scId D a aa →
      ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ ε : ℝ, 0 < ε →
        ∀ (Hd : Type) [Fintype Hd] (hd : Hd → GramWordSpace.Head D j0) (κ : Hd → Hd → ℂ), PSDK κ →
        ∀ t₀ : D.what₂.Tau → ℂ, ∃ sv : ℝ,
          HasSum (fun z : La => Nss (Gm k0 D.R.rS) X Pst j0 s w χ ε hd κ (t₀ + z) (t₀ + z)) (sv : ℂ) ∧
          κL * sv ≤ C₃ ^ (D.R.f * s) * (∏ v, max 1 (Λ v / ‖a v‖) ^ 2) * (∏ v, Λ v ^ (2 * (s - 1))) *
            θ.sum (fun w' c => c * (normalisedGramSum (Gm k0 D.R.rS) X Pst j0 w' χ ε hd κ).re)

def UniformGridGramBound (D : D7) (Gm : ∀ k0 r : ℕ, GramWordSpace.GramMap k0 r) (CB Cs C₃ : ℝ) : Prop :=
  ∀ (k0 : ℕ) (X : GramWordSpace.Dat D k0), StdShort X CB → ∀ y0 : D.what₂.Tau → ℝ, GridOK X y0 →
    ∀ j0 s : ℕ, 1 ≤ s → j0 + s ≤ D.R.rS + 1 →
    ∀ w : GramWordSpace.GWord D, GridW X y0 w → (∀ v, (w v).length + 3 * s ≤ NS D) →
    ∃ θ : GramWordSpace.GWord D →₀ ℝ, GramWordSpace.IsProb θ ∧
      (∀ w' ∈ θ.support, GramWordSpace.ExtAt (3 * s) Set.univ w w' ∧ GridW X y0 w') ∧
      ∀ Pst : D.what₂.Tau → ℝ → ℝ, PosN Pst → ∀ Λ : D.what₂.Tau → ℝ, IsGramThreshold X Pst Cs Λ →
      ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ ε : ℝ, 0 < ε →
        ∀ (Hd : Type) [Fintype Hd] (hd : Hd → GramWordSpace.Head D j0) (κ : Hd → Hd → ℂ), PSDK κ →
        ∀ t : D.what₂.Tau → ℂ, (∀ v, t v ≠ 0) →
          (Nss (Gm k0 D.R.rS) X Pst j0 s w χ ε hd κ t t).re ≤ C₃ ^ (D.R.f * s) * (∏ v, Λ v ^ (2 * s)) *
            θ.sum (fun w' c => c * (normalisedGramSum (Gm k0 D.R.rS) X Pst j0 w' χ ε hd κ).re)

end Formalism.MainNotions.OnePlaceEstimates

end ShortGrids

namespace Formalism.MainNotions.OnePlaceEstimates

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR
open Filter Topology
open scoped ContDiff

export Formalism.MainNotions.S.UnitaryLevelOperators (Jop scalMat mulAfter Op4 op4Mul tens1 tens2 RhOp modL JL fsFun Umat levOf haarOf cutF
  energy Msq mm minv mdet psiC psiLow psiUp lowOf upOf sdScale muLow muUp stabU muStab IsOrbMeas OmG gTC gZW
  fNorm)

def adm1 (_D : D7) (CB : ℝ) : Prop := LemmaB CB

def adm2 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_gauge

def CapelliEigenvalueAlt (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stCapEig

def adm3a (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanTopCondition

def adm3b (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_signs

def adm3 (D : D7) : Prop := adm3a D ∧ adm3b D

def ArithmeticRiemannRochThetaCond (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stLetters

def RTTRelation (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_rtt

def ArchimedeanSignatureMatching (D : D7) : Prop := ArithmeticRiemannRochThetaCond D ∧ RTTRelation D

def adm5 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_det

def HeckeCorrespondenceReflex (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_tele

def TorsionSectionsReflex (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_entry

def adm6 (D : D7) : Prop := HeckeCorrespondenceReflex D ∧ TorsionSectionsReflex D

def TelescopingFormStatement (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_dual C

def ConjugateSelfDualCharacter (_D : Formalism.BasicNotions.D7) (C Co Cd : ℝ) : Prop := 0 < Co ∧ S.UnitaryLevelOperators.stDualList C Co Cd

def adm7 (D : D7) (CB Co Cd : ℝ) : Prop := TelescopingFormStatement D CB ∧ ConjugateSelfDualCharacter D CB Co Cd

def DualityInequality (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stWaveLetters

def DualityForLists (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanWaveCondition

def adm8 (D : D7) : Prop := DualityInequality D ∧ DualityForLists D

def IntegrationByPartsAlt (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stE C

def LogThetaIdentity (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stD C

def adm9 (D : D7) (CB : ℝ) : Prop := IntegrationByPartsAlt D CB ∧ LogThetaIdentity D CB

def adm10 (D : Formalism.BasicNotions.D7) (C0 CA : ℝ) : Prop := S.UnitaryLevelOperators.stLemE' D C0 CA

def GermStatement (C₁ C₂ : ℝ) : Prop := S.UnitaryLevelOperators.stGerm C₁ C₂

def adm11 (_D : D7) (C₁ C₂ : ℝ) : Prop := GermStatement C₁ C₂

def adm18 (_D : D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → (∀ s : Fin n, IsHCParam (μ + Pi.single s 1)) →
      ∃ X : TensorDS n ε μ H σ, ∀ s, s ∈ X.Sm ↔ IsHCParam (μ + Pi.single s 1)

def adm19 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stJSZ

def adm20 (_D : D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam lam → IsDS ε lam σ →
      (∃ S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S ∧
        ∀ S' : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S' → S' = S) ∧
      ∀ (a b : Fin n), a < b → ε a ≠ ε b → ∀ S : Submodule ℂ H, ¬ IsKTypeOf ε σ (lowK ε lam - Formalism.REAL.root a b) S

def adm21 (D : D7) (c C₁ : ℝ) : Prop := S.UnitaryLevelOperators.stDecay D c C₁

abbrev GM := ∀ k0 r : ℕ, GramWordSpace.GramMap k0 r

def adm13 (D : D7) (Gm : GM) (Ks : ℕ) (E₀ Eg E₁ E₂ : ℝ) : Prop :=
  ∀ k0 : ℕ, GramWordSpace.SingleLevelGramEstimate D (Gm k0 D.R.rS) Ks E₀ Eg E₁ E₂

def adm15 (D : D7) (Gm : GM) (Ks : ℕ) (E₀ Eg E₁ E₂ : ℝ) : Prop :=
  ∀ k0 : ℕ, GramWordSpace.BlockLiftEstimate D (Gm k0 D.R.rS) Ks E₀ Eg E₁ E₂

def adm17 (D : D7) (Gm : GM) (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ : ℝ) : Prop :=
  ∀ k0 : ℕ, GramWordSpace.LargeBlockLiftEstimate D (Gm k0 D.R.rS) Ks E₀ Eg E₁ E₂ E₃

def admitted (D : D7) (Gm : GM) (CB Co Cd C0 CA Cg₁ Cg₂ c C₁ : ℝ) (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ Cs C₃ Ch Cg Cq : ℝ) : Prop :=
  adm1 D CB ∧ adm2 D ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D CB Co Cd ∧ adm8 D ∧ adm9 D CB ∧ adm10 D C0 CA ∧
    adm11 D Cg₁ Cg₂ ∧ adm12 D CB ∧ adm13 D Gm Ks E₀ Eg E₁ E₂ ∧ adm15 D Gm Ks E₀ Eg E₁ E₂ ∧ adm17 D Gm Ks E₀ Eg E₁ E₂ E₃ ∧
    ShortGridGramBound D Gm CB Cs ∧ LiftGridGramBound D Gm CB Cs ∧ LargeBlockGridBound D Gm CB Cs C₃ ∧ UniformGridGramBound D Gm CB Cs C₃ ∧
    adm18 D ∧ DualTranslationPrinciple D ∧ adm19 D ∧ adm20 D ∧ adm21 D c C₁ ∧ adm22 D Ch Cg Cq ∧ CapelliEigenvalueAlt D

def aux₃ (D : D7) (Ch Aw Cu Cg Cq Cg' C1 C2 Cb secondBesselConstant Cgf Cf : ℝ) : Prop :=
  TheoremBPrimePointwise D Ch Cg Cb ∧ RotatedSumBound D Ch Cg Cb ∧ PathWeightComponents D secondBesselConstant ∧ ConclusionB3 D Aw Ch Cg Cb ∧ FormalDegreeRatioAlt D ∧
    BesselLeadingMinorBound D Ch Cg Cq Cb ∧ BesselDerivativeIteration D Ch Cg Cq Cb ∧ BesselExpansionCoefficientSum D Ch Cg Cq Cb ∧
    UniformityTheoremBPrime D Ch Cu Cg Cg' Cb ∧ UniformityTheoremB D Aw Ch Cu Cg Cg' Cb ∧ SubmultiplicativeLocalNorm D Ch Cg Cq C1 C2 ∧
    TheoremBIntegralityAtEnds D ∧ FrameBesselBound D Cgf Cf ∧ BesselExpansionCoefficients D Ch Cg Cq Cb ∧ FormalDegreeRatioDual D ∧ PieriNormPairing D Ch Cg Cq ∧
    BesselIterationNearParameter D Ch Cg Cq Cb ∧ BesselExpansionNearParameter D Ch Cg Cq Cb ∧ BesselConjugatesEveryCell D Ch Cg Cq Cb

def Stmt (D : D7) (Gm : GM) (CB Co Cd C0 CA Cg₁ Cg₂ c C₁ : ℝ) (Ks : ℕ)
    (E₀ Eg E₁ E₂ E₃ Cs C₃ Ch Aw Cu Cg Cq Cg' C1 C2 Cb secondBesselConstant Cgf Cf : ℝ) : Prop :=
  admitted D Gm CB Co Cd C0 CA Cg₁ Cg₂ c C₁ Ks E₀ Eg E₁ E₂ E₃ Cs C₃ Ch Cg Cq →
    aux₃ D Ch Aw Cu Cg Cq Cg' C1 C2 Cb secondBesselConstant Cgf Cf

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def admF1 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm1 (Fm.D x i) CB
def admF2 : Prop := ∀ x (i : Fm.Ix x), adm2 (Fm.D x i)
def admF3 : Prop := ∀ x (i : Fm.Ix x), adm3 (Fm.D x i)
def admF4 : Prop := ∀ x (i : Fm.Ix x), ArchimedeanSignatureMatching (Fm.D x i)
def admF5 : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i)
def admF6 : Prop := ∀ x (i : Fm.Ix x), adm6 (Fm.D x i)
def admF7 (CB Co Cd : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm7 (Fm.D x i) CB Co Cd
def admF8 : Prop := ∀ x (i : Fm.Ix x), adm8 (Fm.D x i)
def admF9 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm9 (Fm.D x i) CB
def FamilyRowsCountHypothesis (C0 CA : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm10 (Fm.D x i) C0 CA
def FamilyWeylAndVandermonde (Cg₁ Cg₂ : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm11 (Fm.D x i) Cg₁ Cg₂
def FamilyTwelfthHypothesis (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm12 (Fm.D x i) CB
def FamilyThirteenthHypothesis (Gm : GM) (Ks : ℕ) (E₀ Eg E₁ E₂ : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm13 (Fm.D x i) Gm Ks E₀ Eg E₁ E₂
def FamilyFifteenthHypothesis (Gm : GM) (Ks : ℕ) (E₀ Eg E₁ E₂ : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm15 (Fm.D x i) Gm Ks E₀ Eg E₁ E₂
def FamilyStationaryPhase (Gm : GM) (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm17 (Fm.D x i) Gm Ks E₀ Eg E₁ E₂ E₃
def FamilyShortGridGramBound (Gm : GM) (CB Cs : ℝ) : Prop := ∀ x (i : Fm.Ix x), ShortGridGramBound (Fm.D x i) Gm CB Cs
def FamilyLiftGridBound (Gm : GM) (CB Cs : ℝ) : Prop := ∀ x (i : Fm.Ix x), LiftGridGramBound (Fm.D x i) Gm CB Cs
def FamilyShortGridBound (Gm : GM) (CB Cs C₃ : ℝ) : Prop := ∀ x (i : Fm.Ix x), LargeBlockGridBound (Fm.D x i) Gm CB Cs C₃
def FamilyUniformGridBound (Gm : GM) (CB Cs C₃ : ℝ) : Prop := ∀ x (i : Fm.Ix x), UniformGridGramBound (Fm.D x i) Gm CB Cs C₃
def FamilyBesselUniqueness : Prop := ∀ x (i : Fm.Ix x), adm18 (Fm.D x i)
def FamilyDualTranslationPrinciple : Prop := ∀ x (i : Fm.Ix x), DualTranslationPrinciple (Fm.D x i)
def FamilyNineteenthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm19 (Fm.D x i)
def FamilyTwentiethHypothesis : Prop := ∀ x (i : Fm.Ix x), adm20 (Fm.D x i)
def FamilyTwentyFirstHypothesis (c C₁ : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm21 (Fm.D x i) c C₁
def FamilyTwentySecondHypothesis (Ch Cg Cq : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm22 (Fm.D x i) Ch Cg Cq
def FamilyDualHypothesis : Prop := ∀ x (i : Fm.Ix x), CapelliEigenvalueAlt (Fm.D x i)

def AdmF (Gm : GM) (CB Co Cd C0 CA Cg₁ Cg₂ c C₁ : ℝ) (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ Cs C₃ Ch Cg Cq : ℝ) : Prop :=
  admF1 Fm CB ∧ admF2 Fm ∧ admF3 Fm ∧ admF4 Fm ∧ admF5 Fm ∧ admF6 Fm ∧ admF7 Fm CB Co Cd ∧ admF8 Fm ∧ admF9 Fm CB ∧
    FamilyRowsCountHypothesis Fm C0 CA ∧ FamilyWeylAndVandermonde Fm Cg₁ Cg₂ ∧ FamilyTwelfthHypothesis Fm CB ∧ FamilyThirteenthHypothesis Fm Gm Ks E₀ Eg E₁ E₂ ∧ FamilyFifteenthHypothesis Fm Gm Ks E₀ Eg E₁ E₂ ∧
    FamilyStationaryPhase Fm Gm Ks E₀ Eg E₁ E₂ E₃ ∧ FamilyShortGridGramBound Fm Gm CB Cs ∧ FamilyLiftGridBound Fm Gm CB Cs ∧ FamilyShortGridBound Fm Gm CB Cs C₃ ∧
    FamilyUniformGridBound Fm Gm CB Cs C₃ ∧ FamilyBesselUniqueness Fm ∧ FamilyDualTranslationPrinciple Fm ∧ FamilyNineteenthHypothesis Fm ∧ FamilyTwentiethHypothesis Fm ∧ FamilyTwentyFirstHypothesis Fm c C₁ ∧ FamilyTwentySecondHypothesis Fm Ch Cg Cq ∧
    FamilyDualHypothesis Fm

def FamilyTheoremBPrime (Ch Cg Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), TheoremBPrimePointwise (Fm.D x i) Ch Cg Cb
def FamilyTheoremBFirstBound (Ch Cg Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), RotatedSumBound (Fm.D x i) Ch Cg Cb
def FamilyTheoremBSecondBound (secondBesselConstant : ℝ) : Prop := ∀ x (i : Fm.Ix x), PathWeightComponents (Fm.D x i) secondBesselConstant
def FamilyTheoremBWeighted (Aw Ch Cg Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), ConclusionB3 (Fm.D x i) Aw Ch Cg Cb
def FamilyBesselFormulas : Prop := ∀ x (i : Fm.Ix x), FormalDegreeRatioAlt (Fm.D x i)
def FamilyLeadingMinorBound (Ch Cg Cq Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), BesselLeadingMinorBound (Fm.D x i) Ch Cg Cq Cb
def FamilyBesselIterationBound (Ch Cg Cq Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), BesselDerivativeIteration (Fm.D x i) Ch Cg Cq Cb
def FamilyBesselExtended (Ch Cg Cq Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), BesselExpansionCoefficientSum (Fm.D x i) Ch Cg Cq Cb
def FamilyUniformityTheoremBPrime (Ch Cu Cg Cg' Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), UniformityTheoremBPrime (Fm.D x i) Ch Cu Cg Cg' Cb
def FamilyUniformityTheoremB (Aw Ch Cu Cg Cg' Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), UniformityTheoremB (Fm.D x i) Aw Ch Cu Cg Cg' Cb
def FamilySubmultiplicativeNorm (Ch Cg Cq C1 C2 : ℝ) : Prop := ∀ x (i : Fm.Ix x), SubmultiplicativeLocalNorm (Fm.D x i) Ch Cg Cq C1 C2
def FamilyTheoremBIntegrality : Prop := ∀ x (i : Fm.Ix x), TheoremBIntegralityAtEnds (Fm.D x i)
def FamilyFrameBesselBound (Cgf Cf : ℝ) : Prop := ∀ x (i : Fm.Ix x), FrameBesselBound (Fm.D x i) Cgf Cf
def FamilyBesselConjugateCells (Ch Cg Cq Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), BesselExpansionCoefficients (Fm.D x i) Ch Cg Cq Cb
def FamilyFormalDegreeRatioDual : Prop := ∀ x (i : Fm.Ix x), FormalDegreeRatioDual (Fm.D x i)
def FamilyPieriNormPairing (Ch Cg Cq : ℝ) : Prop := ∀ x (i : Fm.Ix x), PieriNormPairing (Fm.D x i) Ch Cg Cq
def FamilyBesselRangeCells (Ch Cg Cq Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), BesselIterationNearParameter (Fm.D x i) Ch Cg Cq Cb
def FamilyBesselExpansionNear (Ch Cg Cq Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), BesselExpansionNearParameter (Fm.D x i) Ch Cg Cq Cb
def FamilyBesselConjugateAll (Ch Cg Cq Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), BesselConjugatesEveryCell (Fm.D x i) Ch Cg Cq Cb

def FamilyTargetsAtConstants (Ch Aw Cu Cg Cq Cg' C1 C2 Cb secondBesselConstant Cgf Cf : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), aux₃ (Fm.D x i) Ch Aw Cu Cg Cq Cg' C1 C2 Cb secondBesselConstant Cgf Cf

def FamilyStatementAtConstants (Gm : GM) (CB Co Cd C0 CA Cg₁ Cg₂ c C₁ : ℝ) (Ks : ℕ)
    (E₀ Eg E₁ E₂ E₃ Cs C₃ Ch Aw Cu Cg Cq Cg' C1 C2 Cb secondBesselConstant Cgf Cf : ℝ) : Prop :=
  AdmF Fm Gm CB Co Cd C0 CA Cg₁ Cg₂ c C₁ Ks E₀ Eg E₁ E₂ E₃ Cs C₃ Ch Cg Cq →
    FamilyTargetsAtConstants Fm Ch Aw Cu Cg Cq Cg' C1 C2 Cb secondBesselConstant Cgf Cf

end Family

def UniformExportStatement : Prop :=
  ∀ (Gm : GM) (CB Co Cd C0 CA Cg₁ Cg₂ c C₁ : ℝ) (Ks : ℕ) (E₀ Eg E₁ E₂ E₃ Cs C₃ Ch Aw : ℝ),
    ∃ C2 Cb secondBesselConstant Cf Cq₀ C1₀ Cgf₀ : ℝ, ∀ Cq ≥ Cq₀, ∃ Cg₀ : ℝ, ∀ Cu : ℝ, ∃ Cg'₀ : ℝ,
      ∀ Cg ≥ Cg₀, ∀ Cg' ≥ Cg'₀, ∀ C1 ≥ C1₀, ∀ Cgf ≥ Cgf₀, ∀ D : D7,
        Stmt D Gm CB Co Cd C0 CA Cg₁ Cg₂ c C₁ Ks E₀ Eg E₁ E₂ E₃ Cs C₃ Ch Aw Cu Cg Cq Cg' C1 C2 Cb secondBesselConstant Cgf Cf

end Formalism.MainNotions.OnePlaceEstimates
