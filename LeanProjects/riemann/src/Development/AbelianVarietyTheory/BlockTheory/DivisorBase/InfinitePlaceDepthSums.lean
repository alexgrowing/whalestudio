import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.HarderNarasimhan.StatementPl
import Formalism.HarderNarasimhan.QuotRealize
import Formalism.PairingDivisors.StatementH

open Module NumberField IsDedekindDomain
open scoped Matrix MatrixOrder ComplexOrder
open Formalism.L2.Indef Formalism.DivisionValues Formalism.PairingDivisionLocalBalance Formalism.HN

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums

def numL (x ε : ℝ) : ℝ := x ^ ε

def numB (x ε : ℝ) : ℝ := Real.exp (numL x ε)

def numLa (E : Type) [Field E] [NumberField E] (x ε : ℝ) : ℝ :=
  Real.log (x * numB x ε * rootDiscr E)

def numF (E : Type) [Field E] [NumberField E] : ℕ := finrank ℚ (maximalRealSubfield E)

def numN (k m t : ℕ) : ℕ := k + m * (t + (k + m + 5) + 1)

def depthSum {E : Type} [Field E] [NumberField E]
    (S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))))
    (e : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ) : ℝ :=
  ∑ v ∈ S0, (e v : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)

def formFrame {K : Type} [Field K] [NumberField K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) :
    Matrix (Fin n) (Fin n) ℂ :=
  (CFC.sqrt (H.map v.embedding))⁻¹

theorem formFrame_spec {K : Type} [Field K] [NumberField K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (v : InfinitePlace K) (h : (H.map v.embedding).PosDef) :
    IsUnit (formFrame H v).det ∧
      ((formFrame H v)⁻¹).conjTranspose * (formFrame H v)⁻¹ = H.map v.embedding := by
  unfold formFrame
  generalize H.map v.embedding = A at h
  have h0 : 0 ≤ A := h.posSemidef.nonneg
  have h1 : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A h0
  have hd : IsUnit (CFC.sqrt A).det := by
    have : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 h.isUnit
    rw [← h1, Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have hh : (CFC.sqrt A).conjTranspose = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg A)).isHermitian
  refine ⟨Matrix.isUnit_nonsing_inv_det _ hd, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv _ hd, hh, h1]

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def logNormV_sq (Df : DefSide Bs) {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K)) (v : InfinitePlace K) : ℝ :=
  Real.log (opNormAt (Pi.basisFun K (Fin (Df.nV Bs.μ0))) (formFrame (Df.HV Bs.μ0))
    (Pi.basisFun K (Fin a)).dualBasis (dualFrame XM) v vm ^ 2)

def rowFrame (S : IndefData Df) (v : InfinitePlace K) : Matrix (Fin S.D) (Fin S.D) ℂ :=
  ((Real.sqrt (S.κ v) : ℝ) : ℂ) • S.XE v

def logNormPsi_sq (S : IndefData Df) {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (Ψ : (Fin S.D → K) →ₗ[K] Module.Dual K (Fin a → K)) (v : InfinitePlace K) : ℝ :=
  Real.log (opNormAt (Pi.basisFun K (Fin S.D)) (rowFrame S)
    (Pi.basisFun K (Fin a)).dualBasis (dualFrame XM) v Ψ ^ 2)

open Classical in

def occurring (Df : DefSide Bs) : Finset Bs.Ix := Finset.univ.filter fun p => Df.Qp Bs.μ0 p ≠ ⊥

theorem occurring_nonempty (hW : Df.WF) (hp : Df.Pos) : (occurring Df).Nonempty := by
  by_contra hne
  have hall : ∀ p, Df.Qp Bs.μ0 p = ⊥ := by
    intro p
    by_contra h
    exact hne ⟨p, by simp [occurring, h]⟩
  have htop := hW.Qp_top
  simp only [hall, iSup_bot] at htop
  have : Nonempty (Fin (Df.dQ Bs.μ0)) := ⟨⟨0, hp⟩⟩
  exact bot_ne_top htop

def lamMin (hW : Df.WF) (S : IndefRows Df) (v : InfinitePlace K) : ℝ :=
  (occurring Df).inf' (occurring_nonempty hW S.pos) fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)

def TestMap (Df : DefSide Bs) {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K)) : Prop :=
  (∀ v, IsUnit (XM v).det) ∧ LinearMap.ker vm = Df.U Bs.μ0

def Factors (S : IndefData Df) {a : ℕ}
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K))
    (Ψ : (Fin S.D → K) →ₗ[K] Module.Dual K (Fin a → K)) : Prop :=
  ∀ F, Ψ ((S.ι Bs.μ0).mulVec ((Df.Pq Bs.μ0).mulVec F)) = vm F

def NormComparison (hW : Df.WF) (S : IndefRows Df) {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K))
    (Ψ : (Fin S.D → K) →ₗ[K] Module.Dual K (Fin a → K)) : Prop :=
  ∀ v, logNormPsi_sq S.toIndefData XM Ψ v ≤ logNormV_sq Df XM vm v - lamMin hW S v

def MeanNormBound (Df : DefSide Bs) {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K)) (C f m N b L Sig : ℝ) : Prop :=
  meanInf K (logNormV_sq Df XM vm) ≤ C * f * m * N * b * L + C * m ^ 2 * N ^ 2 * Sig

def ScalarLowerBound (hW : Df.WF) (S : IndefRows Df) (C f m N L La : ℝ) : Prop :=
  -(C * f * m * N ^ 2 * La) ≤ meanInf K (lamMin hW S) ∧
  -(3 * C * f * m * N ^ 2 * L) ≤ -(C * f * m * N ^ 2 * La) ∧
  ∀ v, -(C * f * m * N ^ 2 * La) ≤ lamMin hW S v

def MeanBounds (C : ℝ) [IsTotallyComplex K] (hW : Df.WF) (S : IndefRows Df)
    {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K))
    (E : Type) [Field E] [NumberField E] [IsCMField E]
    (S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))))
    (e : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ) (k t : ℕ) (x ε : ℝ) : Prop :=
  1 ≤ x → TestMap Df XM vm →
    MeanNormBound Df XM vm C (numF E) (Fintype.card Bs.J) (numN k (Fintype.card Bs.J) t)
      (numB x ε) (numL x ε) (depthSum S0 e) ∧
    ScalarLowerBound hW S C (numF E) (Fintype.card Bs.J) (numN k (Fintype.card Bs.J) t)
      (numL x ε) (numLa E x ε)

def InfinitePlaces (C : ℝ) [IsTotallyComplex K] (hW : Df.WF) (S : IndefRows Df)
    {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K))
    (Ψ : (Fin S.D → K) →ₗ[K] Module.Dual K (Fin a → K))
    (E : Type) [Field E] [NumberField E] [IsCMField E]
    (S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))))
    (e : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ) (k t : ℕ) (x ε : ℝ) : Prop :=
  (TestMap Df XM vm → Factors S.toIndefData vm Ψ → NormComparison hW S XM vm Ψ) ∧
    MeanBounds C hW S XM vm E S0 e k t x ε

theorem le_lamMin (hW : Df.WF) (S : IndefRows Df) (v : InfinitePlace K) (c : ℝ)
    (h : ∀ p, Df.Qp Bs.μ0 p ≠ ⊥ → c ≤ ∑ j, Real.log (S.lam j Bs.μ0 p v)) : c ≤ lamMin hW S v := by
  classical
  refine Finset.le_inf' _ _ fun p hp => h p ?_
  simpa [occurring] using hp

theorem numLa_eq (E : Type) [Field E] [NumberField E] {x : ℝ} (ε : ℝ) (hx : 0 < x) :
    numLa E x ε = numL x ε + Real.log x + Real.log (rootDiscr E) := by
  have hr : 0 < rootDiscr E := Real.rpow_pos_of_pos (by exact_mod_cast abs_pos.2 (discr_ne_zero E)) _
  have hb : 0 < numB x ε := Real.exp_pos _
  rw [numLa, Real.log_mul (mul_pos hx hb).ne' hr.ne', Real.log_mul hx.ne' hb.ne', numB, Real.log_exp]
  ring

example : numN 6 2 3 = 6 + 2 * (3 + ((6 + 2 - 1) + 6) + 1) := by decide

end GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums
