import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.Development

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine

section Generic

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

def beF (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (w v : H) (p : Mt k r × Mt k r) : Wp →L[ℂ] Wp :=
  (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹

def be (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w v : H) : Wp →L[ℂ] Wp :=
  ∫ p, beF z c π σ w v p ∂(μW.prod μN)

def hsSq [FiniteDimensional ℂ Wp] (A : Wp →L[ℂ] Wp) : ℝ :=
  ∑ i, ‖A (stdOrthonormalBasis ℂ Wp i)‖ ^ 2

def trW [FiniteDimensional ℂ Wp] (A : Wp →L[ℂ] Wp) : ℂ :=
  ∑ i, ⟪stdOrthonormalBasis ℂ Wp i, A (stdOrthonormalBasis ℂ Wp i)⟫_ℂ

def ConvAt (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  (∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H, IsKFinHpk (k := k) (r := r) σ v →
      Integrable (beF z c π σ w v) (μW.prod μN)) ∧
    (∀ v : H, IsKFinHpk (k := k) (r := r) σ v → ∀ x : Wp,
      IsCWCont (k := k) (r := r) σ (fun w => be z c π μW μN σ w v x)) ∧
    (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r, ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H,
      IsKFinHpk (k := k) (r := r) σ v →
      be z c π μW μN σ (σ (h * m) w) v = (psi k r z c m • π h).comp (be z c π μW μN σ w v)) ∧
    (∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v ∈ smoothVecs (k := k) (r := r) σ,
      IsKFinHpk (k := k) (r := r) σ w → IsKFinHpk (k := k) (r := r) σ v →
      ContinuousLinearMap.adjoint (be z c π μW μN σ w v) = be z c π μW μN σ v w)

def Mult1At (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H)) :
    Prop :=
  ∀ B₁ B₂ : H → Wp, IsBesselMapSm z (psi k r z c) σ π B₁ → IsBesselMapSm z (psi k r z c) σ π B₂ →
    (∃ w ∈ smoothVecs (k := k) (r := r) σ, B₂ w ≠ 0) →
    ∃ a : ℂ, ∀ w ∈ smoothVecs (k := k) (r := r) σ, B₁ w = a • B₂ w

def KDenseAt (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H)) :
    Prop :=
  ∀ B : H → Wp, IsBesselMapSm z (psi k r z c) σ π B → (∀ v : H, IsKFinHpk (k := k) (r := r) σ v → B v = 0) →
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, B w = 0

def FSAt [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG νq : Measure (Mt k r)) (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  ∀ w ∈ smoothVecs (k := k) (r := r) σ, w ≠ 0 → 0 < fdegH μG σ w ∧
    (∀ᵐ x ∂νq, σ (Matrix.of x) w ∈ smoothVecs (k := k) (r := r) σ) ∧
    ∀ v ∈ smoothVecs (k := k) (r := r) σ, IsKFinHpk (k := k) (r := r) σ v →
      Integrable (fun x => hsSq (be z c π μW μN σ (σ (Matrix.of x) w) v)) νq ∧
      ∫ x, hsSq (be z c π μW μN σ (σ (Matrix.of x) w) v) ∂νq =
        ‖w‖ ^ 2 * (trW (be z c π μW μN σ v v)).re / fdegH μG σ w

end Generic

def Conv (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG : Measure (Mt D.R.k D.R.rS))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (u : Fin D.R.k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mx D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (μW νq : Measure (Mt D.R.k D.R.rS)),
    SideHyp D Ch Cg Cq L lam0 μ ka b κ σ μG z u π μW νq →
      haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
      ConvAt z L.c π μW L.μN σ

def Mult1 (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG : Measure (Mt D.R.k D.R.rS))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (u : Fin D.R.k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mx D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (μW νq : Measure (Mt D.R.k D.R.rS)),
    SideHyp D Ch Cg Cq L lam0 μ ka b κ σ μG z u π μW νq →
      haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
      Mult1At z L.c π σ

def KDense (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG : Measure (Mt D.R.k D.R.rS))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (u : Fin D.R.k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mx D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (μW νq : Measure (Mt D.R.k D.R.rS)),
    SideHyp D Ch Cg Cq L lam0 μ ka b κ σ μG z u π μW νq →
      haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
      KDenseAt z L.c π σ

def FS (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG : Measure (Mt D.R.k D.R.rS))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (u : Fin D.R.k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mx D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (μW νq : Measure (Mt D.R.k D.R.rS)),
    SideHyp D Ch Cg Cq L lam0 μ ka b κ σ μG z u π μW νq →
      haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
      FSAt z L.c π μW L.μN μG νq σ

end PI.WBL
