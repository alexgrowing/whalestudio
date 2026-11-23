import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselLine

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine

def SideHyp (D : D7) (Ch Cg Cq : ℝ) (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (ka b κ : ℝ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG : Measure (Mt D.R.k D.R.rS))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (u : Fin D.R.k → ℝ)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mx D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (μW νq : Measure (Mt D.R.k D.R.rS)) : Prop :=
  NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ ∧ IsDSHpk D.R.k D.R.rS L.ε μ σ ∧
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG ∧
    (inWb D.R.k D.R.rS z ∧ 0 < Tz D.R.k D.R.rS z) ∧ IsHCTypeW D.R.k D.R.rS z u π ∧
    (IsHaarOn (UWset D.R.k D.R.rS z) μW ∧ μW Set.univ = 1) ∧
    IsQuotMeas μG (muSof μW L.μN) νq

def PartA {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (l : H → Wp) : Prop :=
  ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ v : H, IsKFinHpk (k := k) (r := r) σ v →
    Integrable (fun p : Mt k r × Mt k r =>
      (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹)
      (μW.prod μN) ∧
    ∫ p : Mt k r × Mt k r,
      (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹
      ∂(μW.prod μN) = (innerSL ℂ (l v)).smulRight (l w)

def PartB {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (μG νq : Measure (Mt k r)) (σ : Mx k r → (H →L[ℂ] H)) (l : H → Wp) : Prop :=
  ∀ w ∈ smoothVecs (k := k) (r := r) σ, w ≠ 0 → ∀ v : H, IsKFinHpk (k := k) (r := r) σ v →
    ENNReal.ofReal (‖l v‖ ^ 2) * l2SG νq (fun g => l (σ g w)) =
      ENNReal.ofReal (‖w‖ ^ 2 * ‖l v‖ ^ 2 / fdegH μG σ w)

def StepA (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG : Measure (Mt D.R.k D.R.rS))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (u : Fin D.R.k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mx D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (μW νq : Measure (Mt D.R.k D.R.rS)),
    SideHyp D Ch Cg Cq L lam0 μ ka b κ σ μG z u π μW νq →
      haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
      ∃ l : H → Wp, IsBesselMapSm z (psi D.R.k D.R.rS z L.c) σ π l ∧ PartA z L.c π μW L.μN σ l

def StepB (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG : Measure (Mt D.R.k D.R.rS))
    (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (u : Fin D.R.k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : Mx D.R.k D.R.rS → (Wp →L[ℂ] Wp)) (μW νq : Measure (Mt D.R.k D.R.rS)),
    SideHyp D Ch Cg Cq L lam0 μ ka b κ σ μG z u π μW νq →
      haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
      ∀ l : H → Wp, IsBesselMapSm z (psi D.R.k D.R.rS z L.c) σ π l → PartA z L.c π μW L.μN σ l →
        PartB μG νq σ l

def Eventually (P : D7 → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ Ch Cq : ℝ, ∃ Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7, P D Ch Cg Cq

theorem Eventually.and {P Q : D7 → ℝ → ℝ → ℝ → Prop} (hP : Eventually P) (hQ : Eventually Q) :
    Eventually (fun D Ch Cg Cq => P D Ch Cg Cq ∧ Q D Ch Cg Cq) := by
  intro Ch Cq
  obtain ⟨a, ha⟩ := hP Ch Cq
  obtain ⟨b, hb⟩ := hQ Ch Cq
  exact ⟨max a b, fun Cg h D => ⟨ha Cg (le_trans (le_max_left _ _) h) D, hb Cg (le_trans (le_max_right _ _) h) D⟩⟩

theorem Eventually.mono {P Q : D7 → ℝ → ℝ → ℝ → Prop} (hP : Eventually P)
    (h : ∀ D Ch Cg Cq, P D Ch Cg Cq → Q D Ch Cg Cq) : Eventually Q := by
  intro Ch Cq
  obtain ⟨a, ha⟩ := hP Ch Cq
  exact ⟨a, fun Cg hc D => h _ _ _ _ (ha Cg hc D)⟩

end PI.WBL
