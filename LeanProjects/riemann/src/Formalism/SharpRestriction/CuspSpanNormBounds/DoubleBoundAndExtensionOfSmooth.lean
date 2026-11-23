import Formalism.SharpRestriction.CuspSpanNormBounds.BesselBoundFamilyOfDoubleCoset

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.DoubleDerivativeSmoothness

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

section Side

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

def FI (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (u v : H) : Mt k r × Mt k r → (Wp →L[ℂ] Wp) := fun p =>
  (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹

def DDSmoothAt (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Prop :=
  ∀ u ∈ DDsp σ w0, u ∈ smoothVecs (k := k) (r := r) σ

def KZeroAt (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H)) :
    Prop :=
  ∀ B : H → Wp, IsBesselMapSm z (psi k r z c) σ π B → (∀ v : H, IsKFinHpk (k := k) (r := r) σ v → B v = 0) →
    ∀ w ∈ smoothVecs (k := k) (r := r) σ, B w = 0

def ExtDDAt (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Prop :=
  ∀ u ∈ DDsp σ w0, ∀ v ∈ DDsp σ w0, Integrable (FI z c π σ u v) (μW.prod μN) ∧
    ∀ B : H → Wp, IsBesselMapSm z (psi k r z c) σ π B →
      (∀ v' : H, IsKFinHpk (k := k) (r := r) σ v' →
        ∫ p, FI z c π σ u v' p ∂(μW.prod μN) = (innerSL ℂ (B v')).smulRight (B u)) →
      ∫ p, FI z c π σ u v p ∂(μW.prod μN) = (innerSL ℂ (B v)).smulRight (B u)

theorem s3dDD_of_at {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN μG νq : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)} {w0 : H}
    (hAt : atFormAtPoint z c π μW μN μG νq σ) (hSm : DDSmoothAt σ w0) (hE : ExtDDAt z c π μW μN σ w0)
    (hK : KZeroAt z c π σ) : DoubleCosetSpanBesselBound z c π μW μN μG νq σ w0 := by
  obtain ⟨l, hl, ha, hb⟩ := hAt
  refine ⟨l, hl, fun u hu v hv => ⟨(hE u hu v hv).1,
    (hE u hu v hv).2 l hl (fun v' hv' => (ha u (hSm u hu) v' hv').2)⟩, ?_⟩
  intro u hu hu0 v hv
  by_cases hex : ∃ v', IsKFinHpk (k := k) (r := r) σ v' ∧ l v' ≠ 0
  · obtain ⟨v', hv', hlv'⟩ := hex
    have h := hb u (hSm u hu) hu0 v' hv'
    have ha0 : 0 < ‖l v'‖ ^ 2 := by positivity
    have hL : l2SG νq (fun g => l (σ g u)) = ENNReal.ofReal (‖u‖ ^ 2 / fdegH μG σ u) := by
      rw [show ‖u‖ ^ 2 * ‖l v'‖ ^ 2 / fdegH μG σ u = ‖l v'‖ ^ 2 * (‖u‖ ^ 2 / fdegH μG σ u) by ring,
        ENNReal.ofReal_mul ha0.le] at h
      exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 ha0).ne' ENNReal.ofReal_ne_top).1 h
    rw [hL, ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    ring
  · push Not at hex
    have h0 : l v = 0 := hK l hl hex v (hSm v hv)
    simp [h0]

end Side

def DDSteps (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG νq νq' : Measure (Mt D.R.k D.R.rS)) (w0 : H),
    NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ → IsDSHpk D.R.k D.R.rS L.ε μ σ → IsLowUnitH D.R.k D.R.rS L.ε μ σ w0 →
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → IsQuotMeas μG (muSof L.μW L.μN) νq → IsQuotMeas μG (muSof L.μW' L.μN) νq' →
      DDSmoothAt σ w0 ∧ (ExtDDAt L.z L.c L.π L.μW L.μN σ w0 ∧ KZeroAt L.z L.c L.π σ) ∧
        (ExtDDAt L.z' L.c L.π' L.μW' L.μN σ w0 ∧ KZeroAt L.z' L.c L.π' σ)

theorem extension_smooth_of_admissible (D : D7) (Ch Cg Cq : ℝ) (h : adm22 D Ch Cg Cq) : ExtSm D Ch Cg Cq := by
  intro L lam0 μ ka b κ H _ _ _ σ μG νq νq' w0 hN hσ _ hG hq hq'
  have h' := h L lam0 μ ka b κ H σ μG νq νq' hN hσ hG hq hq'
  exact ⟨fun _ => h'.1, fun _ => h'.2⟩

theorem double_bound_of_admissible_and_steps (D : D7) (Ch Cg Cq : ℝ) (h : adm22 D Ch Cg Cq) (hS : DDSteps D Ch Cg Cq) :
    DoubleCosetBesselBound D Ch Cg Cq := by
  intro L lam0 μ ka b κ H _ _ _ σ μG νq νq' w0 hN hσ hw0 hG hq hq'
  have h' := h L lam0 μ ka b κ H σ μG νq νq' hN hσ hG hq hq'
  obtain ⟨hSm, ⟨hE, hK⟩, hE', hK'⟩ := hS L lam0 μ ka b κ H σ μG νq νq' w0 hN hσ hw0 hG hq hq'
  exact ⟨s3dDD_of_at h'.1 hSm hE hK, s3dDD_of_at h'.2 hSm hE' hK'⟩

theorem double_bound_and_extension_of_smooth (D : D7) (Ch Cg Cq : ℝ) (h : adm22 D Ch Cg Cq) (hS : DDSteps D Ch Cg Cq) :
    DoubleCosetBesselBound D Ch Cg Cq ∧ ExtSm D Ch Cg Cq :=
  ⟨double_bound_of_admissible_and_steps D Ch Cg Cq h hS, extension_smooth_of_admissible D Ch Cg Cq h⟩

end Formalism.MainNotions.DoubleDerivativeSmoothness
