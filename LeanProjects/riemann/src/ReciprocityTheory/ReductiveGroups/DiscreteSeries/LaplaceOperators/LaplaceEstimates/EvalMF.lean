import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalPA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalMD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.MemLpOfBound

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace ConjugateTransportSingles

variable {k r : ℕ}

theorem inv_conj (P G : Mat k r) (hP : IsUnit P.det) : (P * G * P⁻¹)⁻¹ = P * G⁻¹ * P⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hP, Matrix.mul_assoc]

theorem cJd_transport (P : Mat k r) (hP : IsUnit P.det) (x1 β : Fin (2 * r + k + 1) → ℂ) (G : Mat k r) :
    cJd (P *ᵥ x1) β (P * G * P⁻¹) = (β ᵥ* P) ⬝ᵥ (G⁻¹ *ᵥ x1) := by
  unfold cJd
  rw [inv_conj P G hP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ P⁻¹ P,
    Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec, Matrix.dotProduct_mulVec]

theorem cJd_sinv (P : Mat k r) (hP : IsUnit P.det) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (β : Fin (2 * r + k + 1) → ℂ) (s x : Mat k r) (hs : s ∈ Formalism.QuantumDeterminants.Sset k r z)
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    cJd (xJ P z) β (P * (s * x) * P⁻¹) = cJd (xJ P z) β (P * x * P⁻¹) := by
  unfold xJ
  rw [cJd_transport P hP, cJd_transport P hP]
  exact ((mult k r z hz).1 (0 : Fin (2 * r + k + 1) → ℂ) (β ᵥ* P) s hs x hx).2

theorem cJd_single (P : Mat k r) (hP : IsUnit P.det) (z : Fin (2 * r + k + 1) → ℂ) (d : Fin (2 * r + k + 1))
    (x : Mat k r) :
    cJd (xJ P z) (Pi.single d 1) (P * x * P⁻¹) = (P *ᵥ (x⁻¹ *ᵥ xOne k r z)) d := by
  unfold xJ
  rw [cJd_transport P hP, ← Matrix.dotProduct_mulVec]
  simp [dotProduct, Pi.single_apply]

theorem tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (x1 : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H) (G : Mat k r) :
    tMapD σ x1 x₀ w (Pi.single d m) G = cJd x1 (Pi.single d 1) G * coefX σ x₀ w m G := by
  unfold tMapD
  rw [Finset.sum_eq_single d]
  · simp
  · intro c _ hc
    simp [Pi.single_eq_of_ne hc, coefX]
  · simp

theorem tMapD_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (x1 : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (f : Fin (2 * r + k + 1) → H) (G : Mat k r) :
    tMapD σ x1 x₀ w f G = ∑ d, tMapD σ x1 x₀ w (Pi.single d (f d)) G := by
  rw [Finset.sum_congr rfl fun d _ => tMapD_single σ x1 x₀ w d (f d) G]
  rfl

variable {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

theorem perI_tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (P : Mat k r)
    (hP : IsUnit P.det) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H)
    (ξ : Vp) (g : Mat k r) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    CapelliMinorRestriction.perI P ψ π (tMapD σ (xJ P z) x₀ w (Pi.single d m)) ξ g =ᵐ[μW.prod μN]
      fun p => (P *ᵥ (g⁻¹ *ᵥ xOne k r z)) d • CapelliMinorRestriction.perI P ψ π (coefX σ x₀ w m) ξ g p := by
  filter_upwards [CapelliMinorRestriction.ae_S hW hN] with p hp
  simp only [CapelliMinorRestriction.perI]
  rw [tMapD_single, cJd_sinv P hP z hz _ _ g hp hg, cJd_single P hP, mul_smul]

theorem per_tMapD_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z) (P : Mat k r)
    (hP : IsUnit P.det) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H)
    (ξ : Vp) (g : Mat k r) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    per P μW μN ψ π (tMapD σ (xJ P z) x₀ w (Pi.single d m)) ξ g =
      (P *ᵥ (g⁻¹ *ᵥ xOne k r z)) d • per P μW μN ψ π (coefX σ x₀ w m) ξ g := by
  rw [CapelliMinorRestriction.per_eq, CapelliMinorRestriction.per_eq, ← integral_smul]
  exact integral_congr_ae (perI_tMapD_single σ z hz P hP μW μN hW hN ψ π x₀ w d m ξ g hg)

theorem per_add (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (F₁ F₂ : Mat k r → ℂ) (ξ : Vp) (x : Mat k r)
    (h₁ : Integrable (CapelliMinorRestriction.perI P ψ π F₁ ξ x) (μW.prod μN))
    (h₂ : Integrable (CapelliMinorRestriction.perI P ψ π F₂ ξ x) (μW.prod μN)) :
    per P μW μN ψ π (fun G => F₁ G + F₂ G) ξ x = per P μW μN ψ π F₁ ξ x + per P μW μN ψ π F₂ ξ x := by
  rw [CapelliMinorRestriction.per_eq, CapelliMinorRestriction.per_eq, CapelliMinorRestriction.per_eq, ← integral_add h₁ h₂]
  congr 1
  funext p
  simp [CapelliMinorRestriction.perI, add_smul]

end ConjugateTransportSingles

end ReciprocityTheory.ChartRestriction.DS.Lap
