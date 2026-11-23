import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointOfIso

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def aInt {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (w0 a : H) (t : Mx k r) (p : Mt k r × Mt k r) : Wp →L[ℂ] Wp :=
  (psi k r z c (Matrix.of p.2) * ⟪a, σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹ * t) w0⟫_ℂ) • π (Matrix.of p.1)

def bInt {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wq →L[ℂ] Wq)) (σ : Mx k r → (H →L[ℂ] H))
    (w0 y : H) (t γ : Mx k r) (p : Mt k r × Mt k r) : Wq →L[ℂ] Wq :=
  (star (psi k r z c (Matrix.of p.2)) * ⟪w0, σ (t⁻¹ * γ * Matrix.of p.2 * Matrix.of p.1) y⟫_ℂ) •
    π (Matrix.of p.1)⁻¹

theorem aInt_eq {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    {σ : Mx k r → (H →L[ℂ] H)} (hU : PI.WBL.Cv.SigU σ) (w0 a : H) {t : Mx k r} (ht : t ∈ UH (Hpk k r))
    {p : Mt k r × Mt k r} (hp1 : Matrix.of p.1 ∈ UWset k r z) (hp2 : Matrix.of p.2 ∈ Nset k r) :
    beInt z c π σ (σ t w0) a (Prod.map B7.invM B7.invM p) = aInt z c π σ w0 a t p := by
  obtain ⟨p1, p2⟩ := p
  simp only at hp1 hp2
  have hh : Matrix.of p1 ∈ UH (Hpk k r) := hp1.1
  have hn : Matrix.of p2 ∈ UH (Hpk k r) := hp2.1
  have hinv : ((Matrix.of p1)⁻¹)⁻¹ = Matrix.of p1 :=
    Matrix.inv_eq_left_inv (PI.WBL.Cv.uh_inv hh).1
  have hmul : σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * t) =
      (σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹)).comp (σ t) :=
    hU.2.1 _ (PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_inv hh).2.2 (PI.WBL.Cv.uh_inv hn).2.2) t ht
  have hpsi := Formalism.QuantumDeterminants.BesselUnipotentEquiv.star_psi_inv z c hz (Matrix.of p2) hp2
  show (⟪a, σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹) (σ t w0)⟫_ℂ *
      star (psi k r z c (Matrix.of p2)⁻¹)) • π ((Matrix.of p1)⁻¹)⁻¹ =
    (psi k r z c (Matrix.of p2) * ⟪a, σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * t) w0⟫_ℂ) •
      π (Matrix.of p1)
  rw [hinv, hpsi, hmul, ContinuousLinearMap.comp_apply, mul_comm]

private theorem ae_mem_uwset_prod_nset_of_isHaarOn {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)}
    (hW : B.IsHaarOn (UWset k r z) μW) (hN : B.IsHaarOn (Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r := by
  haveI : IsFiniteMeasureOnCompacts μW := ⟨fun K hK => hW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μN := ⟨fun K hK => hN.finite_compact K hK⟩
  rw [ae_iff]
  apply measure_mono_null (t := ((UWset k r z)ᶜ : Set (Mt k r)) ×ˢ (Set.univ : Set (Mt k r)) ∪
    (Set.univ : Set (Mt k r)) ×ˢ ((Nset k r)ᶜ : Set (Mt k r)))
  · intro p hp
    simp only [Set.mem_setOf_eq, not_and_or] at hp
    rcases hp with hp | hp
    · exact Or.inl ⟨hp, Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _, hp⟩
  · apply measure_union_null
    · rw [Measure.prod_prod, hW.conc, zero_mul]
    · rw [Measure.prod_prod, hN.conc, mul_zero]

theorem sideA {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    {σ : Mx k r → (H →L[ℂ] H)} (hU : PI.WBL.Cv.SigU σ) {μW μN : Measure (Mt k r)}
    (hW : B.IsHaarOn (UWset k r z) μW) (hN : B.IsHaarOn (Nset k r) μN) (w0 a : H) {t : Mx k r}
    (ht : t ∈ UH (Hpk k r)) (hI : Integrable (beInt z c π σ (σ t w0) a) (μW.prod μN)) :
    Integrable (aInt z c π σ w0 a t) (μW.prod μN) ∧
      ∫ p, aInt z c π σ w0 a t p ∂(μW.prod μN) = be z c π σ μW μN (σ t w0) a := by
  haveI : IsFiniteMeasureOnCompacts μW := ⟨fun K hK => hW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μN := ⟨fun K hK => hN.finite_compact K hK⟩
  have hmp : MeasurePreserving (Prod.map (B7.invM (k := k) (r := r)) (B7.invM (k := k) (r := r)))
      (μW.prod μN) (μW.prod μN) :=
    (measurePreserving_invM_of_isHaarOn hW).prod (mp_inv_N hN)
  have hae : (fun p => beInt z c π σ (σ t w0) a (Prod.map B7.invM B7.invM p)) =ᵐ[μW.prod μN]
      aInt z c π σ w0 a t := by
    filter_upwards [ae_mem_uwset_prod_nset_of_isHaarOn hW hN] with p hp
    exact aInt_eq hz c π hU w0 a ht hp.1 hp.2
  have hcomp : Integrable (fun p => beInt z c π σ (σ t w0) a (Prod.map B7.invM B7.invM p))
      (μW.prod μN) :=
    (hmp.integrable_comp hI.aestronglyMeasurable).mpr hI
  refine ⟨hcomp.congr hae, ?_⟩
  rw [← integral_congr_ae hae]
  unfold be
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hI.aestronglyMeasurable)]

theorem integral_adjoint {α : Type*} [MeasurableSpace α] {μ : Measure α} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {f : α → (E →L[ℂ] F)} (hf : Integrable f μ) :
    Integrable (fun x => ContinuousLinearMap.adjoint (f x)) μ ∧
      ∫ x, ContinuousLinearMap.adjoint (f x) ∂μ = ContinuousLinearMap.adjoint (∫ x, f x ∂μ) := by
  let L : (E →L[ℂ] F) ≃ₗᵢ[ℝ] (F →L[ℂ] E) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := F)).toIsometryEquiv.toRealLinearIsometryEquivOfMapZero
      (map_zero (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := F)))
  have hL : ∀ g, L g = ContinuousLinearMap.adjoint g := fun g => rfl
  refine ⟨?_, ?_⟩
  · have := L.toLinearIsometry.toContinuousLinearMap.integrable_comp hf
    simpa [hL] using this
  · have := L.toLinearIsometry.toContinuousLinearMap.integral_comp_comm hf
    simpa [hL] using this

theorem bInt_eq {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {π : Mx k r → (Wq →L[ℂ] Wq)} (hrep : IsCRepOn (UWset k r z) π)
    (hun : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖)
    {σ : Mx k r → (H →L[ℂ] H)} (hU : PI.WBL.Cv.SigU σ) (w0 y : H) {t γ : Mx k r} (ht : t ∈ UH (Hpk k r))
    (hγ : γ ∈ UH (Hpk k r))
    {p : Mt k r × Mt k r} (hp1 : Matrix.of p.1 ∈ UWset k r z) (hp2 : Matrix.of p.2 ∈ Nset k r) :
    bInt z c π σ w0 y t γ p = ContinuousLinearMap.adjoint (aInt z c π σ w0 y (γ⁻¹ * t) p) := by
  obtain ⟨p1, p2⟩ := p
  simp only at hp1 hp2
  unfold bInt aInt
  have hh : Matrix.of p1 ∈ UH (Hpk k r) := hp1.1
  have hn : Matrix.of p2 ∈ UH (Hpk k r) := hp2.1
  obtain ⟨-, hh2, hhi⟩ := PI.WBL.Cv.uh_inv hh
  obtain ⟨-, hn2, hni⟩ := PI.WBL.Cv.uh_inv hn
  obtain ⟨-, hγ2, hγi⟩ := PI.WBL.Cv.uh_inv hγ
  obtain ⟨ht1, -, hti⟩ := PI.WBL.Cv.uh_inv ht
  have hXU : (Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * (γ⁻¹ * t) ∈ UH (Hpk k r) :=
    PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_mul hhi hni) (PI.WBL.Cv.uh_mul hγi ht)
  have hYU : t⁻¹ * γ * Matrix.of p2 * Matrix.of p1 ∈ UH (Hpk k r) :=
    PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_mul hti hγ) hn) hh
  have hXY : (Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * (γ⁻¹ * t) * (t⁻¹ * γ * Matrix.of p2 * Matrix.of p1)
      = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc t t⁻¹, ht1, Matrix.one_mul, ← Matrix.mul_assoc γ⁻¹ γ, hγ2, Matrix.one_mul,
      ← Matrix.mul_assoc (Matrix.of p2)⁻¹ (Matrix.of p2), hn2, Matrix.one_mul, hh2]
  have hσ : σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * (γ⁻¹ * t))
      (σ (t⁻¹ * γ * Matrix.of p2 * Matrix.of p1) y) = y := by
    rw [← ContinuousLinearMap.comp_apply, ← hU.2.1 _ hXU _ hYU, hXY, hU.1,
      ContinuousLinearMap.one_apply]
  let LX : H →ₗᵢ[ℂ] H :=
    { toLinearMap := (σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * (γ⁻¹ * t))).toLinearMap
      norm_map' := hU.2.2 _ hXU }
  have hinner : ⟪σ ((Matrix.of p1)⁻¹ * (Matrix.of p2)⁻¹ * (γ⁻¹ * t)) w0, y⟫_ℂ =
      ⟪w0, σ (t⁻¹ * γ * Matrix.of p2 * Matrix.of p1) y⟫_ℂ := by
    conv_lhs => rw [← hσ]
    exact LX.inner_map_map w0 _
  rw [map_smulₛₗ, adjoint_pi hrep hun hp1]
  congr 1
  rw [map_mul, inner_conj_symm, hinner]
  rfl

theorem sideB {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) {π : Mx k r → (Wq →L[ℂ] Wq)}
    (hrep : IsCRepOn (UWset k r z) π) (hun : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖)
    {σ : Mx k r → (H →L[ℂ] H)} (hU : PI.WBL.Cv.SigU σ) {μW μN : Measure (Mt k r)}
    (hW : B.IsHaarOn (UWset k r z) μW) (hN : B.IsHaarOn (Nset k r) μN) (w0 y : H) {t γ : Mx k r}
    (ht : t ∈ UH (Hpk k r)) (hγ : γ ∈ UH (Hpk k r))
    (hI : Integrable (beInt z c π σ (σ (γ⁻¹ * t) w0) y) (μW.prod μN))
    (hadj : ContinuousLinearMap.adjoint (be z c π σ μW μN (σ (γ⁻¹ * t) w0) y) =
      be z c π σ μW μN y (σ (γ⁻¹ * t) w0)) :
    Integrable (bInt z c π σ w0 y t γ) (μW.prod μN) ∧
      ∫ p, bInt z c π σ w0 y t γ p ∂(μW.prod μN) = be z c π σ μW μN y (σ (γ⁻¹ * t) w0) := by
  have hγt : γ⁻¹ * t ∈ UH (Hpk k r) := PI.WBL.Cv.uh_mul (PI.WBL.Cv.uh_inv hγ).2.2 ht
  obtain ⟨hAi, hAe⟩ := sideA hz c π hU hW hN w0 y hγt hI
  obtain ⟨hBi, hBe⟩ := integral_adjoint hAi
  have hae : bInt z c π σ w0 y t γ =ᵐ[μW.prod μN]
      fun p => ContinuousLinearMap.adjoint (aInt z c π σ w0 y (γ⁻¹ * t) p) := by
    filter_upwards [ae_mem_uwset_prod_nset_of_isHaarOn hW hN] with p hp
    exact bInt_eq c hrep hun hU w0 y ht hγ hp.1 hp.2
  refine ⟨hBi.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, hBe, hAe, hadj]

end Formalism.FourierDecayAlt.P.S3dx6
