import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RWConstMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilInducedRepresentationHypothesisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationHypothesisStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel Topology
open Filter

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSmooth

section Group

variable {F : Type} [Field F]

def low (y : F) : GL (Fin 2) F :=
  ⟨!![1, 0; y, 1], !![1, 0; -y, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def stab (W : GL (Fin 2) F → ℂ) : Subgroup (GL (Fin 2) F) where
  carrier := {u | ∀ g, W (g * u) = W g}
  mul_mem' := fun {a b} ha hb g => by rw [← mul_assoc, hb, ha]
  one_mem' := fun g => by rw [mul_one]
  inv_mem' := fun {a} ha g => by
    have h := ha (g * a⁻¹)
    rw [inv_mul_cancel_right] at h
    exact h.symm

end Group

section Iwahori

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem mem_nhds_of_factors (H : Subgroup (GL (Fin 2) F))
    (hN : ∀ᶠ x in 𝓝 (0 : F), uni2 x ∈ H)
    (hL : ∀ᶠ y in 𝓝 (0 : F), low y ∈ H)
    (hD : ∀ᶠ a in 𝓝 (1 : F), ∀ s : Fˣ, (s : F) = a → dg2 s 1 ∈ H)
    (hM : ∀ᶠ a in 𝓝 (1 : F), ∀ s : Fˣ, (s : F) = a → dg2 s s⁻¹ ∈ H) :
    (H : Set (GL (Fin 2) F)) ∈ 𝓝 (1 : GL (Fin 2) F) := by
  have cA : Continuous fun u : GL (Fin 2) F => u.val 0 0 := GLnLocal.continuous_entry F 2 0 0
  have cB : Continuous fun u : GL (Fin 2) F => u.val 0 1 := GLnLocal.continuous_entry F 2 0 1
  have cC : Continuous fun u : GL (Fin 2) F => u.val 1 0 := GLnLocal.continuous_entry F 2 1 0
  have cD : Continuous fun u : GL (Fin 2) F => u.val 1 1 := GLnLocal.continuous_entry F 2 1 1
  have hD1 : (fun u : GL (Fin 2) F => u.val 1 1) 1 ≠ 0 := by simp
  have tx : Tendsto (fun u : GL (Fin 2) F => u.val 0 1 / u.val 1 1) (𝓝 1) (𝓝 0) := by
    have : ContinuousAt (fun u : GL (Fin 2) F => u.val 0 1 / u.val 1 1) 1 :=
      (cB.continuousAt (x := 1)).div cD.continuousAt hD1
    simpa [ContinuousAt] using this
  have ty : Tendsto (fun u : GL (Fin 2) F => u.val 1 0 / u.val 1 1) (𝓝 1) (𝓝 0) := by
    have : ContinuousAt (fun u : GL (Fin 2) F => u.val 1 0 / u.val 1 1) 1 :=
      (cC.continuousAt (x := 1)).div cD.continuousAt hD1
    simpa [ContinuousAt] using this
  have td : Tendsto (fun u : GL (Fin 2) F => u.val 0 0 * u.val 1 1 - u.val 0 1 * u.val 1 0) (𝓝 1) (𝓝 1) := by
    have : ContinuousAt (fun u : GL (Fin 2) F => u.val 0 0 * u.val 1 1 - u.val 0 1 * u.val 1 0) 1 :=
      ((cA.mul cD).sub (cB.mul cC)).continuousAt
    simpa [ContinuousAt] using this
  have ti : Tendsto (fun u : GL (Fin 2) F => (u.val 1 1)⁻¹) (𝓝 1) (𝓝 1) := by
    have : ContinuousAt (fun u : GL (Fin 2) F => (u.val 1 1)⁻¹) 1 :=
      (cD.continuousAt (x := 1)).inv₀ hD1
    simpa [ContinuousAt] using this
  have hne : ∀ᶠ u : GL (Fin 2) F in 𝓝 1, u.val 1 1 ≠ 0 := cD.continuousAt.eventually_ne hD1
  filter_upwards [hne, tx.eventually hN, ty.eventually hL, td.eventually hD, ti.eventually hM] with u h0 h1 h2 h3 h4
  have hdet : u.val 0 0 * u.val 1 1 - u.val 0 1 * u.val 1 0 ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det u).ne_zero
    simpa [Matrix.det_fin_two] using this
  have e : u = uni2 (u.val 0 1 / u.val 1 1) * dg2 (Units.mk0 _ hdet) 1 *
      dg2 (Units.mk0 _ (inv_ne_zero h0)) (Units.mk0 _ (inv_ne_zero h0))⁻¹ * low (u.val 1 0 / u.val 1 1) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uni2, dg2, low, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  rw [e]
  exact H.mul_mem (H.mul_mem (H.mul_mem h1 (h3 _ rfl)) (h4 _ rfl)) h2

end Iwahori

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem ev_sq [CharZero F] {P : F → Prop} (hP : ∀ᶠ r in 𝓝 (1 : F), P r) :
    ∀ᶠ a in 𝓝 (1 : F), ∃ r, P r ∧ r * r = a := by
  let := nontriviallyNormedField F
  have := completeSpace_nontriviallyNormedField F
  have hd : HasStrictDerivAt (fun x : F => x * x) ((1 : F) * 1 + 1 * 1) 1 :=
    (hasStrictDerivAt_id (1 : F)).mul (hasStrictDerivAt_id (1 : F))
  have h2 : ((1 : F) * 1 + 1 * 1) ≠ 0 := by
    norm_num
  have hm := hd.map_nhds_eq h2
  have hs : (fun x : F => x * x) '' {r | P r} ∈ 𝓝 (1 : F) := by
    have := image_mem_map (m := fun x : F => x * x) hP
    rw [hm] at this
    simpa using this
  filter_upwards [hs] with a ha
  obtain ⟨r, hr, rfl⟩ := ha
  exact ⟨r, hr, rfl⟩

theorem ev_modulus : ∀ᶠ r in 𝓝 (1 : F), GroundTheory.LocalField.modulus r = 1 := by
  have hB : (valBall F 1 : Set F) ∈ 𝓝 (0 : F) := (isOpen_valBall 1).mem_nhds (zero_mem _)
  have ht : Tendsto (fun r : F => r - 1) (𝓝 1) (𝓝 0) := by
    have : ContinuousAt (fun r : F => r - 1) 1 := (continuous_id.sub continuous_const).continuousAt
    simpa [ContinuousAt] using this
  filter_upwards [ht hB] with r hr
  have h := modulus_add_eq (K := F) (x := 1) (d := r - 1) one_ne_zero (by simpa using hr)
  simpa using h

end Local

section Support

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

theorem ev_dil {Ψ : E → ℂ} (hΨ : Ψ ∈ SBE E) : ∀ᶠ e in 𝓝 (1 : E), ∀ x, Ψ (x * e) = Ψ x := by
  have hK : IsCompact (tsupport Ψ) := hΨ.2
  have h1 : ∀ᶠ e in 𝓝 (1 : E), ∀ x ∈ tsupport Ψ, Ψ (x * e) = Ψ x := by
    refine hK.eventually_forall_of_forall_eventually (fun y _ => ?_)
    have f1 : IsLocallyConstant fun p : E × E => Ψ (p.2 * p.1) :=
      hΨ.1.comp_continuous (continuous_snd.mul continuous_fst)
    have f2 : IsLocallyConstant fun p : E × E => Ψ p.2 := hΨ.1.comp_continuous continuous_snd
    filter_upwards [f1.eventually_eq (1, y), f2.eventually_eq (1, y)] with p h1 h2
    rw [h1, h2, mul_one]
  have ti : Tendsto (fun e : E => e⁻¹) (𝓝 1) (𝓝 1) := by
    have : ContinuousAt (fun e : E => e⁻¹) 1 := continuousAt_inv₀ one_ne_zero
    simpa [ContinuousAt] using this
  have hne : ∀ᶠ e : E in 𝓝 1, e ≠ 0 := eventually_ne_nhds one_ne_zero
  filter_upwards [h1, ti.eventually h1, hne] with e h1 h2 h0 x
  by_cases hx : x ∈ tsupport Ψ
  · exact h1 x hx
  by_cases hxe : x * e ∈ tsupport Ψ
  · have := h2 _ hxe
    rw [mul_inv_cancel_right₀ h0] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxe]

theorem ev_char (c : Eˣ →* ℂˣ) (hc : Continuous c) :
    ∀ᶠ e in 𝓝 (1 : E), ∀ u : Eˣ, (u : E) = e → c u = 1 := by
  have hV : (c.ker : Set Eˣ) ∈ 𝓝 (1 : Eˣ) :=
    (GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous c hc).mem_nhds (one_mem _)
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  simp only [Units.val_one] at hT
  filter_upwards [hT] with e he u hu
  exact hTV (show (u : E) ∈ T by rw [hu]; exact he)

end Support

section Chirp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [Field E] [Algebra F E] [TopologicalSpace E]

theorem ev_chirp {χ : AddChar F Circle} (hlc : IsLocallyConstant fun x => (χ x : ℂ))
    (hN : Continuous (Algebra.norm F : E → F)) {Ψ : E → ℂ} (hΨ : HasCompactSupport Ψ) :
    ∀ᶠ b in 𝓝 (0 : F), ∀ z, (χ (b * Algebra.norm F z) : ℂ) * Ψ z = Ψ z := by
  have h1 : ∀ᶠ b in 𝓝 (0 : F), ∀ z ∈ tsupport Ψ, (χ (b * Algebra.norm F z) : ℂ) = 1 := by
    refine IsCompact.eventually_forall_of_forall_eventually hΨ (fun y _ => ?_)
    have f1 : IsLocallyConstant fun p : F × E => (χ (p.1 * Algebra.norm F p.2) : ℂ) :=
      hlc.comp_continuous (continuous_fst.mul (hN.comp continuous_snd))
    filter_upwards [f1.eventually_eq (0, y)] with p h1
    simpa using h1
  filter_upwards [h1] with b hb z
  by_cases hz : z ∈ tsupport Ψ
  · rw [hb z hz, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]

end Chirp

section Pi

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [CommRing E] [Nontrivial E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem piG_choice (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) {Φ : E → ℂ}
    (hΦ : ∀ u : Eˣ, Algebra.norm F (u : E) = 1 → ∀ x, Φ (x * u) = (((c u)⁻¹ : ℂˣ) : ℂ) * Φ x)
    (g : GL (Fin 2) F) (t : Eˣ) (ht : Algebra.norm F (t : E) = (g.val).det) (x : E) :
    piG χ σ μE lam c g Φ x = ((c t : ℂˣ) : ℂ) * (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
      rW χ σ μE lam (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1)
        (fun y => Φ (y * (t : E))) x := by
  have h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det := ⟨t, ht⟩
  have h0 : Algebra.norm F (h.choose : E) = (g.val).det := h.choose_spec
  have hne : Algebra.norm F (h.choose : E) ≠ 0 :=
    (h.choose.isUnit.map (Algebra.norm F : E →* F)).ne_zero
  obtain ⟨u, hu⟩ : ∃ u : Eˣ, t = h.choose * u := ⟨h.choose⁻¹ * t, by group⟩
  have hN : Algebra.norm F (u : E) = 1 := by
    have e : Algebra.norm F (h.choose : E) * Algebra.norm F (u : E) =
        Algebra.norm F (h.choose : E) * 1 := by
      rw [← map_mul, ← Units.val_mul, ← hu, ht, h0, mul_one]
    exact mul_left_cancel₀ hne e
  have hfun : (fun y => Φ (y * (t : E))) =
      fun y => (((c u)⁻¹ : ℂˣ) : ℂ) * Φ (y * (h.choose : E)) := by
    funext y
    rw [hu, Units.val_mul, ← mul_assoc]
    exact hΦ u hN _
  have hcu : ((c u : ℂˣ) : ℂ) * (((c u)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [piG, dif_pos h, hfun, GlobalTheory.CompanionTheory.WeilChoice.rW_const_mul, hu, map_mul, Units.val_mul]
  linear_combination (-(((c h.choose : ℂˣ) : ℂ) * (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
      rW χ σ μE lam (g.val 0 0 / (g.val).det) (g.val 0 1)
        (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * (h.choose : E))) x)) * hcu

theorem piG_det_one (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) {Φ : E → ℂ}
    (hΦ : ∀ u : Eˣ, Algebra.norm F (u : E) = 1 → ∀ x, Φ (x * u) = (((c u)⁻¹ : ℂˣ) : ℂ) * Φ x)
    (g : GL (Fin 2) F) (hg : (g.val).det = 1) :
    piG χ σ μE lam c g Φ = rWm χ σ μE lam g.val Φ := by
  funext x
  rw [piG_choice χ σ μE lam c hΦ g 1 (by simp [hg]), hg]
  simp [rWm]

theorem nsg_norm (t : Eˣ) : nsg E (Algebra.norm F (t : E)) = 1 := by
  rw [nsg, if_pos ⟨t, rfl⟩]

theorem nsg_one : nsg E (1 : F) = 1 := by
  have := nsg_norm (F := F) (1 : Eˣ)
  simpa using this

theorem rW_zero (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (a b d : F) (Φ : E → ℂ) (z : E) :
    rW χ σ μE lam a b 0 d Φ z = (χ (a * b * Algebra.norm F z) : ℂ) * nsg E a * ((modulus a : ℝ) : ℂ) *
      Φ (algebraMap F E a * z) := by
  rw [rW, if_pos rfl]

theorem rWm_upper (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (x : F) (Φ : E → ℂ) (z : E) :
    rWm χ σ μE lam !![1, x; 0, 1] Φ z = (χ (x * Algebra.norm F z) : ℂ) * Φ z := by
  simp [rWm, rW_zero, nsg_one]

theorem rWm_one (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (Φ : E → ℂ) :
    rWm χ σ μE lam 1 Φ = Φ := by
  funext z
  simp [rWm, rW_zero, nsg_one]

end Pi

end GlobalTheory.CompanionTheory.WeilSmooth
