import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualTupleIdealsCastAdd
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.IntU

theorem hpk_row (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_mulVec_esI (k r : ℕ) (a : Fin r) (z : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ z) (esI k r a) = z (eI k r a) := by
  simp [Matrix.mulVec, dotProduct, hpk_row]

theorem coord_eI {E : Type} [Field E] {k r : ℕ} (σ : E →+* E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = star (τ x)) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hB : Bᴴ * Hpk k r * B = J.map τ)
    (x y : Fin (2 * r + k + 1) → E) (a : Fin r) (s : ℝ) (hs : s ≠ 0)
    (hy : B *ᵥ (fun i => τ (y i)) = (s : ℂ)⁻¹ • bvec (esI k r a)) :
    (B *ᵥ fun i => τ (x i)) (eI k r a) = (s : ℂ) * τ (form σ J x y) := by
  have key : star (B *ᵥ (fun i => τ (y i))) ⬝ᵥ (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) =
      star (fun i => τ (y i)) ⬝ᵥ (J.map τ *ᵥ fun i => τ (x i)) := by
    rw [← hB]
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have lhs : star (B *ᵥ (fun i => τ (y i))) ⬝ᵥ (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) =
      (s : ℂ)⁻¹ * (B *ᵥ fun i => τ (x i)) (eI k r a) := by
    rw [hy, star_smul, bvec, ← hpk_mulVec_esI k r a (B *ᵥ fun i => τ (x i))]
    simp [Pi.star_def, dotProduct, Pi.single_apply, -Matrix.mulVec_mulVec]
  have rhs : star (fun i => τ (y i)) ⬝ᵥ (J.map τ *ᵥ fun i => τ (x i)) = τ (form σ J x y) := by
    simp only [form, dotProduct, map_sum, map_mul, hτ, RingHom.map_mulVec]
    rfl
  rw [lhs, rhs] at key
  rw [← key, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hs), one_mul]

end GlobalTheory.SnMass.VolN.IntU

namespace GlobalTheory.SnMass.VolN.IntU

theorem form_smul_smul {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (c c' : E) (x y : Fin n → E) : form σ J (c • x) (c' • y) = c * σ c' * form σ J x y := by
  simp only [form, dotProduct, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem mem_of_pair {E : Type} [Field E] [NumberField E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x)
    (𝔞 𝔟 : FractionalIdeal (𝓞 E)⁰ E) (h𝔞 : 𝔞 ≠ 0) (h𝔟 : 𝔟 ≠ 0) (hst : FrameDual.Stab σ 𝔞⁻¹) (u : E)
    (hu : ∀ c ∈ 𝔟, ∀ c' ∈ 𝔞⁻¹, c * σ c' * u ∈ (algebraMap (𝓞 E) E).range) : u ∈ 𝔞 * 𝔟⁻¹ := by
  have hI : 𝔟 * 𝔞⁻¹ ≠ 0 := mul_ne_zero h𝔟 (inv_ne_zero h𝔞)
  have e : 𝔞 * 𝔟⁻¹ = (𝔟 * 𝔞⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
  rw [e, FractionalIdeal.mem_inv_iff hI]
  intro y hy
  refine FractionalIdeal.mul_induction_on hy (fun c hc d hd => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
  · have := hu c hc (σ d) (hst d hd)
    rw [hσ] at this
    obtain ⟨t, ht⟩ := this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨t, by rw [ht]; ring⟩
  · rw [mul_add]; exact Submodule.add_mem (1 : FractionalIdeal (𝓞 E)⁰ E).coeToSubmodule h₁ h₂

end GlobalTheory.SnMass.VolN.IntU

open GlobalTheory.SnMass.VolN.IntU in

theorem GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (eI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV γ hγ p
  obtain ⟨hCM, -, hND, hSD, -, -, hTup, hMod, hs, hAd⟩ := hV
  obtain ⟨⟨a, b⟩, hab⟩ := p
  dsimp only
  have hconj : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x) := hCM.2.2.2
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    show σ (σ x) = x
    exact (Classical.arbitrary (InfinitePlace E)).embedding.injective (by rw [hconj, hconj, star_star])
  set eb : Fin (2 * r + k + 1) → E := fun i => P i b.castSucc with heb
  set fa : Fin (2 * r + k + 1) → E := fun i => f i a with hfa
  refine ⟨form (σ : E →+* E) J (γ *ᵥ eb) fa, ?_, fun w => ?_⟩
  · refine mem_of_pair (σ : E →+* E) hσ _ _ (FrameDual.dInv_ne_zero _) (FrameDual.dInv_ne_zero _)
      ((FrameDual.stab_dInv hσ _).inv hσ (FrameDual.dInv_ne_zero _)) _ ?_
    intro c hc c' hc'
    have h1 : c • eb ∈ Λ := hTup (Submodule.subset_span
      ⟨Fin.castAdd r b.castSucc, c, by rw [FrameDual.frameDualTupleIdeals_castAdd]; exact hc, by
        funext i; simp [heb, sideM]⟩)
    have h2 : c' • fa ∈ Λ := hTup (Submodule.subset_span
      ⟨Fin.natAdd (r + 1) a, c', by rw [FrameDual.frameDualTupleIdeals_natAdd]; exact hc', by
        funext i; simp [hfa, sideM]⟩)
    have h3 : γ *ᵥ (c • eb) ∈ Λ := by
      rw [← hγ.2]; exact ⟨_, h1, rfl⟩
    have h4 := (hSD.2 _).1 h3 _ h2
    rwa [Matrix.mulVec_smul, form_smul_smul] at h4
  · set τ := w.embedding with hτ
    have hB := hMod w
    have hdet : IsUnit (A w).det := by
      refine Ne.isUnit fun h0 => hND.2 ?_
      have := congrArg Matrix.det hB
      rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
      exact (map_eq_zero τ).1 this.symm
    have hsb : (s b : ℂ) ≠ 0 := by exact_mod_cast (hs b).ne'
    have hbv : bvec (eI k r b) = (s b : ℂ)⁻¹ • (A w *ᵥ fun i => τ (eb i)) := by
      rw [(hAd w b).1, smul_smul, inv_mul_cancel₀ hsb, one_smul]
    have hmap : (γ.map τ *ᵥ fun i => τ (eb i)) = fun i => τ ((γ *ᵥ eb) i) := by
      funext i; exact (RingHom.map_mulVec τ γ eb i).symm
    have hent : gM A γ w (eI k r a) (eI k r b) =
        (s b : ℂ)⁻¹ * (A w *ᵥ fun i => τ ((γ *ᵥ eb) i)) (eI k r a) := by
      have e1 : gM A γ w (eI k r a) (eI k r b) = (gM A γ w *ᵥ bvec (eI k r b)) (eI k r a) := by
        simp [bvec]
      rw [e1, hbv, Matrix.mulVec_smul, gM, Matrix.mulVec_mulVec, Matrix.mul_assoc (A w * γ.map τ),
        Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one, ← Matrix.mulVec_mulVec, hmap]
      rfl
    show gM A γ w (eI k r a) (eI k r b) = _
    rw [hent, coord_eI (σ : E →+* E) τ (hconj τ) J (A w) hB (γ *ᵥ eb) fa a (s a) (hs a).ne' (hAd w a).2]
    push_cast
    ring
