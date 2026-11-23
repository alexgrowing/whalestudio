import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualTupleIdealsCastAdd

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

section Corner

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem form_smul_smul' (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : E) (u v : Fin n → E) :
    form σ J (y • u) (x • v) = σ x * y * form σ J u v := by
  simp only [form, Matrix.mulVec_smul, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem form_mem_dInv_mul (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : GlobalTheory.SgGlob.SelfDual σ J Λ) (i j : ℕ) (u v : Fin n → E)
    (hu : ∀ y ∈ (dInv E j)⁻¹, y • u ∈ Λ) (hv : ∀ x ∈ (dInv E i)⁻¹, x • v ∈ Λ) :
    form σ J u v ∈ dInv E i * dInv E j := by
  have h0 : dInv E i * dInv E j ≠ 0 :=
    mul_ne_zero (FrameDual.dInv_ne_zero i) (FrameDual.dInv_ne_zero j)
  rw [← inv_inv (dInv E i * dInv E j), FractionalIdeal.mem_inv_iff (inv_ne_zero h0)]
  intro z hz
  rw [mul_inv] at hz
  refine FractionalIdeal.mul_induction_on hz (fun x hx y hy => ?_) (fun a b ha hb => ?_)
  · have hsx : σ x ∈ (dInv E i)⁻¹ :=
      FrameDual.Stab.inv hσ (FrameDual.stab_dInv hσ i) (FrameDual.dInv_ne_zero i) x hx
    have h1 := (hΛ.2 (y • u)).1 (hu y hy) ((σ x) • v) (hv _ hsx)
    rw [form_smul_smul', hσ] at h1
    obtain ⟨d, hd⟩ := h1
    refine (FractionalIdeal.mem_one_iff _).2 ⟨d, ?_⟩
    rw [hd]; ring
  · rw [mul_add]; exact Submodule.add_mem (1 : FractionalIdeal (𝓞 E)⁰ E).coeToSubmodule ha hb

end Corner

theorem Hpk_esI_apply (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  unfold Hpk
  simp only [esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

end GlobalTheory.SnMass.VolN

namespace GlobalTheory.SnMass.VolN

theorem Hpk_mulVec_esI (k r : ℕ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  simp only [Matrix.mulVec, dotProduct, Hpk_esI_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem map_mulVec_comp {E : Type} [Field E] (φ : E →+* ℂ) {n : ℕ} (γ : Matrix (Fin n) (Fin n) E)
    (v : Fin n → E) : (γ.map φ) *ᵥ (fun i => φ (v i)) = fun i => φ ((γ *ᵥ v) i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem corner_entry {E : Type} [Field E] (σ : E →+* E) (φ : E →+* ℂ) (hφ : ∀ x, φ (σ x) = star (φ x))
    {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (hJ : J.det ≠ 0)
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hM : Mᴴ * Hpk k r * M = J.map φ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (a b : Fin r) (fa fb : Fin (2 * r + k + 1) → E)
    (sa sb : ℝ) (hsa : sa ≠ 0) (hsb : sb ≠ 0)
    (ha : M *ᵥ (fun i => φ (fa i)) = ((sa : ℂ)⁻¹) • bvec (esI k r a))
    (hb : M *ᵥ (fun i => φ (fb i)) = ((sb : ℂ)⁻¹) • bvec (esI k r b)) :
    (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) = ((sa * sb : ℝ) : ℂ) * φ (form σ J (γ *ᵥ fb) fa) := by
  have hsa' : (sa : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsa
  have hsb' : (sb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hsb
  have hdet : (J.map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero φ).2 hJ
  have hU : IsUnit M.det := by
    refine isUnit_iff_ne_zero.2 fun h => hdet ?_
    rw [← hM, Matrix.det_mul, h, mul_zero]
  have hinv : M⁻¹ *ᵥ bvec (esI k r b) = (sb : ℂ) • fun i => φ (fb i) := by
    have e1 : M⁻¹ *ᵥ (M *ᵥ (fun i => φ (fb i))) = fun i => φ (fb i) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
    rw [hb, Matrix.mulVec_smul] at e1
    rw [← e1, smul_smul, mul_inv_cancel₀ hsb', one_smul]
  have hreal : star (M *ᵥ (fun i => φ (fa i))) = M *ᵥ (fun i => φ (fa i)) := by
    rw [ha]; funext j
    simp only [Pi.star_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have hbv : bvec (esI k r a) = (sa : ℂ) • (M *ᵥ (fun i => φ (fa i))) := by
    rw [ha, smul_smul, mul_inv_cancel₀ hsa', one_smul]
  set X : Fin (2 * r + k + 1) → ℂ := fun i => φ ((γ *ᵥ fb) i) with hX
  have h1 : (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) = (sb : ℂ) * (M *ᵥ X) (eI k r a) := by
    have : (M * γ.map φ * M⁻¹) (eI k r a) (esI k r b) =
        ((M * γ.map φ * M⁻¹) *ᵥ bvec (esI k r b)) (eI k r a) := by
      simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv, Matrix.mulVec_smul,
      map_mulVec_comp, Matrix.mulVec_smul]
    rfl
  have h2 : (M *ᵥ X) (eI k r a) = (sa : ℂ) * (star (fun i => φ (fa i)) ⬝ᵥ ((J.map φ) *ᵥ X)) := by
    rw [← Hpk_mulVec_esI k r a (M *ᵥ X)]
    have e2 : (Hpk k r *ᵥ (M *ᵥ X)) (esI k r a) = bvec (esI k r a) ⬝ᵥ (Hpk k r *ᵥ (M *ᵥ X)) := by
      simp [bvec]
    rw [e2, hbv, smul_dotProduct, smul_eq_mul, ← hreal, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
  have h3 : star (fun i => φ (fa i)) ⬝ᵥ ((J.map φ) *ᵥ X) = φ (form σ J (γ *ᵥ fb) fa) := by
    rw [hX, map_mulVec_comp]
    simp [form, dotProduct, map_sum, map_mul, hφ]
  rw [h1, h2, h3]
  push_cast; ring

end GlobalTheory.SnMass.VolN

namespace GlobalTheory.SnMass.VolN

theorem corner_entry_mem_ideLat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (esI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hD γ hγ p
  obtain ⟨hCM, -, hJ, hΛ, -, -, hlat, hA, hs, had⟩ := hD
  obtain ⟨-, -, -, hcc⟩ := hCM
  obtain ⟨-, hγΛ⟩ := hγ
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    let τ : E →+* ℂ := Classical.arbitrary _
    apply τ.injective
    change τ (σ (σ x)) = τ x
    rw [hcc, hcc, star_star]
  have hcol : ∀ (b : Fin r) (y : E), y ∈ (dInv E (r - (b : ℕ)))⁻¹ → y • (fun i => f i b) ∈ Λ := by
    intro b y hy
    refine hlat (Submodule.subset_span ⟨Fin.natAdd (r + 1) b, y, ?_, ?_⟩)
    · simpa [id1] using hy
    · funext i; simp [sideM]
  have hmap : ∀ v ∈ Λ, γ *ᵥ v ∈ Λ := by
    intro v hv
    have : γ *ᵥ v ∈ latMap γ Λ := ⟨v, hv, rfl⟩
    rwa [hγΛ] at this
  have hc : form (σ : E →+* E) J (γ *ᵥ fun i => f i p.1.2) (fun i => f i p.1.1) ∈
      dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val) := by
    refine form_mem_dInv_mul (σ : E →+* E) hσ J Λ hΛ _ _ _ _ (fun y hy => ?_) (fun x hx => hcol _ x hx)
    rw [← Matrix.mulVec_smul]
    exact hmap _ (hcol _ y hy)
  refine ⟨_, hc, fun w => ?_⟩
  have hJ0 : J.det ≠ 0 := hJ.2
  have hφ : ∀ x, w.embedding ((σ : E →+* E) x) = star (w.embedding x) := fun x => hcc _ x
  have := corner_entry (σ : E →+* E) w.embedding hφ J hJ0 (A w) (hA w) γ p.1.1 p.1.2
    (fun i => f i p.1.1) (fun i => f i p.1.2) (s p.1.1) (s p.1.2) (hs _).ne' (hs _).ne'
    (had w p.1.1).2 (had w p.1.2).2
  simp only [gM]
  rw [this]

end GlobalTheory.SnMass.VolN
