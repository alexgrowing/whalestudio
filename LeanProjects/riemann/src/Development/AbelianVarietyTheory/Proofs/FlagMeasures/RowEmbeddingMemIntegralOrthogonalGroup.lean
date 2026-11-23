import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualTupleIdealsCastAdd

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.RowIso

section Alg
variable {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem form_add_left (x x' y : Fin n → E) : form σ J (x + x') y = form σ J x y + form σ J x' y := by
  simp [form, Matrix.mulVec_add, dotProduct_add]

theorem form_sub_left (x x' y : Fin n → E) : form σ J (x - x') y = form σ J x y - form σ J x' y := by
  simp [form, Matrix.mulVec_sub, dotProduct_sub]

theorem form_smul_left (c : E) (x y : Fin n → E) : form σ J (c • x) y = c * form σ J x y := by
  simp [form, Matrix.mulVec_smul, dotProduct_smul]

theorem form_add_right (x y y' : Fin n → E) : form σ J x (y + y') = form σ J x y + form σ J x y' := by
  simp [form, dotProduct, add_mul, Finset.sum_add_distrib]

theorem form_sub_right (x y y' : Fin n → E) : form σ J x (y - y') = form σ J x y - form σ J x y' := by
  simp [form, dotProduct, sub_mul, Finset.sum_sub_distrib]

theorem form_neg_right (x y : Fin n → E) : form σ J x (-y) = -form σ J x y := by
  simp [form, dotProduct]

theorem form_neg_left (x y : Fin n → E) : form σ J (-x) y = -form σ J x y := by
  simp [form, Matrix.mulVec_neg]

theorem form_smul_right (c : E) (x y : Fin n → E) : form σ J x (c • y) = σ c * form σ J x y := by
  simp [form, dotProduct, Finset.mul_sum, mul_assoc]

theorem form_herm (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    form σ J x y = σ (form σ J y x) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem rowE_mulVec (e y : Fin n → E) (t : E) (x : Fin n → E) :
    rowE σ J e y t *ᵥ x = x + form σ J x e • (y + t • e) - form σ J x y • e := by
  ext i
  simp only [rowE, mulVec, dotProduct, form, vecMul, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm (f := fun (a b : Fin n) => y i * (σ (e b) * (J b a * x a))),
    Finset.sum_comm (f := fun (a b : Fin n) => t * (e i * (σ (e b) * (J b a * x a)))),
    Finset.sum_comm (f := fun (a b : Fin n) => e i * (σ (y b) * (J b a * x a))), ← Finset.sum_add_distrib]
  congr 2
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  · funext a
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

theorem isUn_of_form (g : Matrix (Fin n) (Fin n) E)
    (h : ∀ x x', form σ J (g *ᵥ x) (g *ᵥ x') = form σ J x x') : IsUn σ J g := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  simp only [form, dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, apply_ite σ, map_one, map_zero, ite_mul, one_mul, zero_mul] at this
  rw [← this]
  simp only [IsUn, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Alg
end GlobalTheory.SnMass.VolN.RowIso

namespace GlobalTheory.SnMass.VolN.RowIso

section Iso
variable {E : Type} [Field E] {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
  (hJ : ∀ i j, σ (J j i) = J i j) {e y : Fin n → E} {t : E} (he : form σ J e e = 0)
  (hye : form σ J y e = 0) (ht : form σ J y y + t + σ t = 0)
include hσ hJ he hye ht

theorem form_rowE (x x' : Fin n → E) :
    form σ J (rowE σ J e y t *ᵥ x) (rowE σ J e y t *ᵥ x') = form σ J x x' := by
  have hey : form σ J e y = 0 := by rw [form_herm σ J hσ hJ, hye, map_zero]
  have h1 : form σ J y x' = σ (form σ J x' y) := form_herm σ J hσ hJ _ _
  have h2 : form σ J e x' = σ (form σ J x' e) := form_herm σ J hσ hJ _ _
  simp only [rowE_mulVec, form_add_left, form_sub_left, form_smul_left, form_add_right, form_sub_right,
    form_smul_right, map_add, map_sub, map_mul, hσ, he, hye, hey, h1, h2]
  linear_combination (form σ J x e * σ (form σ J x' e)) * ht

theorem rowE_inv (x : Fin n → E) :
    rowE σ J e y t *ᵥ (rowE σ J e (-y) (σ t) *ᵥ x) = x := by
  have hey : form σ J e y = 0 := by rw [form_herm σ J hσ hJ, hye, map_zero]
  have hα : form σ J (rowE σ J e (-y) (σ t) *ᵥ x) e = form σ J x e := by
    simp only [rowE_mulVec, form_add_left, form_sub_left, form_smul_left, form_neg_left, he, hye]
    ring
  have hβ : form σ J (rowE σ J e (-y) (σ t) *ᵥ x) y = form σ J x y - form σ J x e * form σ J y y := by
    simp only [rowE_mulVec, form_add_left, form_sub_left, form_smul_left, form_neg_left, form_neg_right, hey]
    ring
  rw [rowE_mulVec σ J e y t, hα, hβ, rowE_mulVec σ J e (-y) (σ t) x]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, form_neg_right]
  linear_combination (form σ J x e * e i) * ht

end Iso

section Lat
variable {E : Type} [Field E] [NumberField E]

open GlobalTheory.SnMass.FrameDual in

theorem rowE_mem {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hΛ : GlobalTheory.SgGlob.SelfDual σ J Λ) {𝔞 : FractionalIdeal (𝓞 E)⁰ E}
    (h0 : 𝔞 ≠ 0) (hs : Stab σ 𝔞) {e y : Fin n → E} {t : E} (he : ∀ c ∈ 𝔞, c • e ∈ Λ)
    (hy : ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ) (ht : t ∈ 𝔞 * 𝔞) {v : Fin n → E} (hv : v ∈ Λ) :
    rowE σ J e y t *ᵥ v ∈ Λ := by
  have hO : ∀ w ∈ Λ, form σ J v w ∈ (algebraMap (𝓞 E) E).range := (hΛ.2 v).1 hv
  have hα : form σ J v e ∈ 𝔞⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff h0]
    intro z hz
    have := hO _ (he _ (hs z hz))
    rw [form_smul_right, hσ, mul_comm] at this
    obtain ⟨d, hd⟩ := this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨d, hd⟩
  have hβ : form σ J v y ∈ 𝔞 := by
    have h0' : 𝔞⁻¹ ≠ 0 := inv_ne_zero h0
    rw [← inv_inv 𝔞, FractionalIdeal.mem_inv_iff h0']
    intro z hz
    have := hO _ (hy _ (Stab.inv hσ hs h0 z hz))
    rw [form_smul_right, hσ, mul_comm] at this
    obtain ⟨d, hd⟩ := this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨d, hd⟩
  have hγ : t * form σ J v e ∈ 𝔞 := by
    have := FractionalIdeal.mul_mem_mul ht hα
    rwa [mul_assoc, mul_inv_cancel₀ h0, mul_one] at this
  have hvec : rowE σ J e y t *ᵥ v =
      v + form σ J v e • y + (t * form σ J v e) • e - form σ J v y • e := by
    rw [rowE_mulVec, smul_add, smul_smul, mul_comm (form σ J v e) t, add_assoc]
  rw [hvec]
  exact Λ.sub_mem (Λ.add_mem (Λ.add_mem hv (hy _ hα)) (he _ hγ)) (he _ hβ)

end Lat

end GlobalTheory.SnMass.VolN.RowIso

namespace GlobalTheory.SnMass.VolN.RowIso

theorem form_col_col {E : Type} [Field E] (σ : E →+* E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin m) E) (b c : Fin m) :
    form σ J (fun i => P i b) (fun i => P i c) = pairM σ J P P c b := by
  simp only [form, pairM, cT, Matrix.mul_apply, dotProduct, mulVec, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  ring

open GlobalTheory.SnMass.FrameDual in

theorem rowE_mem_GN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (y : Fin (2 * r + k + 1) → E) (t : E), (∀ c : Fin r, c ≤ a → form (σ : E →+* E) J y (fun i => P i c.castSucc) = 0) → form (σ : E →+* E) J y y + t + σ t = 0 → (∀ c ∈ (dInv E (r - a.val))⁻¹, c • y ∈ Λ) → t ∈ dInv E (2 * (r - a.val)) → rowE (σ : E →+* E) J (fun i => P i a.castSucc) y t ∈ GN (σ : E →+* E) J Λ P := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV a y t hyc hyt hyΛ htI
  obtain ⟨hcm, -, hJ, hΛ, hP, -, htup, -⟩ := hV
  set σ' : E →+* E := (σ : E →+* E) with hσ'
  have hσ : ∀ x, σ' (σ' x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have h := hcm.2.2.2 τ
    simp only [hσ', AlgHom.coe_toRingHom, h, star_star]
  have hJ' : ∀ i j, σ' (J j i) = J i j := hJ.1
  have hyt' : form σ' J y y + t + σ' t = 0 := hyt
  set e : Fin (2 * r + k + 1) → E := fun i => P i a.castSucc with he_def
  set 𝔞 : FractionalIdeal (𝓞 E)⁰ E := dInv E (r - a.val) with h𝔞
  have heb : ∀ b c : Fin r, form σ' J (fun i => P i b.castSucc) (fun i => P i c.castSucc) = 0 := by
    intro b c
    rw [form_col_col, hP.2, TF, Matrix.diagonal_apply]
    split_ifs with h1 h2 <;> first | rfl | exact absurd h2 (Fin.castSucc_ne_last c)
  have hee : form σ' J e e = 0 := heb a a
  have hye : form σ' J y e = 0 := hyc a le_rfl
  have hyb : ∀ b : Fin r, b ≤ a → form σ' J (fun i => P i b.castSucc) y = 0 := by
    intro b hb
    rw [form_herm σ' J hσ hJ', hyc b hb, map_zero]
  have h0 : 𝔞 ≠ 0 := dInv_ne_zero _
  have hs : Stab σ' 𝔞 := stab_dInv hσ _
  have he𝔞 : ∀ c ∈ 𝔞, c • e ∈ Λ := by
    intro c hc
    refine htup (Submodule.subset_span ⟨Fin.castAdd r a.castSucc, c, ?_, ?_⟩)
    · rw [frameDualTupleIdeals_castAdd]; exact hc
    · funext i
      simp [sideM, he_def]
  have ht2 : t ∈ 𝔞 * 𝔞 := by
    rw [h𝔞, dInv, ← pow_add, ← two_mul]
    exact htI
  refine ⟨⟨isUn_of_form σ' J _ (form_rowE hσ hJ' hee hye hyt'), ?_, ?_⟩, ?_⟩
  · refine ⟨Matrix.of fun i j => (if i = j then 1 else 0) -
        (if i = a then form σ' J (fun l => P l j.castSucc) y else 0), ?_, ?_⟩
    · intro i j
      refine ⟨fun hji => ?_, fun hij => ?_⟩
      · have hne : i ≠ j := (ne_of_lt hji).symm
        by_cases hia : i = a
        · subst hia
          simp [hne, hyb j (le_of_lt hji)]
        · simp [hne, hia]
      · subst hij
        by_cases hia : i = a
        · subst hia
          simp [hyb i le_rfl]
        · simp [hia]
    · ext l j
      change (rowE σ' J e y t *ᵥ fun m => P m j.castSucc) l = ∑ i : Fin r, P l i.castSucc *
        ((if i = j then 1 else 0) - (if i = a then form σ' J (fun l => P l j.castSucc) y else 0))
      rw [rowE_mulVec, heb j a]
      simp only [Matrix.of_apply, eOf, Matrix.submatrix_apply, id, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, zero_mul, add_zero, he_def]
      ring
  · intro v hv
    have hve : form σ' J v e = 0 := by
      have := congrFun hv a
      rw [← Matrix.mulVec_mulVec] at this
      simpa [form, cT, mulVec, dotProduct, eOf, he_def] using this
    refine ⟨Pi.single a (-form σ' J v y), ?_⟩
    rw [rowE_mulVec, hve, Matrix.mulVec_single]
    ext l
    simp [eOf, he_def] <;> ring
  · apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact rowE_mem hσ hΛ h0 hs he𝔞 hyΛ ht2 hv
    · intro v hv
      have hy' : ∀ c ∈ 𝔞⁻¹, c • (-y) ∈ Λ := fun c hc => by
        rw [smul_neg]; exact Λ.neg_mem (hyΛ c hc)
      refine ⟨rowE σ' J e (-y) (σ' t) *ᵥ v, rowE_mem hσ hΛ h0 hs he𝔞 hy' (hs.mul hs t ht2) hv, ?_⟩
      exact rowE_inv hσ hJ' hee hye hyt' v

end GlobalTheory.SnMass.VolN.RowIso
