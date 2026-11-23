import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualTupleIdealsCastAdd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowIsometryEntriesInModelCoordinatesStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LiftEntry

theorem eI_inj {k r : ℕ} {a b : Fin r} : eI k r a = eI k r b ↔ a = b := by
  simp [eI, Fin.ext_iff]

theorem eI_ne_esI {k r : ℕ} (a b : Fin r) : eI k r a ≠ esI k r b := by
  simp only [eI, esI, ne_eq, Fin.ext_iff]; omega

theorem eI_ne_wI {k r : ℕ} (a : Fin r) (j : Fin (k + 1)) : eI k r a ≠ wI k r j := by
  simp only [eI, wI, ne_eq, Fin.ext_iff]; omega

theorem Hpk_esI {k r : ℕ} (b : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r b) j = if j = eI k r b then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem herm_single {k r : ℕ} (b : Fin r) (c : ℂ) (j : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec j) (c • bvec (esI k r b)) = if j = eI k r b then star c else 0 := by
  simp only [herm, bvec, dotProduct, mulVec, Pi.star_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single (esI k r b)]
  · simp only [if_true, mul_one, star_mul', star_one]
    rw [Finset.sum_eq_single j]
    · simp [Hpk_esI]
    · intro m _ hm; simp [hm]
    · simp
  · intro m _ hm; simp [hm]
  · simp

theorem wI_ne_eI {k r : ℕ} (j : Fin (k + 1)) (a : Fin r) : wI k r j ≠ eI k r a := (eI_ne_wI a j).symm

theorem esI_ne_eI {k r : ℕ} (a b : Fin r) : esI k r a ≠ eI k r b := (eI_ne_esI b a).symm

end GlobalTheory.SnMass.VolN.LiftEntry

namespace GlobalTheory.SnMass.VolN.LiftEntry

theorem form_smul_left {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (c : E) (x z : Fin n → E) : form σ J (c • x) z = c * form σ J x z := by
  simp [form, mulVec_smul, dotProduct_smul]

theorem form_smul_right {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (c : E) (x z : Fin n → E) : form σ J x (c • z) = σ c * form σ J x z := by
  simp only [form, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem form_col {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} {a b : Type} [Fintype a] [Fintype b]
    (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) b E) (Y : Matrix (Fin n) a E) (i : a) (j : b) :
    form σ J (fun l => X l j) (fun l => Y l i) = pairM σ J X Y i j := by
  simp only [form, pairM, cT, dotProduct, mulVec, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end GlobalTheory.SnMass.VolN.LiftEntry

namespace GlobalTheory.SnMass.VolN.LiftEntry

theorem lift_entry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inl p) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inl p) → degB r β ≤ degB r (.inl p) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV p l hl
  have hV' := hV
  obtain ⟨hcm, -, -, -, -, hdu, htup, -, hs, had⟩ := hV'
  have hi : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    change τ (σ (σ x)) = _
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  obtain ⟨u, hu, hlu⟩ := hl
  obtain ⟨⟨a, b⟩, hab⟩ := p
  simp only at hu hlu hab ⊢
  set y : Fin (2 * r + k + 1) → E := (-(σ u)) • fun i => f i b with hy
  refine ⟨rowE (σ : E →+* E) J (fun i => P i a.castSucc) y 0, ?_, ?_⟩
  · refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV a y 0 (fun c hc => ?_) ?_ (fun c hc => ?_)
      (FractionalIdeal.zero_mem _)
    · rw [hy, form_smul_left, form_col, hdu.1]
      have : c.castSucc ≠ b.castSucc := fun h => absurd (Fin.castSucc_injective _ h ▸ hc) (not_le.2 hab)
      simp [this]
    · rw [hy, form_smul_left, form_smul_right, form_col, hdu.2]
      simp
    · have hsu : (σ : E →+* E) u ∈ dInv E (r - a.val) * (dInv E (r - b.val))⁻¹ :=
        (GlobalTheory.SnMass.FrameDual.Stab.mul (GlobalTheory.SnMass.FrameDual.stab_dInv hi _)
          ((GlobalTheory.SnMass.FrameDual.stab_dInv hi _).inv hi (GlobalTheory.SnMass.FrameDual.dInv_ne_zero _))) u hu
      have hm : c * σ u ∈ (dInv E (r - b.val))⁻¹ := by
        have := FractionalIdeal.mul_mem_mul hc hsu
        rwa [← mul_assoc, inv_mul_cancel₀ (GlobalTheory.SnMass.FrameDual.dInv_ne_zero _), one_mul] at this
      have e : c • y = (-(c * σ u)) • fun i => sideM P f i (Fin.natAdd (r + 1) b) := by
        ext i; simp [hy, sideM, mul_comm, mul_left_comm]
      rw [e]
      refine htup (Submodule.subset_span ⟨Fin.natAdd (r + 1) b, -(c * σ u), ?_, rfl⟩)
      rw [GlobalTheory.SnMass.FrameDual.frameDualTupleIdeals_natAdd]
      exact Submodule.neg_mem _ hm
  · have hv : ∀ w : InfinitePlace E, (A w).mulVec (fun l => w.embedding (y l)) =
        (-(star (w.embedding u)) * ((s b)⁻¹ : ℂ)) • bvec (esI k r b) := by
      intro w
      have e : (fun l => w.embedding (y l)) = (-(w.embedding (σ u))) • fun l => w.embedding (f l b) := by
        ext l; simp [hy]
      rw [e, mulVec_smul, (had w b).2, smul_smul, hcm.2.2.2]
    have key : ∀ (w : InfinitePlace E) (a' : Fin r) (j : Fin (2 * r + k + 1)),
        gM A (rowE (σ : E →+* E) J (fun i => P i a.castSucc) y 0) w (eI k r a') j =
          (if eI k r a' = j then 1 else 0) - (if a' = a ∧ j = eI k r b then
            (s a : ℂ) * star (-(star (w.embedding u)) * ((s b)⁻¹ : ℂ)) else 0) := by
      intro w a' j
      rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV a y 0 w, hv w, herm_single]
      simp [bvec, Pi.single_apply, eI_ne_esI, eI_inj, ite_and]
    refine ⟨fun w => ?_, fun β hβ _ w => ?_⟩
    · change gM A _ w (eI k r a) (eI k r b) = l w
      rw [key, hlu]
      simp only [eI_inj, hab.ne, if_false, true_and, if_true, zero_sub]
      push_cast
      simp only [star_mul', star_neg, star_star, Complex.star_def, Complex.conj_ofReal, map_inv₀, Complex.conj_conj]
      ring
    · rcases β with ⟨⟨a', b'⟩, hab'⟩ | a' | ⟨⟨a', b'⟩, hab'⟩ | a'
      · change gM A _ w (eI k r a') (eI k r b') = 0
        rw [key]
        have hne : ¬ (a' = a ∧ eI k r b' = eI k r b) := by
          rintro ⟨rfl, h⟩
          obtain rfl := eI_inj.1 h
          exact hβ rfl
        have hne' : a' ≠ b' := ne_of_lt hab'
        rw [if_neg hne, if_neg (fun h => hne' (eI_inj.1 h)), sub_zero]
      · change (fun j => gM A _ w (eI k r a') (wI k r j)) = (0 : Fin (k + 1) → ℂ)
        funext j
        rw [key]
        simp [eI_ne_wI, wI_ne_eI]
      · change gM A _ w (eI k r a') (esI k r b') = 0
        rw [key]
        simp [eI_ne_esI, esI_ne_eI]
      · change (gM A _ w (eI k r a') (esI k r a')).im = 0
        rw [key]
        simp [eI_ne_esI, esI_ne_eI]

end GlobalTheory.SnMass.VolN.LiftEntry
