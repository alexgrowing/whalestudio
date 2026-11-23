import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

private lemma linearIndependent_map_ringHom_complex {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) {ι : Type}
    [Fintype ι] {v : ι → Fin n → E} (hv : LinearIndependent E v) :
    LinearIndependent ℂ (fun i l => φ (v i l)) := by
  classical

  let f : (ι → E) →ₗ[E] (Fin n → E) := Fintype.linearCombination E v
  have hf : ∀ c, f c = ∑ i, c i • v i := fun c => Fintype.linearCombination_apply E v c
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [hf] at hc
    funext i
    exact (Fintype.linearIndependent_iff.mp hv) c hc i
  obtain ⟨L, hL⟩ := f.exists_leftInverse_of_injective hker
  have hB : ∀ i, LinearMap.toMatrix' L *ᵥ v i = Pi.single i 1 := by
    intro i
    rw [LinearMap.toMatrix'_mulVec]
    have h1 := LinearMap.congr_fun hL (Pi.single i 1)
    have h2 : f (Pi.single i 1) = v i := by
      rw [hf]
      simp [Pi.single_apply]
    rw [LinearMap.comp_apply, h2] at h1
    exact h1
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hcol : ∀ i k, ((LinearMap.toMatrix' L).map φ *ᵥ fun l => φ (v i l)) k
      = if k = i then 1 else 0 := by
    intro i k
    have h3 := RingHom.map_mulVec φ (LinearMap.toMatrix' L) (v i) k
    rw [hB i] at h3
    rw [show (fun l => φ (v i l)) = φ ∘ v i from rfl, ← h3]
    by_cases hki : k = i
    · subst hki; simp
    · simp [hki]
  have h4 := congrArg (fun w => ((LinearMap.toMatrix' L).map φ *ᵥ w) j) hc
  simp only [Matrix.mulVec_zero, Pi.zero_apply] at h4
  rw [← h4, ← Matrix.mulVecLin_apply, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, Matrix.mulVecLin_apply, hcol, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private lemma map_mem_span_image_of_mem_span {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ)
    (t : Set (Fin n → E)) {x : Fin n → E} (hx : x ∈ Submodule.span E t) :
    (fun l => φ (x l)) ∈ Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' t) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have h0 : (fun l => φ ((0 : Fin n → E) l)) = 0 := by funext l; simp
    rw [h0]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have h1 : (fun l => φ ((y + z) l)) = (fun l => φ (y l)) + (fun l => φ (z l)) := by
      funext l; simp
    rw [h1]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have h1 : (fun l => φ ((c • y) l)) = φ c • (fun l => φ (y l)) := by
      funext l; simp
    rw [h1]
    exact Submodule.smul_mem _ _ hy

theorem finrank_span_image_ringHom {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ)
    (s : Set (Fin n → E)) :
    Module.finrank ℂ (Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' s))
      = Module.finrank E (Submodule.span E s) := by
  classical
  let V := Submodule.span E s
  let b := Module.finBasis E V
  let v : Fin (Module.finrank E V) → Fin n → E := fun i => (b i : Fin n → E)
  have hv : LinearIndependent E v := b.linearIndependent.map' V.subtype V.ker_subtype
  have hvV : ∀ i, v i ∈ V := fun i => (b i).2
  have hspan : Submodule.span E (Set.range v) = V := by
    have hr : Set.range v = V.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have heq : Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' s)
      = Submodule.span ℂ (Set.range fun i l => φ (v i l)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span E (Set.range v) := by
        rw [hspan]; exact Submodule.subset_span hx
      have h := map_mem_span_image_of_mem_span φ _ hx'
      rw [← Set.range_comp] at h
      exact h
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact map_mem_span_image_of_mem_span φ s (hvV i)
  rw [heq, finrank_span_eq_card (linearIndependent_map_ringHom_complex φ hv), Fintype.card_fin]

theorem finrank_locFlag_and_lowers (E : Type) [Field E] [NumberField E] (n : ℕ) (φ : E →+* ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (hP : IsUnit P) :
    (∀ b, Module.finrank ℂ (locFlag φ P F b) = Formalism.HN.rkK (F b)) ∧
      ∀ c, ∀ T ∈ lowers F c, P⁻¹ * T.map φ * P ∈ lowers (locFlag φ P F) c := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  refine ⟨fun b => ?_, fun c T hT => ?_⟩
  · have hinj : Function.Injective (Matrix.mulVecLin P⁻¹) := by
      intro x y hxy
      have h := congrArg (fun z => P *ᵥ z) hxy
      simpa [Matrix.mulVec_mulVec, hPP] using h
    have himg : locFlag φ P F b = Submodule.map (Matrix.mulVecLin P⁻¹)
        (Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' (F b : Set (Fin n → E)))) := by
      rw [Submodule.map_span, ← Set.image_comp]
      rfl
    rw [himg, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, finrank_span_image_ringHom]
    rfl
  · rw [GlobalTheory.RadCov.mem_lowers] at hT ⊢
    intro b y hy
    have key : locFlag φ P F (b + c + 1)
        ≤ Submodule.comap (Matrix.mulVecLin (P⁻¹ * T.map φ * P)) (locFlag φ P F b) := by
      rw [locFlag, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      refine Submodule.subset_span ⟨T *ᵥ x, hT b x hx, ?_⟩
      have h1 : (fun l => φ ((T *ᵥ x) l)) = T.map φ *ᵥ (fun l => φ (x l)) := by
        funext l; exact RingHom.map_mulVec φ T x l
      dsimp only
      rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (P⁻¹ * T.map φ) P P⁻¹,
        hPP, Matrix.mul_one]
    exact key hy

end GlobalTheory.RadCov
