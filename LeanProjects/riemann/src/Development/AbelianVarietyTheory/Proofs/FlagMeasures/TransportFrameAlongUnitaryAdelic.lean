import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep

noncomputable section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.FrMap

theorem hform_eq_dot {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (x y : Fin n → A) : hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J M : Matrix (Fin n) (Fin n) A)
    (x y : Fin n → A) : hform s J (M *ᵥ x) (M *ᵥ y) = hform s (cT s M * J * M) x y := by
  rw [hform_eq_dot, hform_eq_dot]
  have h1 : (fun i => s ((M *ᵥ x) i)) = (M.map s) *ᵥ (fun i => s (x i)) := by
    funext i; simp [mulVec, dotProduct, map_sum]
  rw [h1, cT, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm, dotProduct_mulVec,
    dotProduct_comm]

theorem inModL_map {A : Type} [CommRing A] {O : Subring A} {n : ℕ} {Λ Λ' : Submodule O (Fin n → A)} (m : ℕ)
    (P : Matrix (Fin n) (Fin n) A) (hP : ∀ z ∈ Λ, P *ᵥ z ∈ Λ') {S S' : Set (Fin n → A)}
    (hS : ∀ s ∈ S, P *ᵥ s ∈ S') {x : Fin n → A} (hx : InModL Λ m S x) : InModL Λ' m S' (P *ᵥ x) := by
  obtain ⟨s, hs, z, hz, rfl⟩ := hx
  let f : (Fin n → A) →ₗ[O] (Fin n → A) := (Matrix.mulVecLin P).restrictScalars O
  refine ⟨P *ᵥ s, ?_, P *ᵥ z, hP z hz, by rw [mulVec_add, mulVec_smul]⟩
  have : f s ∈ Submodule.span O (f '' S) := by
    rw [← Submodule.map_span]; exact Submodule.mem_map_of_mem hs
  exact Submodule.span_mono (by rintro _ ⟨t, ht, rfl⟩; exact hS t ht) this

theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (g k : ℕ) (h : UPts σ J (Ad F)), (∀ x, (h⁻¹).1.1 *ᵥ x ∈ Λ' ↔ x ∈ Λ) → ∀ Fr : AdFrame σ J Λ g k, ∃ Fr' : AdFrame σ J Λ' g k, ∀ y : UPts σ J (Ad F), (Fr.InK y.1 ↔ Fr'.InK (h⁻¹ * y * h : UPts σ J (Ad F)).1) ∧ Fr.chi y.1 = Fr'.chi (h⁻¹ * y * h : UPts σ J (Ad F)).1 := by
  intro F E _ _ _ _ _ n σ J Λ Λ' g k h hΛ Fr
  set M : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F) := h.1.1 with hM
  set Mi : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F) := (h⁻¹).1.1 with hMi
  have hMMi : M * Mi = 1 := by
    rw [hM, hMi]; show (h.1 * h.1⁻¹).val = 1; rw [mul_inv_cancel]; rfl
  have hMiM : Mi * M = 1 := by
    rw [hM, hMi]; show (h.1⁻¹ * h.1).val = 1; rw [inv_mul_cancel]; rfl
  have hinvM : ∀ u v, hR σ J (Ad F) (M *ᵥ u) (M *ᵥ v) = hR σ J (Ad F) u v := by
    intro u v; unfold hR; rw [hform_mulVec]; congr 1; exact h.2
  have hinvMi : ∀ u v, hR σ J (Ad F) (Mi *ᵥ u) (Mi *ᵥ v) = hR σ J (Ad F) u v := by
    intro u v; unfold hR; rw [hform_mulVec]; congr 1; exact (h⁻¹).2
  have hΛ'' : ∀ x, x ∈ Λ' ↔ M *ᵥ x ∈ Λ := by
    intro x; rw [← hΛ (M *ᵥ x), mulVec_mulVec, hMiM, one_mulVec]
  have hMiΛ : ∀ z ∈ Λ, Mi *ᵥ z ∈ Λ' := fun z hz => (hΛ z).2 hz
  have hMΛ' : ∀ z ∈ Λ', M *ᵥ z ∈ Λ := fun z hz => (hΛ'' z).1 hz
  have hMMiv : ∀ v, M *ᵥ (Mi *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hMMi, one_mulVec]
  have hMiMv : ∀ v, Mi *ᵥ (M *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hMiM, one_mulVec]
  let Fr' : AdFrame σ J Λ' g k :=
    { eps := Fr.eps, eps_idem := Fr.eps_idem, eps_orth := Fr.eps_orth, eps_int := Fr.eps_int,
      eps_full := by
        intro y hy
        obtain ⟨z, hz, e⟩ := Fr.eps_full (M *ᵥ y) (hMΛ' y hy)
        refine ⟨Mi *ᵥ z, hMiΛ z hz, ?_⟩
        have := congrArg (Mi *ᵥ ·) e
        simp only [mulVec_smul, hMiMv] at this
        exact this
      b := fun i => Mi *ᵥ Fr.b i, bd := fun i => Mi *ᵥ Fr.bd i,
      b_mem := fun i => hMiΛ _ (Fr.b_mem i), bd_mem := fun i => hMiΛ _ (Fr.bd_mem i),
      b_eps := fun i => by
        show Mi *ᵥ Fr.b i = Fr.eps • (Mi *ᵥ Fr.b i)
        rw [← mulVec_smul, ← Fr.b_eps i]
      bd_eps := fun i => by
        show Mi *ᵥ Fr.bd i = sigR σ (Ad F) Fr.eps • (Mi *ᵥ Fr.bd i)
        rw [← mulVec_smul, ← Fr.bd_eps i]
      dual := fun i j => by
        show ∃ t ∈ OAd F E, hR σ J (Ad F) (Mi *ᵥ Fr.bd i) (Mi *ᵥ Fr.b j) - _ = _
        rw [hinvMi]; exact Fr.dual i j
      span := by
        intro y hy
        have := inModL_map g Mi hMiΛ (S' := Set.range (fun i => Mi *ᵥ Fr.b i) ∪ Set.range (fun i => Mi *ᵥ Fr.bd i))
          (by rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩); exacts [Or.inl ⟨i, rfl⟩, Or.inr ⟨i, rfl⟩])
          (Fr.span (M *ᵥ y) (hMΛ' y hy))
        rwa [hMiMv] at this
      psi := Fr.psi, psi_add := Fr.psi_add, psi_int := Fr.psi_int, psi_rat := Fr.psi_rat }
  refine ⟨Fr', fun y => ?_⟩
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F) := y.1.1 with hY
  have hconj : ((h⁻¹ * y * h : UPts σ J (Ad F)).1 : Matrix (Fin n) (Fin n) (E ⊗[F] Ad F)) = Mi * Y * M := rfl
  have hc1 : M * (Mi * Y * M) = Y * M := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMMi, Matrix.one_mul]
  have hc3 : M * (Mi * Y * M - 1) = (Y - 1) * M := by
    rw [Matrix.mul_sub, hc1, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul]
  have hc4 : (Mi * Y * M - 1) * Mi = Mi * (Y - 1) := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hMMi, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
  have hc5 : (Mi * Y * M) * Mi = Mi * Y := by
    rw [Matrix.mul_assoc, hMMi, Matrix.mul_one]
  constructor
  · unfold AdFrame.InK
    rw [hconj]
    have key1 : ∀ x, (Mi * Y * M) *ᵥ x ∈ Λ' ↔ Y *ᵥ (M *ᵥ x) ∈ Λ := by
      intro x; rw [hΛ'', mulVec_mulVec, hc1, ← mulVec_mulVec]
    have key2 : ∀ x, (Mi * Y * M - 1) *ᵥ x ∈ Λ' ↔ (Y - 1) *ᵥ (M *ᵥ x) ∈ Λ := by
      intro x; rw [hΛ'', mulVec_mulVec, hc3, ← mulVec_mulVec]
    have keyd : ∀ x, (∀ z ∈ Λ', hR σ J (Ad F) z x ∈ OAd F E) ↔ (∀ z ∈ Λ, hR σ J (Ad F) z (M *ᵥ x) ∈ OAd F E) := by
      intro x; constructor
      · intro H z hz; have := H _ (hMiΛ z hz); rwa [← hinvM, hMMiv] at this
      · intro H z hz; have := H _ (hMΛ' z hz); rwa [hinvM] at this
    refine and_congr ?_ (and_congr ?_ ?_)
    · show (∀ x, x ∈ Λ ↔ Y *ᵥ x ∈ Λ) ↔ (∀ x, x ∈ Λ' ↔ (Mi * Y * M) *ᵥ x ∈ Λ')
      constructor
      · intro H x; rw [hΛ'', key1]; exact H _
      · intro H x; have := H (Mi *ᵥ x); rwa [hΛ'', key1, hMMiv] at this
    · constructor
      · intro H x hx; rw [key2]; exact H _ ((keyd x).1 hx)
      · intro H x hx
        have := H (Mi *ᵥ x) ((keyd _).2 (by rwa [hMMiv]))
        rwa [key2, hMMiv] at this
    · refine forall_congr' fun i => ?_
      show _ ↔ InModL Λ' g ((fun j => Mi *ᵥ Fr.b j) '' {j | j.1 < i.1}) ((Mi * Y * M - 1) *ᵥ (Mi *ᵥ Fr.b i))
      rw [mulVec_mulVec, hc4, ← mulVec_mulVec]
      constructor
      · intro H
        exact inModL_map g Mi hMiΛ (by rintro _ ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩) H
      · intro H
        have := inModL_map g M hMΛ' (S' := Fr.b '' {j | j.1 < i.1})
          (by rintro _ ⟨j, hj, rfl⟩; exact ⟨j, hj, (hMMiv _).symm⟩) H
        rwa [hMMiv] at this
  · unfold AdFrame.chi
    rw [hconj]
    show Fr.psi _ = Fr.psi _
    congr 2
    unfold supSum
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · show hR σ J (Ad F) (Fr.bd i) (Y *ᵥ Fr.b _) = hR σ J (Ad F) (Mi *ᵥ Fr.bd i) ((Mi * Y * M) *ᵥ (Mi *ᵥ Fr.b _))
      rw [mulVec_mulVec, hc5, ← mulVec_mulVec, hinvMi]
    · rfl

end GlobalTheory.St.G.FrMap
