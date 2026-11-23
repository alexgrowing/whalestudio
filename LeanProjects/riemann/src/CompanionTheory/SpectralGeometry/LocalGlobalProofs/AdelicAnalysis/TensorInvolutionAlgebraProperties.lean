import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.KAlg

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem exists_basis_one_delta (σ : E →ₐ[F] E) {δ : E} (hδ : σ δ = -δ) (h0 : δ ≠ 0)
    (hfr : Module.finrank F E = 2) (h2 : (2 : F) ≠ 0) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = δ := by
  have li : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : s • (1 : E) + t • (-δ) = 0 := by
      have := congrArg σ hst
      simpa [map_add, map_smul, hδ] using this
    have hs : (2 * s) • (1 : E) = 0 := by
      have : (2 * s) • (1 : E) = (s • (1 : E) + t • δ) + (s • (1 : E) + t • (-δ)) := by module
      rw [this, hst, h1, add_zero]
    have hs0 : s = 0 := by
      rcases smul_eq_zero.1 hs with h | h
      · exact (mul_eq_zero.1 h).resolve_left h2
      · exact absurd h one_ne_zero
    subst hs0
    refine ⟨rfl, ?_⟩
    rcases smul_eq_zero.1 (by simpa using hst : t • δ = 0) with h | h
    · exact h
    · exact absurd h h0
  refine ⟨basisOfLinearIndependentOfCardEqFinrank li (by simp [hfr]), ?_, ?_⟩
  · simp
  · simp

variable {R : Type} [CommRing R] [Algebra F R]

theorem exists_coord (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ)
    (y : R ⊗[F] E) : ∃ a c : R, y = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ := by
  let B := Algebra.TensorProduct.basis R b
  refine ⟨B.repr y 0, B.repr y 1, ?_⟩
  have h := (B.sum_repr y).symm
  rw [Fin.sum_univ_two] at h
  have e0 : B 0 = (1 : R) ⊗ₜ[F] (1 : E) := by simp [B, hb0]
  have e1 : B 1 = (1 : R) ⊗ₜ[F] δ := by simp [B, hb1]
  rw [e0, e1, TensorProduct.smul_tmul', TensorProduct.smul_tmul'] at h
  simpa using h

theorem coord_inj (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ)
    {a c a' c' : R} (h : a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ = a' ⊗ₜ[F] (1 : E) + c' ⊗ₜ[F] δ) :
    a = a' ∧ c = c' := by
  let B := Algebra.TensorProduct.basis R b
  have e : ∀ p q : R, p ⊗ₜ[F] (1 : E) + q ⊗ₜ[F] δ = p • B 0 + q • B 1 := by
    intro p q
    have e0 : B 0 = (1 : R) ⊗ₜ[F] (1 : E) := by simp [B, hb0]
    have e1 : B 1 = (1 : R) ⊗ₜ[F] δ := by simp [B, hb1]
    rw [e0, e1, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp
  rw [e, e] at h
  have h0 := congrArg (fun y => B.repr y 0) h
  have h1 := congrArg (fun y => B.repr y 1) h
  simp at h0 h1
  exact ⟨h0, h1⟩

theorem tmul_one_injective (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ) :
    Function.Injective (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E) := by
  intro p q h
  have h' : p ⊗ₜ[F] (1 : E) + (0 : R) ⊗ₜ[F] δ = q ⊗ₜ[F] (1 : E) + (0 : R) ⊗ₜ[F] δ := by
    simpa using h
  exact (coord_inj b hb0 hb1 h').1

end Coord

theorem algebra_tensor_invol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R],
    IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsUnit (2 : R ⊗[F] E) ∧
      (∀ y, sigR R σ (sigR R σ y) = y) ∧ (∃ δ : R ⊗[F] E, IsUnit δ ∧ sigR R σ δ = -δ) ∧
      (∀ y : R ⊗[F] E, sigR R σ y = y → ∃ r : R, y = r ⊗ₜ[F] (1 : E)) ∧
      ∀ r : R, IsUnit (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) ↔ IsUnit r := by
  intro F E _ _ _ _ _ σ h R _ _ _ _
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hc
    push Not at hc
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := h.2.1
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have h' := h.2.2.2 τ x
    rw [hc] at h'
    simpa [ComplexEmbedding.conjugate_coe_eq] using h'.symm
  obtain ⟨x₀, hx₀⟩ := hne
  set δ : E := x₀ - σ x₀ with hδdef
  have hδ : σ δ = -δ := by simp [hδdef, hσσ]
  have hδ0 : δ ≠ 0 := fun e => hx₀ (sub_eq_zero.1 e).symm
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  obtain ⟨b, hb0, hb1⟩ := exists_basis_one_delta σ hδ hδ0 h.2.2.1 h2F
  have : Module.Finite F E := Module.Finite.of_basis b
  have hsig : ∀ (a : R) (e : E), sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := fun _ _ => rfl
  have h2R : IsUnit (2 : R) := by
    have := (IsUnit.mk0 (2 : F) h2F).map (algebraMap F R)
    rwa [map_ofNat] at this
  have half : ∀ a : R, a + a = 0 → a = 0 := fun a ha =>
    (h2R.mul_right_eq_zero).1 (by rw [two_mul, ha])
  have hnil : ∀ a : R, IsNilpotent (a ⊗ₜ[F] (1 : E) : R ⊗[F] E) → a = 0 := fun a ha =>
    ((IsNilpotent.map_iff (tmul_one_injective (R := R) b hb0 hb1)).1 ha).eq_zero
  have hδu : IsUnit ((1 : R) ⊗ₜ[F] δ : R ⊗[F] E) :=
    (IsUnit.mk0 δ hδ0).map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E)
  refine ⟨IsArtinianRing.of_finite R _, ⟨fun x hx => ?_⟩, ?_, fun y => ?_, ⟨_, hδu, ?_⟩, fun y hy => ?_, fun r => ⟨?_, ?_⟩⟩
  · obtain ⟨a, c, rfl⟩ := exists_coord b hb0 hb1 x
    have hs := hx.map (sigR R σ)
    have hadd := (Commute.all _ _).isNilpotent_add hx hs
    have e1 : (a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ) + sigR R σ (a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ) =
        (a + a) ⊗ₜ[F] (1 : E) := by
      rw [map_add, hsig, hsig, map_one, hδ, TensorProduct.tmul_neg, TensorProduct.add_tmul]
      abel
    rw [e1] at hadd
    have ha : a = 0 := half a (hnil _ hadd)
    subst ha
    rw [TensorProduct.zero_tmul, zero_add] at hx ⊢
    have hm : IsNilpotent ((c ⊗ₜ[F] δ) * ((1 : R) ⊗ₜ[F] δ⁻¹) : R ⊗[F] E) :=
      (Commute.all _ _).isNilpotent_mul_right (show IsNilpotent (c ⊗ₜ[F] δ : R ⊗[F] E) from hx)
    have e2 : ((c ⊗ₜ[F] δ) * ((1 : R) ⊗ₜ[F] δ⁻¹) : R ⊗[F] E) = c ⊗ₜ[F] (1 : E) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hδ0]
    rw [e2] at hm
    rw [hnil c hm, TensorProduct.zero_tmul]
  · have := (IsUnit.mk0 (2 : F) h2F).map (algebraMap F (R ⊗[F] E))
    rwa [map_ofNat] at this
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | tmul a e => rw [hsig, hsig, hσσ]
  · rw [hsig, hδ, TensorProduct.tmul_neg]
  · obtain ⟨a, c, rfl⟩ := exists_coord b hb0 hb1 y
    rw [map_add, hsig, hsig, map_one, hδ, TensorProduct.tmul_neg, ← TensorProduct.neg_tmul] at hy
    have hc := (coord_inj b hb0 hb1 hy).2
    have : c = 0 := half c (by nth_rewrite 1 [← hc]; simp)
    exact ⟨a, by rw [this, TensorProduct.zero_tmul, add_zero]⟩
  · rintro ⟨u, hu⟩
    obtain ⟨a, c, hac⟩ := exists_coord b hb0 hb1 (u⁻¹ : (R ⊗[F] E)ˣ).val
    have e : (r * a) ⊗ₜ[F] (1 : E) + (r * c) ⊗ₜ[F] δ =
        (1 : R) ⊗ₜ[F] (1 : E) + (0 : R) ⊗ₜ[F] δ := by
      have : (u : R ⊗[F] E) * (u⁻¹ : (R ⊗[F] E)ˣ).val = 1 := u.mul_inv
      rw [hu, hac, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, one_mul, Algebra.TensorProduct.one_def] at this
      rw [this, TensorProduct.zero_tmul, add_zero]
    exact IsUnit.of_mul_eq_one a (coord_inj b hb0 hb1 e).1
  · intro hr
    exact hr.map (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E)

end GlobalTheory.CompanionTheory.SW.KAlg
