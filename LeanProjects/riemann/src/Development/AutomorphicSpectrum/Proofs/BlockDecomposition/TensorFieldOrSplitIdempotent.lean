import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.Dichotomy

section Core

variable {K R : Type} [Field K] [CommRing R] [Algebra K R]

theorem core (s : R →+* R) (T : R) (D : K) (hT : T * T = algebraMap K R D) (hD : D ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsK : ∀ x, s (algebraMap K R x) = algebraMap K R x) (hsT : s T = -T)
    (hspan : ∀ z : R, ∃ x y : K, z = algebraMap K R x + algebraMap K R y * T)
    (hind : ∀ x y : K, algebraMap K R x + algebraMap K R y * T = 0 → x = 0 ∧ y = 0) :
    IsField R ∨ ∃ e : R, e * e = e ∧ e + s e = 1 ∧ e * s e = 0 := by
  by_cases hsq : ∃ t : K, t * t = D
  · obtain ⟨t, ht⟩ := hsq
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hD (by rw [← ht, mul_zero])
    right
    have hw : (algebraMap K R t⁻¹ * T) * (algebraMap K R t⁻¹ * T) = 1 := by
      calc (algebraMap K R t⁻¹ * T) * (algebraMap K R t⁻¹ * T)
          = algebraMap K R t⁻¹ * algebraMap K R t⁻¹ * (T * T) := by ring
        _ = algebraMap K R (t⁻¹ * t⁻¹ * D) := by rw [hT, map_mul, map_mul]
        _ = 1 := by
          have : t⁻¹ * t⁻¹ * D = 1 := by
            rw [← ht]
            field_simp
          rw [this, map_one]
    have hh : algebraMap K R 2⁻¹ * 2 = 1 := by
      have h : algebraMap K R 2 = 2 := map_ofNat _ 2
      rw [← h, ← map_mul, inv_mul_cancel₀ h2, map_one]
    have hs : s (algebraMap K R 2⁻¹ * (1 + algebraMap K R t⁻¹ * T)) =
        algebraMap K R 2⁻¹ * (1 - algebraMap K R t⁻¹ * T) := by
      rw [map_mul, map_add, map_mul, hsK, hsK, hsT, map_one]
      ring
    refine ⟨algebraMap K R 2⁻¹ * (1 + algebraMap K R t⁻¹ * T), ?_, ?_, ?_⟩
    · generalize algebraMap K R t⁻¹ * T = w at hw
      generalize algebraMap K R 2⁻¹ = h at hh
      linear_combination h ^ 2 * hw + h * (1 + w) * hh
    · rw [hs]
      generalize algebraMap K R t⁻¹ * T = w
      generalize algebraMap K R 2⁻¹ = h at hh
      linear_combination hh
    · rw [hs]
      generalize algebraMap K R t⁻¹ * T = w at hw
      generalize algebraMap K R 2⁻¹ = h at hh
      linear_combination (-h ^ 2) * hw
  · left
    have h10 : (1 : R) ≠ 0 := fun h =>
      one_ne_zero (hind 1 0 (by rw [map_one, map_zero, zero_mul, add_zero, h])).1
    refine ⟨⟨1, 0, h10⟩, mul_comm, ?_⟩
    intro z hz
    obtain ⟨x, y, rfl⟩ := hspan z
    have hn : x * x - D * (y * y) ≠ 0 := by
      intro h0
      by_cases hy : y = 0
      · subst hy
        have hx : x = 0 := by simpa using h0
        exact hz (by rw [hx, map_zero, zero_mul, add_zero])
      · refine hsq ⟨x / y, ?_⟩
        field_simp
        linear_combination h0
    refine ⟨algebraMap K R (x * (x * x - D * (y * y))⁻¹) - algebraMap K R (y * (x * x - D * (y * y))⁻¹) * T, ?_⟩
    have hni : algebraMap K R (x * x - D * (y * y)) * algebraMap K R (x * x - D * (y * y))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hn, map_one]
    have hnn : algebraMap K R (x * x - D * (y * y)) =
        algebraMap K R x * algebraMap K R x - algebraMap K R D * (algebraMap K R y * algebraMap K R y) := by
      simp only [map_sub, map_mul]
    rw [map_mul, map_mul]
    generalize algebraMap K R (x * x - D * (y * y))⁻¹ = N at hni ⊢
    generalize algebraMap K R (x * x - D * (y * y)) = n at hni hnn
    generalize algebraMap K R x = X at hnn ⊢
    generalize algebraMap K R y = Y at hnn ⊢
    generalize algebraMap K R D = D' at hT hnn
    linear_combination (-(Y * Y * N)) * hT + hni - N * hnn

end Core

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_moved {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ y, σ y ≠ y := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 τ x
    rw [hc x] at this
    exact this.symm)
  have hcx := h.2.1.isComplex (InfinitePlace.mk τ)
  exact (InfinitePlace.isComplex_mk_iff.1 hcx) hreal

theorem exists_theta {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ (θ : E) (d : F) (B : Module.Basis (Fin 2) F E), θ ≠ 0 ∧ d ≠ 0 ∧ σ θ = -θ ∧ θ * θ = algebraMap F E d ∧
      B 0 = 1 ∧ B 1 = θ := by
  obtain ⟨y, hy⟩ := exists_moved h
  have hE2 : (2 : E) ≠ 0 := two_ne_zero
  have hσθ : σ (y - σ y) = -(y - σ y) := by
    rw [map_sub, sigma_sigma h]
    ring
  have hθ : y - σ y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  generalize y - σ y = θ at hσθ hθ
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Algebra.smul_def, mul_one] at hst
    have h1 := congrArg σ hst
    simp only [map_add, map_mul, AlgHom.commutes, hσθ, map_zero] at h1
    have hs : (2 : E) * algebraMap F E s = 0 := by
      linear_combination hst + h1
    have ht : (2 : E) * (algebraMap F E t * θ) = 0 := by
      linear_combination hst - h1
    have hs0 : s = 0 := by
      have := (mul_eq_zero.1 hs).resolve_left hE2
      exact (map_eq_zero _).1 this
    have ht0 : t = 0 := by
      have := ((mul_eq_zero.1 ((mul_eq_zero.1 ht).resolve_left hE2))).resolve_right hθ
      exact (map_eq_zero _).1 this
    exact ⟨hs0, ht0⟩
  let B : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [h.2.2.1, Fintype.card_fin])
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = θ := by simp [B]
  have hsum := B.sum_repr (θ * θ)
  rw [Fin.sum_univ_two, hB0, hB1] at hsum
  generalize B.repr (θ * θ) 0 = a at hsum
  generalize B.repr (θ * θ) 1 = b at hsum
  have hsum' : algebraMap F E a + algebraMap F E b * θ = θ * θ := by
    simpa only [Algebra.smul_def, mul_one] using hsum
  have hconj := congrArg σ hsum'
  simp only [map_add, map_mul, AlgHom.commutes, hσθ] at hconj
  have hb : (2 : E) * (algebraMap F E b * θ) = 0 := by
    linear_combination hsum' - hconj
  have hb0 : algebraMap F E b = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 hb).resolve_left hE2)).resolve_right hθ
  have hsq : θ * θ = algebraMap F E a := by
    rw [← hsum', hb0, zero_mul, add_zero]
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hsq
    exact hθ (mul_self_eq_zero.1 hsq)
  exact ⟨θ, a, B, hθ, ha, hσθ, hsq, hB0, hB1⟩

end CM

theorem field_or_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K],
    IsField (K ⊗[F] E) ∨ ∃ e : K ⊗[F] E, e * e = e ∧ e + sigR K σ e = 1 ∧ e * sigR K σ e = 0 := by
  intro F E _ _ _ _ _ σ h K _ _
  obtain ⟨θ, d, B, hθ, hd, hσθ, hsq, hB0, hB1⟩ := exists_theta h
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let C : Module.Basis (Fin 2) K (K ⊗[F] E) := Algebra.TensorProduct.basis K B
  have hC0 : C 0 = 1 := by
    simp only [C, Algebra.TensorProduct.basis_apply, hB0]
    rfl
  have hC1 : C 1 = (1 : K) ⊗ₜ[F] θ := by
    simp only [C, Algebra.TensorProduct.basis_apply, hB1]
  refine core (K := K) (sigR K σ) ((1 : K) ⊗ₜ[F] θ) (algebraMap F K d) ?_ ?_ two_ne_zero ?_ ?_ ?_ ?_
  · rw [Algebra.TensorProduct.tmul_mul_tmul, hsq, mul_one, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one (A := K),
      TensorProduct.smul_tmul']
    simp [Algebra.algebraMap_eq_smul_one]
  · exact fun h0 => hd ((map_eq_zero _).1 h0)
  · intro x
    change Algebra.TensorProduct.map (AlgHom.id F K) σ (algebraMap K (K ⊗[F] E) x) = _
    simp [Algebra.TensorProduct.algebraMap_apply]
  · change Algebra.TensorProduct.map (AlgHom.id F K) σ ((1 : K) ⊗ₜ[F] θ) = _
    rw [Algebra.TensorProduct.map_tmul, hσθ, TensorProduct.tmul_neg]
    rfl
  · intro z
    have hz := C.sum_repr z
    rw [Fin.sum_univ_two, hC0, hC1, Algebra.smul_def, Algebra.smul_def, mul_one] at hz
    exact ⟨_, _, hz.symm⟩
  · intro x y hxy
    have hl := Fintype.linearIndependent_iff.1 C.linearIndependent ![x, y] (by
      rw [Fin.sum_univ_two, hC0, hC1]
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one] using hxy)
    exact ⟨hl 0, hl 1⟩

end GlobalTheory.CompanionTheory.SaGen.Dichotomy
