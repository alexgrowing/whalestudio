import Mathlib

open NumberField

noncomputable section

namespace Formalism.BasicNotions.Examples₂

section Core

variable {E : Type*} [Field E] [NumberField E] {N : ℕ}

def detIdeal (L : Submodule (𝓞 E) (Fin N → E)) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {x | ∃ v : Fin N → Fin N → E, (∀ j, v j ∈ L) ∧ x = (Matrix.of v).det}

theorem of_mulVec_eq (γ : Matrix (Fin N) (Fin N) E) (v : Fin N → Fin N → E) :
    Matrix.of (fun j => γ.mulVec (v j)) = Matrix.of v * γ.transpose := by
  ext i k
  change (∑ l, γ k l * v i l) = ∑ l, v i l * γ k l
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

private theorem det_mem_detIdeal_lemma (L : Submodule (𝓞 E) (Fin N → E)) (v : Fin N → Fin N → E)
    (hv : ∀ j, v j ∈ L) : (Matrix.of v).det ∈ detIdeal L := by
  unfold detIdeal
  exact Submodule.subset_span ⟨v, hv, rfl⟩

theorem detIdeal_smul (γ : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E))
    (hγ : ∀ x ∈ L, γ.mulVec x ∈ L) : ∀ n ∈ detIdeal L, γ.det • n ∈ detIdeal L := by
  have hle : detIdeal L ≤ (detIdeal L).comap (LinearMap.mulLeft (𝓞 E) γ.det) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    have h := det_mem_detIdeal_lemma L (fun j => γ.mulVec (v j)) (fun j => hγ _ (hv j))
    rwa [of_mulVec_eq, Matrix.det_mul, Matrix.det_transpose, mul_comm] at h
  intro n hn
  have h := hle hn
  rwa [Submodule.mem_comap, LinearMap.mulLeft_apply, ← smul_eq_mul] at h

theorem detIdeal_ne_bot (L : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤) : detIdeal L ≠ ⊥ := by
  classical
  obtain ⟨b, hbL, hbspan, hbli⟩ : ∃ b ⊆ (L : Set (Fin N → E)),
      Submodule.span E b = Submodule.span E (L : Set (Fin N → E)) ∧
        LinearIndependent E ((↑) : b → Fin N → E) := by
    exact exists_linearIndependent E _
  rw [hsp] at hbspan
  let B : Module.Basis b E (Fin N → E) :=
    Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan]))
  have : Finite b := Module.Finite.finite_basis B
  letI : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = N := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e : b ≃ Fin N := Fintype.equivFinOfCardEq hcard
  let v : Fin N → Fin N → E := fun j => ((e.symm j : b) : Fin N → E)
  have hvL : ∀ j, v j ∈ L := fun j => hbL (e.symm j).2
  have hli : LinearIndependent E (fun j => Matrix.of v j) := hbli.comp e.symm e.symm.injective
  have hdet : (Matrix.of v).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hli)).ne_zero
  rw [Submodule.ne_bot_iff]
  exact ⟨(Matrix.of v).det, det_mem_detIdeal_lemma L v hvL, hdet⟩

theorem detIdeal_fg (L : Submodule (𝓞 E) (Fin N → E)) (hfg : L.FG) : (detIdeal L).FG := by
  classical
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E))
    (S.biUnion fun s => Finset.univ.image s)
  have hL : ∀ x ∈ L, ∀ j, ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = (a : 𝓞 E) • x j := by
    have hle : L ≤ ⨅ j : Fin N, (1 : Submodule (𝓞 E) E).comap
        ((a : 𝓞 E) • (LinearMap.proj j : (Fin N → E) →ₗ[𝓞 E] E)) := by
      rw [← hS, Submodule.span_le]
      intro s hs
      simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.smul_apply,
        LinearMap.proj_apply, Submodule.mem_one]
      intro j
      exact RingHom.mem_rangeS.mp (ha _ (Finset.mem_biUnion.mpr
        ⟨s, hs, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩))
    intro x hx j
    have h := hle hx
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.smul_apply,
      LinearMap.proj_apply, Submodule.mem_one] at h
    exact h j
  have hgen : ∀ v : Fin N → Fin N → E, (∀ j, v j ∈ L) →
      ∃ z : 𝓞 E, algebraMap (𝓞 E) E z = ((a : 𝓞 E) ^ N) • (Matrix.of v).det := by
    intro v hv
    choose y hy using fun i j => hL (v i) (hv i) j
    have h1 : (algebraMap (𝓞 E) E (a : 𝓞 E)) • Matrix.of v
        = (algebraMap (𝓞 E) E).mapMatrix (Matrix.of y) := by
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.of_apply, Matrix.of_apply, hy, Algebra.smul_def]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_smul, Fintype.card_fin, ← RingHom.map_det] at h2
    exact ⟨(Matrix.of y).det, by rw [← h2, Algebra.smul_def, map_pow]⟩
  have hle : detIdeal L ≤ (1 : Submodule (𝓞 E) E).comap
      (((a : 𝓞 E) ^ N) • (LinearMap.id : E →ₗ[𝓞 E] E)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mem_one]
    exact hgen v hv
  have hfrac : IsFractional (nonZeroDivisors (𝓞 E)) (detIdeal L) := by
    refine ⟨(a : 𝓞 E) ^ N, pow_mem a.2 N, fun b hb => ?_⟩
    have h := hle hb
    rw [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, Submodule.mem_one] at h
    exact RingHom.mem_rangeS.mpr h
  exact FractionalIdeal.fg_of_isNoetherianRing le_rfl ⟨detIdeal L, hfrac⟩

theorem isIntegral_det_of_stab (γ : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤)
    (hγ : ∀ x ∈ L, γ.mulVec x ∈ L) : IsIntegral ℤ γ.det := by
  have h : IsIntegral (𝓞 E) γ.det :=
    isIntegral_of_smul_mem_submodule (detIdeal L) (detIdeal_ne_bot L hsp) (detIdeal_fg L hfg)
      γ.det (detIdeal_smul γ L hγ)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y

theorem det_root_of_unity_of_stab [StarRing E]
    (hstar : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (γ : Matrix (Fin N) (Fin N) E) (hu : γ.det ∈ unitary E) (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤)
    (hγ : ∀ x ∈ L, γ.mulVec x ∈ L) : ∃ n : ℕ, 0 < n ∧ γ.det ^ n = 1 := by
  have hint_r := isIntegral_det_of_stab γ L hfg hsp hγ
  have hnorm : ∀ φ : E →+* ℂ, ‖φ γ.det‖ = 1 := by
    intro φ
    have h1 : star γ.det * γ.det = 1 := hu.1
    have h2 : starRingEnd ℂ (φ γ.det) * φ γ.det = 1 := by
      rw [← hstar, ← map_mul, h1, map_one]
    have h4 : Complex.normSq (φ γ.det) = 1 := by
      have h := Complex.normSq_eq_conj_mul_self (z := φ γ.det)
      rw [h2] at h
      exact_mod_cast h
    have h5 : ‖φ γ.det‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact h4
    nlinarith [norm_nonneg (φ γ.det)]
  obtain ⟨n, hn, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one (K := E) (A := ℂ) hint_r hnorm
  exact ⟨n, hn, h⟩

end Core

end Formalism.BasicNotions.Examples₂
