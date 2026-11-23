import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CMSpan

open ComplexConjugate

theorem functional_single {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℝ] ℝ) (j : Fin n) (z : ℂ) :
    ((f (Pi.single j z) : ℝ) : ℂ) =
      (((f (Pi.single j 1) : ℂ) - Complex.I * (f (Pi.single j Complex.I) : ℂ)) / 2) * z +
      conj (((f (Pi.single j 1) : ℂ) - Complex.I * (f (Pi.single j Complex.I) : ℂ)) / 2) * conj z := by
  have hz : (Pi.single j z : Fin n → ℂ) =
      z.re • (Pi.single j (1:ℂ) : Fin n → ℂ) + z.im • (Pi.single j Complex.I : Fin n → ℂ) := by
    ext k
    by_cases h : k = j
    · subst h; simp [Complex.ext_iff]
    · simp [h]
  rw [hz, map_add, map_smul, map_smul]
  simp only [map_div₀, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  apply Complex.ext <;> simp <;> ring

theorem conjugate_ne_self {E : Type} [Field E] [IsTotallyComplex E] (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ ≠ σ := fun h =>
  IsTotallyComplex.complexEmbedding_not_isReal σ (ComplexEmbedding.isReal_iff.2 h)

end GlobalTheory.CMSpan

namespace GlobalTheory.CMSpan

open ComplexConjugate

theorem cmType_embeddings_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type}
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) :
    Function.Injective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
  have hTC : IsTotallyComplex E := IsCMField.to_isTotallyComplex
  rintro (i | i) (j | j) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl ((hφ (φ i)).unique (Or.inl rfl) (Or.inl h))
  · have hij : i = j := (hφ (φ i)).unique (Or.inl rfl) (Or.inr h)
    subst hij
    exact absurd h.symm (conjugate_ne_self (φ i))
  · have hij : j = i := (hφ (φ j)).unique (Or.inl rfl) (Or.inr h.symm)
    subst hij
    exact absurd h (conjugate_ne_self (φ j))
  · have h' : φ i = φ j := by
      refine RingHom.ext fun x => ?_
      have := congrArg (fun σ : E →+* ℂ => conj (σ x)) h
      simpa [ComplexEmbedding.conjugate_coe_eq] using this
    exact congrArg Sum.inr ((hφ (φ i)).unique (Or.inl rfl) (Or.inl h'))

theorem span_real_eq_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E),
      (∃ N : ℕ, 0 < N ∧ ∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) →
    ∀ (Λ : Submodule ℤ (Fin n → ℂ)), (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) →
      Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ := by
  intro E _ _ _ I _ φ hφ n e L hL Λ hΛ
  classical
  obtain ⟨N, hN, hNL⟩ := hL
  by_contra hne
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)

  have hkill : ∀ x : E, f (fun j ↦ φ (e j) x) = 0 := by
    intro x
    obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
    let z : 𝓞 E := ⟨y • x, hyint x (Finset.mem_singleton_self x)⟩
    have hmem : (fun j ↦ φ (e j) ((N : E) * algebraMap (𝓞 E) E z)) ∈ Λ :=
      (hΛ _).2 ⟨_, hNL z, rfl⟩
    have h0 := hfk (Submodule.subset_span hmem)
    rw [LinearMap.mem_ker] at h0
    have hsm : (fun j ↦ φ (e j) ((N : E) * algebraMap (𝓞 E) E z)) =
        ((N : ℝ) * (y : ℝ)) • (fun j ↦ φ (e j) x) := by
      ext j
      simp [z, zsmul_eq_mul, Complex.real_smul, mul_assoc]
    rw [hsm, map_smul, smul_eq_mul] at h0
    have hNy : (N : ℝ) * (y : ℝ) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hN.ne') (by exact_mod_cast hy0)
    exact (mul_eq_zero.1 h0).resolve_left hNy

  set c : Fin n → ℂ := fun j =>
    ((f (Pi.single j 1) : ℂ) - Complex.I * (f (Pi.single j Complex.I) : ℂ)) / 2 with hc
  have hexp : ∀ w : Fin n → ℂ, ((f w : ℝ) : ℂ) = ∑ j, (c j * w j + conj (c j) * conj (w j)) := by
    intro w
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => functional_single f j (w j)

  let ψ : I ⊕ I → (E →* ℂ) := fun a => ((Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i)) a : E →+* ℂ) : E →* ℂ)
  have hψ : Function.Injective ψ := by
    intro a b h
    apply cmType_embeddings_injective φ hφ
    exact RingHom.ext fun x => DFunLike.congr_fun h x
  have hli := (linearIndependent_monoidHom E ℂ).comp ψ hψ
  let g : I ⊕ I → ℂ := Sum.elim (fun i => c (e.symm i)) (fun i => conj (c (e.symm i)))
  have hg : ∑ a, g a • (fun x => ψ a x) = 0 := by
    funext x
    have hx := hexp (fun j ↦ φ (e j) x)
    rw [hkill x, Complex.ofReal_zero] at hx
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fintype.sum_sum_type,
      g, ψ, Sum.elim_inl, Sum.elim_inr, MonoidHom.coe_coe, ComplexEmbedding.conjugate_coe_eq]
    rw [← Finset.sum_add_distrib, ← e.sum_comp]
    simpa using hx.symm
  have hc0 : ∀ j, c j = 0 := by
    intro j
    have := Fintype.linearIndependent_iff.1 hli g hg (Sum.inl (e j))
    simpa [g] using this
  apply hf0
  refine LinearMap.ext fun w => ?_
  have hw := hexp w
  simp only [hc0, zero_mul, map_zero, add_zero, Finset.sum_const_zero] at hw
  simpa using hw

end GlobalTheory.CMSpan
