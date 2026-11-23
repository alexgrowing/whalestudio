import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ZarhinBundleKernelSecondCoordEquations
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem root_mul_complexConj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E]
    (x : E) (n : ℕ) (hn : 0 < n) (hx : x ^ n = 1) : x * IsCMField.complexConj E x = 1 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  have h1 : ‖φ x‖ = 1 := by
    have h : ‖φ x‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hx, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h
  rw [map_mul, IsCMField.complexEmbedding_complexConj, map_one, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, h1]
  simp

theorem root_eq_one_of_halfLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → ∀ (I : Ideal (𝓞 E)) (M : ℕ), 3 ≤ M → I * I.map (bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(M : 𝓞 E)} → I ⊔ I.map (bar : 𝓞 E →+* 𝓞 E) = ⊤ → ∀ (u : 𝓞 E) (n : ℕ), 0 < n → u ^ n = 1 → u - 1 ∈ I → u = 1 := by
  intro E _ _ _ bar hbar I M hM hI hco u n hn hu h1
  have hub : u * bar u = 1 := by
    apply RingOfIntegers.ext
    have hx : (u : E) ^ n = 1 := by
      have := congrArg (fun a : 𝓞 E => (a : E)) hu
      simpa using this
    have := root_mul_complexConj_eq_one (u : E) n hn hx
    rw [← hbar] at this
    simpa using this
  have h2 : bar u - 1 ∈ I.map (bar : 𝓞 E →+* 𝓞 E) := by
    have := Ideal.mem_map_of_mem (bar : 𝓞 E →+* 𝓞 E) h1
    simpa using this
  have h3 : u - 1 ∈ I.map (bar : 𝓞 E →+* 𝓞 E) := by
    have e : u - 1 = (-u) * (bar u - 1) := by linear_combination hub
    rw [e]
    exact Ideal.mul_mem_left _ _ h2
  have h4 : u - 1 ∈ Ideal.span {(M : 𝓞 E)} := by
    rw [← hI, Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 hco)]
    exact ⟨h1, h3⟩
  exact GlobalTheory.CompanionTheory.Ar.Flat.root_of_unity_eq_one_of_dvd_sub_one E u n M hn hu hM (Ideal.mem_span_singleton.1 h4)

end GlobalTheory.CompanionTheory.Ar.Flat
