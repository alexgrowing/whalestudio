import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfullyFlatAdicCompletionSpan
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem algHom_quot_eq_of_etaleLow : ∀ (A R C : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing C] [Algebra R C] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    GlobalTheory.GoodEtale.EtaleLow A R C →
    ∀ (n : ℕ) (f f' : C →ₐ[R] R ⧸ Ideal.span {t} ^ n),
      (∀ c : C, f c - f' c ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t}) → f = f' := by
  intro A R C _ _ _ _ _ _ ρ hρ t hker ht hE n f f' hff
  set P₀ : Ideal R := RingHom.ker ρ with hP₀
  haveI hP : P₀.IsPrime := RingHom.ker_isPrime ρ
  have hρa : ∀ a : A, ρ (algebraMap A R a) = a := fun a => by
    have := congrArg (fun g => g a) hρ
    simpa using this
  have hcomap : P₀.comap (algebraMap A R) = ⊥ := by
    ext a
    simp only [Ideal.mem_comap, hP₀, RingHom.mem_ker, Ideal.mem_bot, hρa]
  have hht : (P₀.comap (algebraMap A R)).height ≤ 1 := by
    rw [hcomap, Ideal.height_bot]; exact zero_le_one
  set Rp := Localization.AtPrime P₀
  haveI : Algebra.Etale Rp (Rp ⊗[R] C) := hE P₀ hht
  haveI : Algebra.FormallyUnramified R Rp := Algebra.FormallyUnramified.of_isLocalization P₀.primeCompl
  haveI : Algebra.FormallyUnramified R (Rp ⊗[R] C) := Algebra.FormallyUnramified.comp R Rp (Rp ⊗[R] C)
  set Q := R ⧸ Ideal.span {t} ^ n
  set B := Localization (Algebra.algebraMapSubmonoid Q P₀.primeCompl)
  letI : Algebra Rp B := localizationAlgebra P₀.primeCompl Q

  have hle : Algebra.algebraMapSubmonoid Q P₀.primeCompl ≤ nonZeroDivisors Q := by
    rintro _ ⟨s, hs, rfl⟩
    suffices H : ∀ x : Q, x * algebraMap R Q s = 0 → x = 0 from
      mem_nonZeroDivisors_iff.2 ⟨fun x hx => H x (by rw [mul_comm]; exact hx), H⟩
    intro x hx
    set a := ρ s
    have ha : a ≠ 0 := fun h => hs (RingHom.mem_ker.2 h)
    have hd : s - algebraMap A R a ∈ Ideal.span {t} := by
      rw [← hker, RingHom.mem_ker, map_sub, hρa, sub_self]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hd
    set u : Q := Ideal.Quotient.mk _ s
    set e : Q := Ideal.Quotient.mk _ (s - algebraMap A R a)
    have he : e ^ n = 0 := by
      simp only [e, ← map_pow, ← hr, mul_pow]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self t) n)
    have hdv : u ∣ (u - e) ^ n := by
      have h1 := sub_dvd_pow_sub_pow (u - e) (-e) n
      rw [neg_pow, he, mul_zero, sub_zero, sub_neg_eq_add, sub_add_cancel] at h1
      exact h1
    obtain ⟨k, hk⟩ := hdv
    have hue : u - e = Ideal.Quotient.mk _ (algebraMap A R a) := by
      simp only [u, e, map_sub, sub_sub_cancel]
    have hzero : algebraMap A R (a ^ n) • x = 0 := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_pow, map_pow, ← hue, hk]
      calc u * k * x = k * (x * u) := by ring
        _ = 0 := by rw [show x * u = 0 from hx, mul_zero]
    exact torsionFree_quot A R ρ hρ t hker ht n (a ^ n) (pow_ne_zero n ha) x hzero
  have hinj : Function.Injective (algebraMap Q B) := IsLocalization.injective B hle
  let φ : Rp →ₐ[R] B := (Algebra.ofId Rp B).restrictScalars R
  let ι : Q →ₐ[R] B := IsScalarTower.toAlgHom R Q B
  let g₁ : Rp ⊗[R] C →ₐ[R] B := Algebra.TensorProduct.productMap φ (ι.comp f)
  let g₂ : Rp ⊗[R] C →ₐ[R] B := Algebra.TensorProduct.productMap φ (ι.comp f')
  set J : Ideal B := Ideal.span {algebraMap R B t}
  have hJ : IsNilpotent J := by
    refine ⟨n, ?_⟩
    rw [Ideal.span_singleton_pow (algebraMap R B t) n, ← map_pow, IsScalarTower.algebraMap_apply R Q B,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self t) n), map_zero, Ideal.zero_eq_bot,
      Ideal.span_singleton_eq_bot]
  have e : (Ideal.Quotient.mkₐ R J).comp g₁ = (Ideal.Quotient.mkₐ R J).comp g₂ := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext; intro x; simp [g₁, g₂]
    · ext c
      simp only [g₁, g₂, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.productMap_apply_tmul,
        map_one, one_mul, Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq, ← map_sub]
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 (hff c)
      rw [← hq, map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      rw [show ι (Ideal.Quotient.mk _ t) = algebraMap R B t from
        (IsScalarTower.algebraMap_apply R Q B t).symm]
      exact Ideal.mem_span_singleton_self _
  have hg : g₁ = g₂ := Algebra.FormallyUnramified.ext J hJ fun x => by
    simpa using congrArg (fun g => g x) e
  ext c
  apply hinj
  have := congrArg (fun g => g ((1 : Rp) ⊗ₜ[R] c)) hg
  simpa [g₁, g₂, ι] using this

end GlobalTheory.GoodEtaleSection
