import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XJacPowNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.XMulConjIMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.DegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsBis
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.RedRoot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsTer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.xEx :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b : ℕ) (𝔞 : Ideal (𝓞 K)), b < M → 𝔞 ≠ ⊥ → ∃ X : K, IsX M K b 𝔞 X := by
  intro M _ K _ _ _ b 𝔞 hb h𝔞
  have h𝔞0 : 𝔞 ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero h𝔞
  set S : Set (HeightOneSpectrum (𝓞 K)) := {v | v.asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 K)}}
  have hM0 : Ideal.span {((M : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast NeZero.ne M
  have hS : S.Finite := Ideal.finite_factors hM0
  obtain ⟨v, hvS, hprime, hvc⟩ := degOne K S hS (ClassGroup.mk0 ⟨𝔞, h𝔞0⟩)⁻¹
  haveI : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hprime⟩
  obtain ⟨π, hπ⟩ := (red K (Ideal.absNorm v.asIdeal) v.asIdeal).1 rfl
  have hpv := ((red K (Ideal.absNorm v.asIdeal) v.asIdeal).2 π hπ).2.2.2
  have hcop : (Ideal.absNorm v.asIdeal).Coprime M := by
    rw [Nat.Prime.coprime_iff_not_dvd hprime]
    rintro ⟨k, hk⟩
    apply hvS
    show v.asIdeal ∣ _
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hpv
  have hζ := (IsCyclotomicExtension.zeta_spec M ℚ K).toInteger_isPrimitiveRoot
  obtain ⟨hπζ, hdvd⟩ := redRoot (𝓞 K) _ π M _ hcop hζ
  obtain ⟨χ, hχ, -⟩ := teich (𝓞 K) _ π M ((Ideal.absNorm v.asIdeal - 1) / M) _ hζ hπζ (Nat.mul_div_cancel' hdvd)
  have hXv := xJac M K b _ π χ hcop hb hχ
  rw [hπ] at hXv
  have hv0 : v.asIdeal ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero v.ne_bot
  have hprin : (𝔞 * v.asIdeal).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (mul_mem h𝔞0 hv0)]
    have hm : ClassGroup.mk0 ⟨𝔞 * v.asIdeal, mul_mem h𝔞0 hv0⟩ =
        ClassGroup.mk0 ⟨𝔞, h𝔞0⟩ * ClassGroup.mk0 ⟨v.asIdeal, hv0⟩ := by
      rw [← map_mul]
      rfl
    rw [hm]
    change _ * UpperTheory.V.Kum.primeCl v = 1
    rw [hvc, mul_inv_cancel]
  obtain ⟨y, hy⟩ := hprin
  have hy' : Ideal.span {y} = 𝔞 * v.asIdeal := hy.symm
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at hy'
    exact (mul_ne_zero h𝔞 v.ne_bot) hy'.symm
  have hXy := (xMul M K b).2.2.2.2 y hy0
  rw [hy'] at hXy
  exact ⟨_, (xMul M K b).2.1 𝔞 v.asIdeal _ _ h𝔞 v.ne_bot hXy hXv⟩
