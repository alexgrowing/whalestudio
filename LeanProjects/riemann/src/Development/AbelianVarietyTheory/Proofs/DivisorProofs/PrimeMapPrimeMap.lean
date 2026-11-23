import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CountSpanSingletonRingEquiv
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.FixNormCls

variable {E : Type} [Field E] [NumberField E]

def ord (P : HeightOneSpectrum (𝓞 E)) (x : E) : ℤ :=
  FractionalIdeal.count E P (FractionalIdeal.spanSingleton (𝓞 E)⁰ x)

def primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) where
  asIdeal := P.asIdeal.comap (RingOfIntegers.mapRingEquiv τ.symm : 𝓞 E →+* 𝓞 E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply P.ne_bot
    rw [eq_bot_iff] at h ⊢
    intro x hx
    have : (RingOfIntegers.mapRingEquiv τ) x ∈
        P.asIdeal.comap (RingOfIntegers.mapRingEquiv τ.symm : 𝓞 E →+* 𝓞 E) := by
      rw [Ideal.mem_comap]
      convert hx using 1
      exact (RingOfIntegers.mapRingEquiv τ).symm_apply_apply x
    have h2 := h this
    rw [Submodule.mem_bot, map_eq_zero_iff _ (RingOfIntegers.mapRingEquiv τ).injective] at h2
    rw [Submodule.mem_bot]; exact h2

theorem mem_primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) :
    a ∈ (primeMap τ P).asIdeal ↔ RingOfIntegers.mapRingEquiv τ.symm a ∈ P.asIdeal :=
  Ideal.mem_comap

theorem ord_zero (P : HeightOneSpectrum (𝓞 E)) : ord P (0 : E) = 0 := by
  simp [ord, FractionalIdeal.count_zero]

theorem ord_mul (P : HeightOneSpectrum (𝓞 E)) {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord P (x * y) = ord P x + ord P y := by
  unfold ord
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  exact FractionalIdeal.count_mul E P (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)

theorem ord_inv (P : HeightOneSpectrum (𝓞 E)) (x : E) : ord P x⁻¹ = - ord P x := by
  unfold ord
  rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv]

theorem ord_div (P : HeightOneSpectrum (𝓞 E)) {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord P (x / y) = ord P x - ord P y := by
  rw [div_eq_mul_inv, ord_mul P hx (inv_ne_zero hy), ord_inv, sub_eq_add_neg]

theorem ord_one (P : HeightOneSpectrum (𝓞 E)) : ord P (1 : E) = 0 := by
  simp [ord, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

theorem ord_primeMap (τ : E ≃+* E) (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    ord (primeMap τ P) (τ x) = ord P x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ord_zero]
  exact GlobalTheory.OrdTransport.count_spanSingleton_ringEquiv (𝓞 E) E (RingOfIntegers.mapRingEquiv τ) τ
    (fun a => rfl) P (primeMap τ P)
    (fun a => by
      rw [mem_primeMap]
      have : RingOfIntegers.mapRingEquiv τ.symm (RingOfIntegers.mapRingEquiv τ a) = a :=
        RingOfIntegers.ext (by change τ.symm (τ (a : E)) = (a : E); exact τ.symm_apply_apply _)
      rw [this]) x hx

theorem primeMap_primeMap (τ : E ≃+* E) (hτ : ∀ x, τ (τ x) = x) (P : HeightOneSpectrum (𝓞 E)) :
    primeMap τ (primeMap τ P) = P := by
  ext a
  rw [mem_primeMap, mem_primeMap]
  have : RingOfIntegers.mapRingEquiv τ.symm (RingOfIntegers.mapRingEquiv τ.symm a) = a := by
    apply RingOfIntegers.ext
    change τ.symm (τ.symm (a : E)) = (a : E)
    rw [RingEquiv.symm_apply_eq, RingEquiv.symm_apply_eq, hτ]
  rw [this]

end GlobalTheory.FixNormCls
