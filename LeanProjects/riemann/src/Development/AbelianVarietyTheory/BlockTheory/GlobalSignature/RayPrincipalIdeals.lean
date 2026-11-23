import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

def idealsPrimeTo (𝔪 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier := {J | ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭.asIdeal ∣ 𝔪 →
    FractionalIdeal.count K 𝔭 (J : FractionalIdeal (𝓞 K)⁰ K) = 0}
  one_mem' := fun 𝔭 _ => by simpa using FractionalIdeal.count_one K 𝔭
  mul_mem' := fun {a b} ha hb 𝔭 h => by
    rw [Units.val_mul, FractionalIdeal.count_mul K 𝔭 a.ne_zero b.ne_zero, ha 𝔭 h, hb 𝔭 h, add_zero]
  inv_mem' := fun {a} ha 𝔭 h => by
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv K 𝔭, ha 𝔭 h, neg_zero]

def rayUnits (𝔪 : Ideal (𝓞 K)) : Subgroup Kˣ where
  carrier := {x | ∃ α β : 𝓞 K, GlobalTheory.NT.RayPair 𝔪 α β ∧ (x : K) * (β : K) = (α : K)}
  one_mem' := ⟨1, 1, ⟨one_ne_zero, one_ne_zero, by simp [← Ideal.one_eq_top, isCoprime_one_left],
    by simp [← Ideal.one_eq_top, isCoprime_one_left], by simp, fun φ => by simp⟩, by simp⟩
  mul_mem' := by
    rintro x y ⟨a, b, ⟨ha, hb, ha', hb', hab, hp⟩, hx⟩ ⟨c, d, ⟨hc, hd, hc', hd', hcd, hq⟩, hy⟩
    refine ⟨a * c, b * d, ⟨mul_ne_zero ha hc, mul_ne_zero hb hd, ?_, ?_, ?_, fun φ => ?_⟩, ?_⟩
    · rw [← Ideal.span_singleton_mul_span_singleton]; exact ha'.mul_left hc'
    · rw [← Ideal.span_singleton_mul_span_singleton]; exact hb'.mul_left hd'
    · have : a * c - b * d = c * (a - b) + b * (c - d) := by ring
      rw [this]
      exact 𝔪.add_mem (𝔪.mul_mem_left _ hab) (𝔪.mul_mem_left _ hcd)
    · have := mul_pos (hp φ) (hq φ)
      push_cast
      rw [map_mul, map_mul]
      linarith [this]
    · have e1 : ((b * d : 𝓞 K) : K) = (b : K) * (d : K) := rfl
      have e2 : ((a * c : 𝓞 K) : K) = (a : K) * (c : K) := rfl
      rw [e1, e2, Units.val_mul, ← hx, ← hy]; ring
  inv_mem' := by
    rintro x ⟨a, b, ⟨ha, hb, ha', hb', hab, hp⟩, hx⟩
    refine ⟨b, a, ⟨hb, ha, hb', ha', ?_, fun φ => ?_⟩, ?_⟩
    · simpa using 𝔪.neg_mem hab
    · rw [mul_comm]; exact hp φ
    · rw [← hx, ← mul_assoc, Units.inv_mul, one_mul]

def rayPrincipal (𝔪 : Ideal (𝓞 K)) : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  (rayUnits 𝔪).map (toPrincipalIdeal (𝓞 K) K)

theorem count_span_eq_zero {𝔪 : Ideal (𝓞 K)} {a : 𝓞 K} (ha : a ≠ 0) (h : IsCoprime (Ideal.span {a}) 𝔪)
    (𝔭 : HeightOneSpectrum (𝓞 K)) (hp : 𝔭.asIdeal ∣ 𝔪) :
    FractionalIdeal.count K 𝔭 (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) = 0 := by
  have h0 : Ideal.span {a} ≠ (0 : Ideal (𝓞 K)) := by simpa using ha
  have : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_span_singleton a).symm
  rw [this, FractionalIdeal.count_coe K 𝔭 h0]
  norm_cast
  by_contra hne
  have hd : 𝔭.asIdeal ∣ Ideal.span {a} :=
    (Associates.count_ne_zero_iff_dvd h0 𝔭.irreducible).1 hne
  exact 𝔭.prime.not_unit (h.isUnit_of_dvd' hd hp)

abbrev RayClassGroup (𝔪 : Ideal (𝓞 K)) : Type :=
  idealsPrimeTo 𝔪 ⧸ (rayPrincipal 𝔪).subgroupOf (idealsPrimeTo 𝔪)

def primeElt (𝔪 : Ideal (𝓞 K)) (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ 𝔭.asIdeal ∣ 𝔪) : idealsPrimeTo 𝔪 :=
  ⟨Units.mk0 (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 𝔭.ne_bot),
    fun 𝔮 hq => FractionalIdeal.count_maximal_coprime K 𝔮 (by rintro rfl; exact h hq)⟩

def primeClass (𝔪 : Ideal (𝓞 K)) (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ 𝔭.asIdeal ∣ 𝔪) : RayClassGroup 𝔪 :=
  QuotientGroup.mk (primeElt 𝔪 𝔭 h)

def RayField : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L), IsAbelianGalois K L ∧
      ∃ Art : RayClassGroup 𝔪 ≃* (L ≃ₐ[K] L),
        ∀ (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ 𝔭.asIdeal ∣ 𝔪),
          GlobalTheory.NT.UnramIn L 𝔭 ∧ GlobalTheory.NT.IsFrob L 𝔭 (Art (primeClass 𝔪 𝔭 h))

example : idealsPrimeTo (⊤ : Ideal (𝓞 K)) = ⊤ := by
  refine eq_top_iff.2 fun J _ 𝔭 h => absurd ?_ 𝔭.isPrime.ne_top
  exact top_le_iff.1 (Ideal.le_of_dvd h)

example (𝔪 : Ideal (𝓞 ℚ)) : (-1 : ℚˣ) ∉ rayUnits 𝔪 := by
  rintro ⟨a, b, ⟨-, -, -, -, -, hp⟩, hx⟩
  have := hp (Rat.castHom ℝ)
  rw [← hx] at this
  simp only [Units.val_neg, Units.val_one, map_mul, map_neg, map_one] at this
  nlinarith [mul_self_nonneg ((Rat.castHom ℝ) (b : ℚ))]

end GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals

end
