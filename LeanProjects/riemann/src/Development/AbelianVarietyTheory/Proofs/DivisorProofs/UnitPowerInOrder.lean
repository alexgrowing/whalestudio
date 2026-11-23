import Mathlib
open NumberField

namespace GlobalTheory

theorem order_conductor_exists (K F : Type) [CommRing K] [IsDomain K] [Module.Finite ℤ K]
    [Field F] [NumberField F] [Algebra K F] [IsFractionRing K F] :
    ∃ d : K, d ≠ 0 ∧ ∀ x : 𝓞 F, ∃ y : K, algebraMap K F y = algebraMap K F d * (x : F) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := 𝓞 F)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors K)
    (s.image (fun x : 𝓞 F => (x : F)))
  refine ⟨(b : K), nonZeroDivisors.ne_zero b.2, fun x => ?_⟩
  have hx : x ∈ Submodule.span ℤ (s : Set (𝓞 F)) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy⟩ := hb (z : F) (Finset.mem_image_of_mem _ hz)
    exact ⟨y, by rw [hy, Algebra.smul_def]⟩
  | zero => exact ⟨0, by simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨y1, h1⟩ := hz
    obtain ⟨y2, h2⟩ := hw
    exact ⟨y1 + y2, by rw [map_add, h1, h2]; push_cast; ring⟩
  | smul n z _ hz =>
    obtain ⟨y, h⟩ := hz
    exact ⟨n • y, by rw [zsmul_eq_mul, map_mul, map_intCast, h]; push_cast; ring⟩

theorem order_unit_pow_mem (K F : Type) [CommRing K] [IsDomain K] [Module.Finite ℤ K] [Field F]
    [NumberField F] [Algebra K F] [IsFractionRing K F] (u : (𝓞 F)ˣ) :
    ∃ e : ℕ, 0 < e ∧ ∃ a : Kˣ, algebraMap K F (a : K) = ((u : 𝓞 F) : F) ^ e := by
  obtain ⟨d, hd0, hd⟩ := order_conductor_exists K F
  have hint : IsIntegral ℤ (algebraMap K F d) :=
    (Algebra.IsIntegral.isIntegral (R := ℤ) d).algebraMap
  let D : 𝓞 F := ⟨algebraMap K F d, hint⟩
  have hDF : (D : F) = algebraMap K F d := rfl
  have hD0 : D ≠ 0 := by
    intro h
    apply hd0
    apply IsFractionRing.injective K F
    rw [← hDF, h]; simp
  let I : Ideal (𝓞 F) := Ideal.span {D}
  have hI : I ≠ ⊥ := by simpa [I, Ideal.span_singleton_eq_bot] using hD0
  haveI : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let f : 𝓞 F →* 𝓞 F ⧸ I := (Ideal.Quotient.mk I).toMonoidHom
  let e := orderOf (Units.map f u)
  have he : 0 < e := orderOf_pos _
  have key : ∀ w : (𝓞 F)ˣ, Units.map f w ^ e = 1 →
      ∃ y : K, algebraMap K F y = ((w : 𝓞 F) : F) ^ e := by
    intro w hw
    have h1 : Ideal.Quotient.mk I ((w : 𝓞 F) ^ e) = 1 := by
      have := congrArg (fun z : (𝓞 F ⧸ I)ˣ => (z : 𝓞 F ⧸ I)) hw
      simpa [f] using this
    have h2 : (w : 𝓞 F) ^ e - 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, map_one, sub_self]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h2
    obtain ⟨y, hy⟩ := hd c
    refine ⟨1 + y, ?_⟩
    have hcF : (c : F) * (D : F) = ((w : 𝓞 F) : F) ^ e - 1 := by
      have := congrArg (fun z : 𝓞 F => (z : F)) hc
      simpa using this
    rw [map_add, map_one, hy, ← hDF, mul_comm, hcF]; ring
  obtain ⟨y1, hy1⟩ := key u (pow_orderOf_eq_one _)
  obtain ⟨y2, hy2⟩ := key u⁻¹ (by rw [map_inv, inv_pow, pow_orderOf_eq_one, inv_one])
  have h12 : y1 * y2 = 1 := by
    apply IsFractionRing.injective K F
    rw [map_mul, hy1, hy2, map_one, ← mul_pow]
    have : ((u : 𝓞 F) : F) * (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
      have := congrArg (fun z : 𝓞 F => (z : F)) (Units.mul_inv u)
      simpa using this
    rw [this, one_pow]
  exact ⟨e, he, ⟨y1, y2, h12, by rw [mul_comm, h12]⟩, hy1⟩

end GlobalTheory
