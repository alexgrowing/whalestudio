import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.LocalRingCardinality.DataSpaces

open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.LocSpan

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_disc_notMem (hc : Formalism.BasicNotions.CMData F E) (p : HeightOneSpectrum (𝓞 F)) :
    ∃ (θ t : 𝓞 E) (d : 𝓞 F), (t : E) = star (θ : E) ∧ d ∉ p.asIdeal ∧
      algebraMap F E (d : F) = ((θ : E) - (t : E)) ^ 2 := by
  haveI := p.isMaximal
  obtain ⟨P, hP, hPp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) p.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
      exact bot_le)
  obtain ⟨θ, t, ht, hθ⟩ := hc.cmUnram.2.2 P hP
  have ht' : (t : E) = star (θ : E) := ht
  obtain ⟨d0, hd0⟩ := (hc.fixed (((θ : E) - (t : E)) ^ 2)).1 (by
    rw [ht', star_pow, star_sub, star_star]; ring)
  have hint : IsIntegral ℤ d0 := by
    have h1 : IsIntegral ℤ (algebraMap F E d0) := by
      rw [hd0]
      exact (θ.isIntegral_coe.sub t.isIntegral_coe).pow 2
    exact (isIntegral_algHom_iff ((algebraMap F E).toIntAlgHom) (algebraMap F E).injective).1 h1
  refine ⟨θ, t, ⟨d0, hint⟩, ht', ?_, hd0⟩
  intro hd
  rw [← hPp] at hd
  replace hd := Ideal.mem_comap.1 hd
  have : algebraMap (𝓞 F) (𝓞 E) ⟨d0, hint⟩ = (θ - t) ^ 2 := by
    apply RingOfIntegers.ext
    simp only [map_pow, map_sub]
    exact hd0
  rw [this] at hd
  exact hθ (hP.isPrime.mem_of_pow_mem 2 hd)

theorem exists_coord (hc : Formalism.BasicNotions.CMData F E) (θ : E) (hθ : θ - star θ ≠ 0) (x : E) :
    ∃ a b : F, x = algebraMap F E a + algebraMap F E b * θ := by
  have hθ' : star θ - θ ≠ 0 := fun h => hθ (by rw [← neg_sub, h, neg_zero])
  obtain ⟨b, hb⟩ := (hc.fixed ((x - star x) / (θ - star θ))).1 (by
    rw [star_div₀, star_sub, star_sub, star_star, star_star]; field_simp; ring)
  obtain ⟨a, ha⟩ := (hc.fixed (x - (x - star x) / (θ - star θ) * θ)).1 (by
    rw [star_sub, star_mul, star_div₀, star_sub, star_sub, star_star, star_star]; field_simp; ring)
  exact ⟨a, b, by rw [ha, hb]; ring⟩

omit [StarRing E] in
theorem isIntegral_ιE {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)
    (x : 𝓞 E) : IsIntegral 𝒪[A.Fp] (A.ιE (x : E)) :=
  (x.isIntegral_coe.map A.ιE.toIntAlgHom).tower_top

omit [StarRing E] in
theorem mem_integer_of_isIntegral {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (A : LocAt F E sig p) (a : A.Fp) (h : IsIntegral 𝒪[A.Fp] (algebraMap A.Fp A.Ep a)) :
    a ∈ 𝒪[A.Fp] := by
  haveI : Nontrivial A.Ep := Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)
  have h1 : IsIntegral 𝒪[A.Fp] a :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[A.Fp] A.Fp A.Ep)
      (algebraMap A.Fp A.Ep).injective).1 h
  exact (Valuation.integer.integers (valuation A.Fp)).mem_of_integral h1

omit [StarRing E] in
theorem valuation_ιF_eq_one {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (A : LocAt F E sig p) (d : 𝓞 F) (hd : d ∉ p.asIdeal) :
    valuation A.Fp (A.ιF (d : F)) = 1 := by
  have h : p.valuation F (d : F) = 1 := (p.valuation_eq_one_iff_notMem (K := F)).2 hd
  have h1 := (A.val (d : F) 1).2 (by rw [h, map_one])
  have h2 := (A.val 1 (d : F)).2 (by rw [h, map_one])
  rw [Valuation.Compatible.vle_iff_le (v := valuation A.Fp)] at h1 h2
  simp only [map_one] at h1 h2
  exact le_antisymm h1 h2

theorem mem_O_iff : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p), ∀ y : A.Ep, y ∈ A.O ↔ ∃ (n : ℕ) (c : Fin n → 𝒪[A.Fp]) (x : Fin n → 𝓞 E), y = ∑ i, algebraMap A.Fp A.Ep (c i : A.Fp) * A.ιE (x i : E) := by
  intro F E _ _ _ _ _ _ hc sig hsig p A y
  constructor
  · intro hy
    rw [A.O_def] at hy
    obtain ⟨θ, t, d, ht, hd, hdisc⟩ := exists_disc_notMem hc p
    have hv := valuation_ιF_eq_one A d hd
    have hne : (θ : E) - star (θ : E) ≠ 0 := by
      intro h
      rw [ht, h] at hdisc
      have : d = 0 := by
        apply RingOfIntegers.ext
        simpa using hdisc
      exact hd (this ▸ p.asIdeal.zero_mem)
    have hco : ∀ z : A.Ep, ∃ a b : A.Fp,
        z = algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (θ : E) := by
      intro z
      have hz : z ∈ Submodule.span A.Fp (Set.range A.ιE) := by rw [A.span]; trivial
      induction hz using Submodule.span_induction with
      | mem _ hx =>
        obtain ⟨x, rfl⟩ := hx
        obtain ⟨a, b, rfl⟩ := exists_coord hc θ hne x
        exact ⟨A.ιF a, A.ιF b, by rw [map_add, map_mul, A.compat, A.compat]⟩
      | zero => exact ⟨0, 0, by simp⟩
      | add _ _ _ _ h1 h2 =>
        obtain ⟨a, b, rfl⟩ := h1
        obtain ⟨a', b', rfl⟩ := h2
        exact ⟨a + a', b + b', by rw [map_add, map_add]; ring⟩
      | smul c _ _ h1 =>
        obtain ⟨a, b, rfl⟩ := h1
        exact ⟨c * a, c * b, by rw [map_mul, map_mul, Algebra.smul_def]; ring⟩
    obtain ⟨a, b, rfl⟩ := hco y
    have hcj := hy.map (A.cj.toAlgHom.restrictScalars 𝒪[A.Fp])
    have hcj' : IsIntegral 𝒪[A.Fp]
        (algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (t : E)) := by
      have e : A.cj (algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (θ : E)) =
          algebraMap A.Fp A.Ep a + algebraMap A.Fp A.Ep b * A.ιE (t : E) := by
        rw [map_add, map_mul, A.cj.commutes, A.cj.commutes, A.cj_ιE, hsig, ht]
      rw [← e]; exact hcj
    have hbd : b * A.ιF (d : F) ∈ 𝒪[A.Fp] := by
      apply mem_integer_of_isIntegral A
      have := (hy.sub hcj').mul ((isIntegral_ιE A θ).sub (isIntegral_ιE A t))
      convert this using 1
      rw [map_mul, ← A.compat, hdisc, map_pow, map_sub]; ring
    have hb : b ∈ 𝒪[A.Fp] := by
      rw [Valuation.mem_integer_iff] at hbd ⊢
      rwa [map_mul, hv, mul_one] at hbd
    have hbI : IsIntegral 𝒪[A.Fp] (algebraMap A.Fp A.Ep b) :=
      isIntegral_algebraMap (R := 𝒪[A.Fp]) (x := ⟨b, hb⟩)
    have ha : a ∈ 𝒪[A.Fp] := by
      apply mem_integer_of_isIntegral A
      have := hy.sub (hbI.mul (isIntegral_ιE A θ))
      simpa using this
    exact ⟨2, ![⟨a, ha⟩, ⟨b, hb⟩], ![1, θ], by simp [Fin.sum_univ_two]⟩
  · rintro ⟨n, c, x, rfl⟩
    rw [A.O_def]
    refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ (isIntegral_ιE A _)
    exact isIntegral_algebraMap (R := 𝒪[A.Fp]) (x := c i)

end GlobalTheory.LocSpan
