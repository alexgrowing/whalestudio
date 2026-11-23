import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta

open NumberField IsDedekindDomain

namespace GlobalTheory.RayDescent

theorem dvd_intNorm_sub_one (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (n : ℕ)
    (a : 𝓞 E) (h : (n : 𝓞 E) ∣ a - 1) : (n : 𝓞 K) ∣ Algebra.intNorm (𝓞 K) (𝓞 E) a - 1 := by
  classical
  obtain ⟨c, hc⟩ := h
  have ha : a = 1 + n * c := by rw [← hc]; ring
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha]
  let F := AlgebraicClosure E
  let r : (E →ₐ[K] F) → (𝓞 E →+* 𝓞 F) := fun σ => RingOfIntegers.mapRingHom (σ : E →+* F)
  have hd : (n : 𝓞 F) ∣ (∏ σ : E →ₐ[K] F, r σ a) - 1 := by
    have : ∀ s : Finset (E →ₐ[K] F), (n : 𝓞 F) ∣ (∏ σ ∈ s, r σ a) - 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert σ s hσ ih =>
        rw [Finset.prod_insert hσ]
        obtain ⟨d, hd⟩ := ih
        refine ⟨r σ a * d + r σ c, ?_⟩
        have h1 : r σ a = 1 + n * r σ c := by rw [ha]; simp
        have h2 : ∏ σ ∈ s, r σ a = 1 + n * d := by rw [← hd]; ring
        rw [h2, h1]; ring
    exact this _
  obtain ⟨d, hd⟩ := hd
  set N := Algebra.intNorm (𝓞 K) (𝓞 E) a with hN
  have hNK : (N : K) = Algebra.norm K (a : E) := Algebra.algebraMap_intNorm (L := E) a
  have hprod : algebraMap K F (N : K) = 1 + n * (d : F) := by
    rw [hNK, Algebra.norm_eq_prod_embeddings K F]
    have := congrArg (algebraMap (𝓞 F) F) hd
    rw [map_sub, map_prod, map_one, map_mul, map_natCast] at this
    rw [← this]
    simp [r]
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  have hnF : (n : F) ≠ 0 := by exact_mod_cast hn.ne'
  have hy : algebraMap K F (((N : K) - 1) / n) = d := by
    rw [map_div₀, map_sub, hprod, map_one, map_natCast]
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hnF]
  have hint : IsIntegral ℤ (((N : K) - 1) / n) := by
    rw [← isIntegral_algebraMap_iff (algebraMap K F).injective, hy]
    exact d.isIntegral_coe
  obtain ⟨y, hy'⟩ : ∃ y : 𝓞 K, (y : K) = ((N : K) - 1) / n := ⟨⟨_, hint⟩, rfl⟩
  refine ⟨y, ?_⟩
  apply RingOfIntegers.ext
  change algebraMap (𝓞 K) K (N - 1) = algebraMap (𝓞 K) K (n * y)
  rw [map_sub, map_mul, map_one, map_natCast]
  change (N : K) - 1 = n * (y : K)
  rw [hy', mul_div_cancel₀ _ hnK]

theorem containsRayField_comp (K E L : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Field L] [NumberField L]
    (φ : K →+* E) (ψ : E →+* L) (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField ψ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (ψ.comp φ) n := by
  intro P hP
  obtain ⟨f, α, h1, h2, h3⟩ := h P hP
  letI : Algebra K E := φ.toAlgebra
  letI : Algebra E L := ψ.toAlgebra
  have hq : P.asIdeal.comap (RingOfIntegers.mapRingHom ψ) = P.asIdeal.under (𝓞 E) := rfl
  have hp : P.asIdeal.comap (RingOfIntegers.mapRingHom (ψ.comp φ)) = (P.asIdeal.under (𝓞 E)).under (𝓞 K) := by
    ext x
    rfl
  rw [hq] at h1 h2
  rw [hp]
  haveI := P.isMaximal
  set q := P.asIdeal.under (𝓞 E)
  set p := q.under (𝓞 K)
  haveI : q.IsMaximal := inferInstance
  haveI : p.IsMaximal := inferInstance
  have hrel : Ideal.relNorm (𝓞 K) q = p ^ q.inertiaDeg (𝓞 K) := Ideal.relNorm_eq_pow_of_isMaximal q p
  refine ⟨q.inertiaDeg (𝓞 K) * f, Algebra.intNorm (𝓞 K) (𝓞 E) α, ?_, ?_, dvd_intNorm_sub_one K E n α h3⟩
  · rw [h1, pow_mul, ← map_pow Ideal.absNorm p, ← hrel, Ideal.absNorm_relNorm]
  · rw [pow_mul, ← hrel, ← map_pow, h2, Ideal.relNorm_singleton]

end GlobalTheory.RayDescent
