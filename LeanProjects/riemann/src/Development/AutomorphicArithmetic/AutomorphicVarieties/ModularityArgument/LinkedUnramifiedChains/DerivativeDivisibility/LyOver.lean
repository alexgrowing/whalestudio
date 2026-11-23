import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.CmpPrime

open Polynomial

private theorem ext_injective {R S K : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Field K]
    [IsAlgClosed K] (f : R →+* S) (hi : Function.Injective f) (hf : f.IsIntegral) (φ : R →+* K)
    (hφ : Function.Injective φ) : ∃ ψ : S →+* K, ψ.comp f = φ := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R K := φ.toAlgebra
  haveI : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.2 hi
  haveI : Module.IsTorsionFree R K := Module.isTorsionFree_iff_algebraMap_injective.2 hφ
  haveI : Algebra.IsIntegral R S := ⟨hf⟩
  haveI : Algebra.IsAlgebraic R S := Algebra.IsIntegral.isAlgebraic
  let e : S →ₐ[R] K := IsAlgClosed.lift
  exact ⟨e.toRingHom, RingHom.ext fun r => e.commutes r⟩

private theorem ext_integral {R S K : Type} [CommRing R] [CommRing S] [Field K] [IsAlgClosed K]
    (f : R →+* S) (hf : f.IsIntegral) (φ : R →+* K) (h : RingHom.ker f ≤ RingHom.ker φ) :
    ∃ ψ : S →+* K, ψ.comp f = φ := by
  letI : Algebra R S := f.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hf⟩
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker φ) ⊥ (by
    intro r hr
    apply h
    rw [RingHom.mem_ker]
    exact Ideal.mem_bot.1 (Ideal.mem_comap.1 hr))
  have hQc' : Q.comap f = RingHom.ker φ := hQc
  let φ' : R ⧸ Q.comap f →+* K := Ideal.Quotient.lift _ φ (fun a ha => by
    rw [hQc'] at ha
    exact ha)
  have hφ' : Function.Injective φ' := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem, hQc']
    exact hx
  obtain ⟨ψ, hψ⟩ := ext_injective (Ideal.quotientMap Q f le_rfl) Ideal.quotientMap_injective
    (RingHom.IsIntegral.quotient f hf) φ' hφ'
  refine ⟨ψ.comp (Ideal.Quotient.mk Q), ?_⟩
  ext r
  have := congrArg (fun g => g (Ideal.Quotient.mk _ r)) hψ
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk] at this ⊢
  exact this.trans (Ideal.Quotient.lift_mk _ _ _)

theorem UpperTheory.V.J.lyOver :
    UpperTheory.V.J.LyOver := by
  intro O Λ B K _ _ _ _ _ _ _ _ _ lam J t s g hC p z i hz
  obtain ⟨hprime, hdiv, hnot⟩ := UpperTheory.V.J.cmpPrime O Λ B lam J t s g hC i
  set Q := UpperTheory.V.J.cmp lam J t g i with hQdef
  have hJQ : J ≤ Q := by
    intro a ha
    rw [hQdef, UpperTheory.V.J.cmp, Submodule.mem_colon]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    simpa [smul_eq_mul] using J.mul_mem_right _ ha
  let f : Λ[X] →+* B ⧸ Q := (Ideal.Quotient.mk Q).comp (eval₂RingHom (lam : Λ →+* B) t)
  have hfC : f.comp C = (Ideal.Quotient.mk Q).comp (lam : Λ →+* B) := by
    ext c
    simp [f]
  have hint : f.IsIntegral := by
    apply RingHom.IsIntegral.tower_top C f
    rw [hfC]
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, hqm, hq⟩ := hC.int b
    refine ⟨q, hqm, ?_⟩
    rw [← hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
    exact hJQ hq
  let φ : Λ[X] →+* K := eval₂RingHom (p : Λ →+* K) z
  have hker : RingHom.ker f ≤ RingHom.ker φ := by
    intro q hq
    rw [RingHom.mem_ker] at hq ⊢
    have hq' : eval₂ (lam : Λ →+* B) t q ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [f] using hq
    obtain ⟨r, rfl⟩ := (hdiv q).1 hq'
    simp only [φ, coe_eval₂RingHom, eval₂_mul]
    rw [hz, zero_mul]
  obtain ⟨ψ, hψ⟩ := ext_integral f hint φ hker
  have hc : ∀ c, ψ (Ideal.Quotient.mk Q (lam c)) = p c := by
    intro c
    have := congrArg (fun h => h (C c)) hψ
    simpa [f, φ] using this
  have ht : ψ (Ideal.Quotient.mk Q t) = z := by
    have := congrArg (fun h => h X) hψ
    simpa [f, φ] using this
  refine ⟨{ toRingHom := ψ.comp (Ideal.Quotient.mk Q), commutes' := ?_ }, ?_, ?_, ?_⟩
  · intro o
    have := hc (algebraMap O Λ o)
    simpa using this
  · intro b hb
    rw [RingHom.mem_ker]
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hb]
  · ext c
    simpa using hc c
  · simpa using ht
