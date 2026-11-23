import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DiagChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cont_of_adic {Γ R K : Type} [TopologicalSpace Γ] [CommRing R] [NormedRing K] (I : Ideal R)
    (y : R →+* K) (a : ℝ) (ha1 : a < 1) (hy : ∀ n, ∀ x ∈ I ^ n, ‖y x‖ ≤ a ^ n)
    (f : Γ → R) (hf : AdicCont I f) : Continuous fun g => y (f g) := by
  have ha0 : 0 ≤ a := by simpa using hy 1 0 (Ideal.zero_mem _)
  rw [Metric.continuous_iff']
  intro g0 ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε ha1
  have hopen := (hf N).isOpen_fiber ((Ideal.Quotient.mk (I ^ N)) (f g0))
  filter_upwards [hopen.mem_nhds rfl] with g hg
  rw [dist_eq_norm, ← map_sub]
  exact lt_of_le_of_lt (hy N _ (Ideal.Quotient.eq.mp hg)) hN

theorem UpperTheory.V.Ws.smallCont :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ {ι Γ : Type} [Group Γ] [TopologicalSpace Γ]
          (P : PD ι Γ 𝔞.V), 𝔞.Small P → Continuous (mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) P.r) := by
  intro l _ 𝔞 e he ι Γ _ _ P hP
  obtain ⟨A, _, _, _, f, P₁, hf, hc, rfl⟩ := hP
  obtain ⟨inj, loc, -, -, -⟩ := hf
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let y : A →+* PadicAlgCl l := (e : 𝔞.K →+* PadicAlgCl l).comp (𝔞.toK.comp f)
  have hV : ∀ v : 𝔞.V, ‖e (v : 𝔞.K)‖ ≤ 1 := fun v => (he.2 _).mp v.2
  have hle : ∀ x : A, ‖y x‖ ≤ 1 := fun x => hV (f x)
  have hlt : ‖y ϖ‖ < 1 := by
    refine lt_of_le_of_ne (hle ϖ) fun h1 => hϖ.not_isUnit ?_
    have hne : (f ϖ : 𝔞.K) ≠ 0 := by
      intro h0
      have h0' : f ϖ = 0 := Subtype.ext h0
      exact hϖ.ne_zero (inj (by rw [h0', map_zero]))
    have h1' : ‖e (f ϖ : 𝔞.K)‖ = 1 := h1
    have hinv : ((f ϖ : 𝔞.K))⁻¹ ∈ 𝔞.V := by
      rw [he.2, map_inv₀, norm_inv, h1', inv_one]
    have hu : IsUnit (f ϖ) := IsUnit.of_mul_eq_one (⟨_, hinv⟩ : 𝔞.V) (Subtype.ext (mul_inv_cancel₀ hne))
    haveI := loc
    exact (isUnit_map_iff f ϖ).mp hu
  have hpow : ∀ n, ∀ x ∈ maximalIdeal A ^ n, ‖y x‖ ≤ ‖y ϖ‖ ^ n := by
    intro n x hx
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [map_mul, map_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (hle c)
  refine continuous_matrix fun i j => ?_
  have hc' : AdicCont (maximalIdeal A) fun g => P₁.r g i j := by
    unfold PD.Cont at hc
    exact hc i j
  exact cont_of_adic (maximalIdeal A) y _ hlt hpow (fun g => P₁.r g i j) hc'
