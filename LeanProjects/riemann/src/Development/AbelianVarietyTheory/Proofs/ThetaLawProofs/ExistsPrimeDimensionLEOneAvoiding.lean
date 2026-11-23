import Mathlib
open Polynomial
namespace GlobalTheory.LineThrough

theorem exists_common_nonroot (d : ℕ) (S : Set (MvPolynomial (Fin d) ℂ)) (hS : S.Countable)
    (h0 : (0 : MvPolynomial (Fin d) ℂ) ∉ S) :
    ∃ c : Fin d → ℂ, ∀ f ∈ S, MvPolynomial.eval c f ≠ 0 := by
  have hd : Dense (⋂ f ∈ S, {c : Fin d → ℂ | MvPolynomial.eval c f ≠ 0}) := by
    refine dense_biInter_of_isOpen (fun f _ => ?_) hS (fun f hf => ?_)
    · exact isOpen_ne_fun (MvPolynomial.continuous_eval f) continuous_const
    · rw [Metric.dense_iff]
      intro x r hr
      by_contra hne
      apply h0
      have : f = 0 := by
        refine MvPolynomial.funext_set (fun i => Metric.ball (x i) r)
          (fun i => (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)) |> infinite_of_mem_nhds (x i)) ?_
        intro y hy
        by_contra hy0
        apply hne
        refine ⟨y, ?_, by simpa using hy0⟩
        rw [ball_pi _ hr]
        exact hy
      exact this ▸ hf
  obtain ⟨c, hc⟩ := hd.nonempty
  exact ⟨c, fun f hf => by simpa using Set.mem_iInter₂.1 hc f hf⟩

noncomputable def lineMap {d : ℕ} (a c : Fin d → ℂ) : MvPolynomial (Fin d) ℂ →ₐ[ℂ] ℂ[X] :=
  MvPolynomial.aeval fun i => C (a i) + C (c i - a i) * X

theorem eval_zero_lineMap {d : ℕ} (a c : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    (lineMap a c f).eval 0 = MvPolynomial.eval a f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [lineMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, eval_mul, hp]; simp [lineMap]

theorem eval_one_lineMap {d : ℕ} (a c : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    (lineMap a c f).eval 1 = MvPolynomial.eval c f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [lineMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, eval_mul, hp]; simp [lineMap]

theorem lineMap_self {d : ℕ} (a : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    lineMap a a f = C (MvPolynomial.eval a f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [lineMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, hp]; simp [lineMap]

theorem lineMap_surjective {d : ℕ} {a c : Fin d → ℂ} (h : c ≠ a) :
    Function.Surjective (lineMap a c) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have hi' : c i - a i ≠ 0 := sub_ne_zero.2 hi
  have hX : (X : ℂ[X]) ∈ (lineMap a c).range := by
    refine ⟨MvPolynomial.C (c i - a i)⁻¹ * (MvPolynomial.X i - MvPolynomial.C (a i)), ?_⟩
    simp only [lineMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_sub,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [add_sub_cancel_left, ← mul_assoc, ← C_sub, ← C_mul, inv_mul_cancel₀ hi', C_1, one_mul]
  rw [← AlgHom.range_eq_top, eq_top_iff, ← Polynomial.adjoin_X]
  exact Algebra.adjoin_le (by simpa using hX)

theorem isMaximal_of_ker_lineMap_lt {d : ℕ} (a c : Fin d → ℂ)
    (P : Ideal (MvPolynomial (Fin d) ℂ)) [hP : P.IsPrime] (h : RingHom.ker (lineMap a c) < P) :
    P.IsMaximal := by
  by_cases hc : c = a
  · subst hc
    have hk : RingHom.ker (lineMap c c) = RingHom.ker (MvPolynomial.eval c) := by
      ext f
      simp [RingHom.mem_ker, lineMap_self]
    have hm : (RingHom.ker (MvPolynomial.eval c)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun z => ⟨MvPolynomial.C z, by simp⟩)
    rw [hk] at h
    exact absurd (hm.1.2 P h) hP.ne_top
  · have hs := lineMap_surjective hc
    have hp : (P.map (lineMap a c)).IsPrime := Ideal.map_isPrime_of_surjective hs h.le
    have hcm : (P.map (lineMap a c)).comap (lineMap a c) = P := by
      rw [Ideal.comap_map_of_surjective _ hs, sup_eq_left]
      exact h.le
    have hne : P.map (lineMap a c) ≠ ⊥ := by
      intro hb
      rw [hb] at hcm
      exact h.ne hcm
    have hm : (P.map (lineMap a c)).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hne hp
    rw [← hcm]
    exact Ideal.comap_isMaximal_of_surjective _ hs

theorem exists_prime_dimensionLEOne_avoiding
    (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E] [Algebra.FiniteType ℂ E]
    (e : E →ₐ[ℂ] ℂ) (T : Set E) (hT : T.Countable) (h0 : (0 : E) ∉ T) :
    ∃ Q : Ideal E, Q.IsPrime ∧ Q ≤ RingHom.ker e ∧ (∀ r ∈ T, r ∉ Q) ∧
      Ring.DimensionLEOne (E ⧸ Q) := by
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ E
  letI : Algebra (MvPolynomial (Fin d) ℂ) E := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) E := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) E :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hn : ∀ r : T, ∃ n : MvPolynomial (Fin d) ℂ, n ≠ 0 ∧
      algebraMap _ E n ∈ Ideal.span {(r : E)} := by
    intro r
    have hr : (r : E) ≠ 0 := fun h => h0 (h ▸ r.2)
    have := Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin d) ℂ) hr
      (Ideal.mem_span_singleton_self (r : E)) (Algebra.IsIntegral.isIntegral _)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
    exact ⟨n, hn0, hn⟩
  choose n hn0 hn using hn
  haveI : Countable T := hT.to_subtype
  obtain ⟨c, hc⟩ := exists_common_nonroot d (Set.range n) (Set.countable_range n)
    (by rintro ⟨r, hr⟩; exact hn0 r hr)
  let a : Fin d → ℂ := fun i => e (g (MvPolynomial.X i))
  have hea : ∀ f, e (g f) = MvPolynomial.eval a f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r =>
      have : g (MvPolynomial.C r) = algebraMap ℂ E r := g.commutes r
      simp [this]
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp, a]
  haveI hpp : (RingHom.ker (lineMap a c)).IsPrime := RingHom.ker_isPrime _
  haveI hM : (RingHom.ker e).IsPrime := RingHom.ker_isPrime _
  have hle : RingHom.ker (lineMap a c) ≤ (RingHom.ker e).under (MvPolynomial (Fin d) ℂ) := by
    intro f hf
    change e (g f) = 0
    rw [hea, ← eval_zero_lineMap a c, RingHom.mem_ker.1 hf, eval_zero]
  obtain ⟨Q, hQ, hQp, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := RingHom.ker (lineMap a c)) (RingHom.ker e) hle
  have hQc : Q.comap (algebraMap (MvPolynomial (Fin d) ℂ) E) = RingHom.ker (lineMap a c) :=
    hQo.over.symm
  refine ⟨Q, hQp, hQ, fun r hr hrQ => ?_, ⟨fun {P} hP0 hP => ?_⟩⟩
  · have h1 : n ⟨r, hr⟩ ∈ RingHom.ker (lineMap a c) := by
      rw [← hQc]
      exact (Ideal.span_singleton_le_iff_mem _).2 hrQ (hn ⟨r, hr⟩)
    apply hc _ ⟨⟨r, hr⟩, rfl⟩
    rw [← eval_one_lineMap a c, RingHom.mem_ker.1 h1, eval_zero]
  · have hs : Function.Surjective (Ideal.Quotient.mk Q) := Ideal.Quotient.mk_surjective
    have hlt : Q < P.comap (Ideal.Quotient.mk Q) := by
      refine lt_of_le_of_ne (fun x hx => ?_) (fun h => hP0 ?_)
      · simp [Ideal.Quotient.eq_zero_iff_mem.2 hx]
      · rw [← Ideal.map_comap_of_surjective _ hs P, ← h, Ideal.map_quotient_self]
    have hlt' := Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin d) ℂ) hlt
    rw [hQc] at hlt'
    have hm := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := MvPolynomial (Fin d) ℂ) _
      (isMaximal_of_ker_lineMap_lt a c _ hlt')
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hs hm with h | h
    · rw [Ideal.map_comap_of_surjective _ hs] at h
      exact absurd h hP.ne_top
    · rwa [Ideal.map_comap_of_surjective _ hs] at h

end GlobalTheory.LineThrough
