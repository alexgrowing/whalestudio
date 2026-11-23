import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ContResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.PlaceMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.FlagNew
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.GradedFlagMoves.FlagMove

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Chain.exists_residual_datum_over_restriction_to_rationals :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) →
      ∀ c₀ : PD Unit (G ℚ Ω) k, (frQ D T.pr (resQ T.F T.g0)).IsRes a c₀ → c₀.In nP →
      ∃ s : PD T.ι (G T.F Ω) k, (T.fr ∅).IsRes a s ∧ T.OverQ c₀ s := by
  intro _ Ω _ _ _ l _ c D T hT k _ a ha c₀ hc₀ hin
  have hG : D.Good := by
    rcases hT.2 with h | h
    · exact h.1.1
    · exact h.1.1
  haveI : NumberField T.F := T.nF
  have hl : l.Prime := Fact.out
  have hpl : ∀ v, ∃ g : G ℚ Ω, (∀ x : Ω, g x ∈ T.pl v ↔ x ∈ D.pl l) ∧
      (∀ s ∈ Dec (T.pl v), g⁻¹ * resQ T.F s * g ∈ Dec (D.pl l)) ∧
      (∀ s ∈ Ine (T.pl v), g⁻¹ * resQ T.F s * g ∈ Ine (D.pl l)) := fun v =>
    Rq.placeMove T.F l hl (T.pl v) (D.pl l) (T.ovl v) (hG.pl_over l hl)
  choose g hg using hpl
  have hne : ∀ h : G ℚ Ω, a ((frQ D T.pr (resQ T.F T.g0)).ν h : c.O) ≠ 0 := by
    intro h
    exact ((Units.map a.toMonoidHom) ((frQ D T.pr (resQ T.F T.g0)).ν h)).ne_zero
  have hn : ∀ v, ∃ n' : UpperTheory.V.GradeZeroInterpolatingElement.M4 k, IsLow n' ∧ IsUp (adj n' * c₀.r (g v) * c₀.n ()) ∧
      (SuppM nP (c₀.r (g v)) ∧ SuppM qQ (c₀.n ()) → SuppM qQ n') := fun v =>
    Rt.flagNew k _ (c₀.r (g v)) (c₀.n ()) (hne (g v)) (hc₀.pair.mult (g v)) (hc₀.pair.low ())
      (Or.inl ⟨hin.1 (g v), hin.2 ()⟩)
  choose n' hn' using hn
  have key : ∀ v, ∀ s ∈ Dec (T.pl v), IsUp (adj (n' v) * c₀.r (resQ T.F s) * n' v) ∧
      ∀ i, (adj (n' v) * c₀.r (resQ T.F s) * n' v) i i = a ((frQ D T.pr (resQ T.F T.g0)).χ i (resQ T.F s) : c.O) := by
    intro v s hs
    have hconj := (hg v).2.1 s hs
    have hX : c₀.r (g v) * c₀.r (g v)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    obtain ⟨h1, h2⟩ := Rt.flagMove k (c₀.r (g v)) (c₀.r (g v)⁻¹)
      (c₀.r ((g v)⁻¹ * resQ T.F s * g v)) (c₀.n ()) (n' v) hX (hc₀.pair.low ()) (hn' v).1
      (hn' v).2.1 (hc₀.pair.flag () _ hconj)
    have he : c₀.r (g v) * c₀.r ((g v)⁻¹ * resQ T.F s * g v) * c₀.r (g v)⁻¹ =
        c₀.r (resQ T.F s) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [he] at h1 h2
    refine ⟨h1, fun i => ?_⟩
    rw [h2 i]
    refine (hc₀.res.char () _ hconj i).trans ?_
    rw [map_mul, map_mul, map_inv, mul_comm _ ((frQ D T.pr (resQ T.F T.g0)).χ i (resQ T.F s)), inv_mul_cancel_right]
  refine ⟨⟨c₀.r.comp (resQ T.F), n'⟩, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩,
    ⟨rfl, fun v => ⟨(), g v, (hg v).1, (hn' v).2.1⟩⟩⟩
  · intro h
    exact hc₀.pair.mult (resQ T.F h)
  · rintro h ⟨A, hA, hI, hb⟩
    show c₀.r (resQ T.F h) = 1
    have hAl : ¬ A.valuation (l : Ω) < 1 := hA l (Finset.mem_insert_self _ _)
    by_cases hS : ∃ p ∈ D.Sb, A.valuation (p : Ω) < 1
    · obtain ⟨p, hp, hpA⟩ := hS
      have hpS : p ∈ D.S := (Finset.mem_filter.1 hp).1
      have hpp : p.Prime := hG.S_prime p hpS
      obtain ⟨γ, -, -, hγ⟩ := Rq.placeMove T.F p hpp A (D.pl p) hpA (hG.pl_over p hpp)
      have hmem := hγ h hI
      have hψ : D.ψ (resQ T.F h) = 1 := by
        refine hT.1.kb A ?_ h hI hb
        intro q hq
        rw [Finset.mem_singleton] at hq
        subst hq
        exact hAl
      have hk := hc₀.pair.kill (γ⁻¹ * resQ T.F h * γ) (Or.inr ⟨p, hp, Subgroup.mem_inf.2 ⟨hmem, by
        rw [MonoidHom.mem_ker, map_mul, map_mul, hψ, mul_one, map_inv, inv_mul_cancel]⟩⟩)
      have hx : resQ T.F h = γ * (γ⁻¹ * resQ T.F h * γ) * γ⁻¹ := by group
      rw [hx, map_mul, map_mul, hk, mul_one, ← map_mul, mul_inv_cancel, map_one]
    · push_neg at hS
      refine hc₀.pair.kill _ (Or.inl ⟨A, ?_, hI, hb⟩)
      intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact hAl
      · exact not_lt.2 (hS q hq)
  · exact hc₀.pair.nrm
  · intro v
    exact (hn' v).1
  · intro v s hs
    exact (key v s hs).1
  · intro v s hs i
    obtain ⟨hsD, m, hm⟩ := hs
    refine ((key v s hsD).2 i).trans ?_
    have hchar : CharP k l := by
      haveI := c.dvr
      haveI := c.fin
      have hmax : ((l : ℕ) : c.O) ∈ IsLocalRing.maximalIdeal c.O := by
        obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (R := ℤ_[l]) (S := c.O)
          (IsLocalRing.maximalIdeal ℤ_[l]) (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _))
        have hlQ : ((l : ℕ) : c.O) ∈ Q := by
          have h0 : ((l : ℕ) : ℤ_[l]) ∈ Q.comap (algebraMap ℤ_[l] c.O) := by
            rw [hQc, PadicInt.maximalIdeal_eq_span_p]
            exact Ideal.subset_span (Set.mem_singleton _)
          simpa using h0
        exact (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
          hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hlQ hu)
      rw [CharP.charP_iff_prime_eq_zero hl]
      have h0 := ha _ hmax
      simpa using h0
    let φ : G T.F Ω →* kˣ := (Units.map a.toMonoidHom).comp
      (((frQ D T.pr (resQ T.F T.g0)).χ i).comp (resQ T.F))
    have hφv : ∀ x, (φ x : k) = c₀.r (resQ T.F x) i i := fun x =>
      (hc₀.res.diag (resQ T.F x) i).symm
    have hlc : IsLocallyConstant (fun x : G T.F Ω => c₀.r (resQ T.F x) i i) := by
      have h1 := (hc₀.cont i i 1).comp_continuous (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω)
      refine IsLocallyConstant.desc _ (Ideal.Quotient.mk ((⊥ : Ideal k) ^ 1)) h1 ?_
      intro x y hxy
      rw [Ideal.Quotient.eq, pow_one, Ideal.mem_bot, sub_eq_zero] at hxy
      exact hxy
    have hcl : IsClosed ((φ.ker : Subgroup (G T.F Ω)) : Set (G T.F Ω)) := by
      have he : ((φ.ker : Subgroup (G T.F Ω)) : Set (G T.F Ω)) =
          (fun x : G T.F Ω => c₀.r (resQ T.F x) i i) ⁻¹' {1} := by
        ext x
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff,
          ← hφv, Units.val_eq_one]
      rw [he]
      exact (hlc.isClopen_fiber 1).isClosed
    have hcomm : ⁅Dec (T.pl v), Dec (T.pl v)⁆ ≤ φ.ker :=
      le_trans (Subgroup.commutator_mono le_top le_top) (Abelianization.commutator_subset_ker φ)
    have hker := Subgroup.topologicalClosure_minimal _ hcomm hcl hm
    rw [MonoidHom.mem_ker, map_pow] at hker
    have hx : (φ s : k) ^ (l ^ m) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hker, Units.val_one]
    have hz : ((φ s : k) - 1) ^ (l ^ m) = 0 := by
      rw [sub_pow_char_pow, one_pow, hx, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ hl.ne_zero) |>.1 hz)
  · intro h i
    exact hc₀.res.diag (resQ T.F h) i
  · intro v s hs i
    exact (key v s hs).2 i
  · exact Or.inl ⟨fun h => hin.1 (resQ T.F h), fun v => (hn' v).2.2 ⟨hin.1 _, hin.2 ()⟩⟩
  · intro i j N
    exact (hc₀.cont i j N).comp_continuous
      (UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω)
