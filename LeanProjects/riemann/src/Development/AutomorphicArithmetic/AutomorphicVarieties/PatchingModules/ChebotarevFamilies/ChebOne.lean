import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.chebOne_split {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {w : Plc L} {B : ValuationSubring Ω} (hB : IsPlaceOver B w)
    (hp : (Ideal.absNorm w.asIdeal).Prime) (x : 𝓞 L)
    (hx : IsCMField.ringOfIntegersComplexConj L x - x ∉ w.asIdeal) :
    Dec (F := Lp L) B ≤ (resP L Ω).range := by
  intro σ hσ
  let ρ : L ≃ₐ[Lp L] L := σ.restrictNormal L
  have hρ : ∀ a : L, algebraMap L Ω (ρ a) = σ (algebraMap L Ω a) := fun a =>
    σ.restrictNormal_commutes L a
  have h2 : ρ = 1 ∨ ρ = IsCMField.complexConj L := by
    have hm : ρ ∈ Submonoid.powers (IsCMField.complexConj L) := by
      rw [mem_powers_iff_mem_zpowers, IsCMField.zpowers_complexConj_eq_top]
      trivial
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp hm
    rw [← hk, ← pow_mod_orderOf, IsCMField.orderOf_complexConj]
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp
  have key : ρ = 1 := by
    refine h2.resolve_right fun hc => ?_
    haveI : Fact (Ideal.absNorm w.asIdeal).Prime := ⟨hp⟩
    haveI : Nontrivial (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
    have hQ : Nat.card (𝓞 L ⧸ w.asIdeal) = Ideal.absNorm w.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    obtain ⟨n, hn⟩ := (AddSubmonoid.mem_multiples_iff _ _).mp
      (mem_multiples_of_prime_card hQ (one_ne_zero (α := 𝓞 L ⧸ w.asIdeal))
        (g' := Ideal.Quotient.mk w.asIdeal x))
    have hxn : x - (n : 𝓞 L) ∈ w.asIdeal :=
      Ideal.Quotient.eq.mp (by rw [map_natCast, ← hn, nsmul_one])
    have e1 : ((IsCMField.ringOfIntegersComplexConj L x : 𝓞 L) : L) = ρ (x : L) := by
      rw [hc]; rfl
    have hs : ∀ y : 𝓞 L, ((y - (n : 𝓞 L) : 𝓞 L) : L) = (y : L) - n := fun y => by simp
    have e : algebraMap L Ω ((IsCMField.ringOfIntegersComplexConj L x - (n : 𝓞 L) : 𝓞 L) : L) =
        σ (algebraMap L Ω ((x - (n : 𝓞 L) : 𝓞 L) : L)) := by
      rw [hs, hs, e1]
      simp only [map_sub, map_natCast, hρ]
    have hcn : IsCMField.ringOfIntegersComplexConj L x - (n : 𝓞 L) ∈ w.asIdeal := by
      refine (hB _).mp ?_
      rw [e, valuation_apply_lt_one_iff hσ]
      exact (hB _).mpr hxn
    apply hx
    have := w.asIdeal.sub_mem hcn hxn
    simpa using this
  refine ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun a => ?_), ?_⟩
  · show σ (algebraMap L Ω a) = algebraMap L Ω a
    rw [← hρ, key]
    rfl
  · ext y
    rfl

theorem UpperTheory.V.Pa.chebOne :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (U : Subgroup (G L Ω)) (g : G L Ω) (A : Set (Plc (Lp L))), IsOpen (U : Set (G L Ω)) → A.Finite → ∃ (v : Plc (Lp L)) (w : Plc L) (B : ValuationSubring Ω) (σ : G L Ω), v ∉ A ∧ IsPlaceOver B w ∧ IsPlaceOver B v ∧ Dec (F := Lp L) B ≤ (resP L Ω).range ∧ IsFrob (F := L) B (normV w) σ ∧ σ * g⁻¹ ∈ U := by
  intro L Ω _ _ _ _ _ _ U g A hU hA
  let φ : Plc L → Plc (Lp L) := fun w =>
    { asIdeal := w.asIdeal.comap (algebraMap (𝓞 (Lp L)) (𝓞 L))
      isPrime := by haveI := w.isPrime; infer_instance
      ne_bot := by
        obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
        exact Ideal.comap_ne_bot_of_integral_mem hy0 hy (Algebra.IsIntegral.isIntegral y) }
  have hφ : ∀ (w : Plc L) (B : ValuationSubring Ω), IsPlaceOver B w → IsPlaceOver B (φ w) := by
    intro w B hB y
    show _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) y ∈ w.asIdeal
    rw [← hB]
    rfl
  obtain ⟨x0, hx0⟩ : ∃ x0 : 𝓞 L, IsCMField.ringOfIntegersComplexConj L x0 ≠ x0 := by
    by_contra! h
    apply IsCMField.complexConj_ne_one L
    ext y
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (𝓞 L) y
    have h' : ∀ a : 𝓞 L, IsCMField.complexConj L (algebraMap (𝓞 L) L a) = algebraMap (𝓞 L) L a :=
      fun a => by
        rw [show algebraMap (𝓞 L) L a = (a : L) from rfl,
          ← IsCMField.coe_ringOfIntegersComplexConj, h a]
    rw [map_div₀, h', h', AlgEquiv.one_apply]
  set d := IsCMField.ringOfIntegersComplexConj L x0 - x0 with hd_def
  have hd : d ≠ 0 := sub_ne_zero.mpr hx0
  have hfin : ∀ y : 𝓞 L, y ≠ 0 → {w : Plc L | y ∈ w.asIdeal}.Finite := fun y hy => by
    have := Ideal.finite_factors (I := Ideal.span {y})
      (by rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hy)
    simpa [Ideal.dvd_span_singleton] using this
  have hfib : ∀ v : Plc (Lp L), {w : Plc L | φ w = v}.Finite := by
    intro v
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    refine (hfin (algebraMap (𝓞 (Lp L)) (𝓞 L) a) ?_).subset ?_
    · intro h0
      apply ha0
      exact FaithfulSMul.algebraMap_injective _ _ (h0.trans (map_zero _).symm)
    · intro w hw
      have hw' : φ w = v := hw
      have : a ∈ (φ w).asIdeal := by rw [hw']; exact ha
      exact this
  let S : Set (Plc L) := {w | d ∈ w.asIdeal} ∪ ⋃ v ∈ A, {w | φ w = v}
  have hS : S.Finite := (hfin d hd).union (hA.biUnion fun v _ => hfib v)
  have hden := GlobalTheory.Published.ChebotarevDegreeOne.dense (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
  have hO : IsOpen ((fun τ : G L Ω => τ * g⁻¹) ⁻¹' (U : Set (G L Ω))) :=
    hU.preimage (continuous_mul_right _)
  obtain ⟨σ, hσU, w, hwS, hin, B, hB, hF⟩ :=
    hden.inter_open_nonempty _ hO ⟨g, by simp [U.one_mem]⟩
  have hp : (Ideal.absNorm w.asIdeal).Prime :=
    ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified L).1 w).mpr hin
  refine ⟨φ w, w, B, σ, ?_, hB, hφ w B hB, UpperTheory.V.Pa.chebOne_split hB hp x0 ?_, hF, hσU⟩
  · intro hv
    exact hwS (Or.inr (Set.mem_biUnion hv rfl))
  · intro h
    exact hwS (Or.inl h)
