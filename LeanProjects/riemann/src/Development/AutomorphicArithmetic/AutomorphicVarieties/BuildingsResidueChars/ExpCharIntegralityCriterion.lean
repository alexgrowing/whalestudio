import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EcField
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel IsLocalRing UpperTheory.V
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ec_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem ec_le {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] {w : W.Plc L} (j : W.Emb l w)
    (x : 𝒪[w.adicCompletion L]) : ‖j.1 (x : w.adicCompletion L)‖ ≤ 1 := by
  have hc : Continuous fun y : 𝒪[w.adicCompletion L] => ‖j.1 (y : w.adicCompletion L)‖ :=
    (j.2.comp continuous_subtype_val).norm
  obtain ⟨B, hB⟩ := (isCompact_range hc).bddAbove
  by_contra hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (not_le.1 hx)
  have h := hB ⟨x ^ n, rfl⟩
  simp only [SubmonoidClass.coe_pow, map_pow, norm_pow] at h
  exact absurd h (not_le.2 hn)

private theorem ec_lt {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] {w : W.Plc L} (j : W.Emb l w)
    (x : 𝒪[w.adicCompletion L]) (hx : x ∈ maximalIdeal 𝒪[w.adicCompletion L]) :
    ‖j.1 (x : w.adicCompletion L)‖ < 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h1 : valuation (w.adicCompletion L) (x : w.adicCompletion L) < 1 :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 hx
  have h2 : Valued.v (x : w.adicCompletion L) < 1 :=
    (ValuativeRel.isEquiv (valuation (w.adicCompletion L))
      (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one.1 h1
  have ht : Filter.Tendsto (fun k : ℕ => (x : w.adicCompletion L) ^ k) Filter.atTop (nhds 0) :=
    Valued.tendsto_zero_pow_of_v_lt_one h2
  have ht2 := (j.2.tendsto 0).comp ht
  rw [map_zero] at ht2
  refine tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 (ht2.congr fun k => ?_)
  simp

private theorem ec_field {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] {w : W.Plc L} (j : W.Emb l w) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ x, j.1 x ∈ K :=
  _root_.UpperTheory.Reformulated.B.Qh13.ec_field j

theorem UpperTheory.expChar_integrality_criterion :
    ∀ (L : Type) [Field L] [NumberField L] (l : ℕ) [Fact l.Prime] (w : W.Plc L) (j : W.Emb l w), (∀ c : Coef l, ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ x : 𝒪[w.adicCompletion L], j.1 (x : w.adicCompletion L) ∈ c'.O) ∧ ∀ (c' : Coef l), ∀ x ∈ maximalIdeal 𝒪[w.adicCompletion L], ∀ h : j.1 (x : w.adicCompletion L) ∈ c'.O, (⟨_, h⟩ : c'.O) ∈ maximalIdeal c'.O := by
  intro L _ _ l _ w j
  refine ⟨fun c => ?_, fun c' x hx h hu => ?_⟩
  · obtain ⟨K, hK, hj⟩ := ec_field j
    obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
    let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
    have hf : Function.Injective f := Subtype.val_injective
    let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
    let d : Coef l := ⟨(integralClosure ℤ_[l] K).map f, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
      Module.Finite.equiv e.toLinearEquiv⟩
    obtain ⟨c', hc, hd⟩ := (HV.coefSup l).1 c d
    refine ⟨c', hc, fun x => hd ?_⟩
    exact ⟨⟨_, hj x⟩, (isIntegral_algHom_iff f hf).1 ((ec_intIff _).2 (ec_le j x)), rfl⟩
  · obtain ⟨y, hy⟩ := hu.exists_left_inv
    have hy' : (y : PadicAlgCl l) * j.1 (x : w.adicCompletion L) = 1 := congrArg Subtype.val hy
    have h1 : ‖(y : PadicAlgCl l)‖ ≤ 1 :=
      (ec_intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y).map c'.O.val)
    have h2 := mul_lt_one_of_nonneg_of_lt_one_right h1 (norm_nonneg _) (ec_lt j x hx)
    rw [← norm_mul, hy', norm_one] at h2
    exact lt_irrefl _ h2
