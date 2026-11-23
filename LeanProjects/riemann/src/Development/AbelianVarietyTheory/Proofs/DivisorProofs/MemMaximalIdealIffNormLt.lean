import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulEqZeroOfToCompletion

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section

namespace GlobalTheory.PlaceRing

open IsDedekindDomain NumberField ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen GlobalTheory.EigenLieCompare

theorem mem_maximalIdeal_iff_norm_lt (p : ℕ) [Fact p.Prime] (x : 𝓞_ℂ_[p]) :
    x ∈ IsLocalRing.maximalIdeal 𝓞_ℂ_[p] ↔ ‖(x : ℂ_[p])‖ < 1 := by
  have hv : (Valued.v : Valuation ℂ_[p] _).Integers 𝓞_ℂ_[p] :=
    Valuation.valuationSubring.integers _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one, ← ne_eq,
    ← (hv.map_le_one x).lt_iff_ne]
  change Valued.v (x : ℂ_[p]) < 1 ↔ _
  rw [← GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.valuation_coe_eq_norm, NNReal.coe_lt_one]

theorem natCast_mem_maximalIdeal (p : ℕ) [Fact p.Prime] :
    ((p : ℕ) : 𝓞_ℂ_[p]) ∈ IsLocalRing.maximalIdeal 𝓞_ℂ_[p] := by
  rw [mem_maximalIdeal_iff_norm_lt]
  have h : (((p : ℕ) : 𝓞_ℂ_[p]) : ℂ_[p]) = ((p : ℕ) : ℂ_[p]) := by push_cast; rfl
  rw [h, GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.norm_p]
  exact GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.inv_p_lt_one p

theorem exists_padicInt_hom (p : ℕ) [Fact p.Prime] : Nonempty (ℤ_[p] →+* 𝓞_ℂ_[p]) :=
  ⟨((algebraMap ℚ_[p] ℂ_[p]).comp (PadicInt.Coe.ringHom (p := p))).codRestrict 𝓞_ℂ_[p]
    fun x => by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.mem_iff_norm]
      change ‖algebraMap ℚ_[p] ℂ_[p] (x : ℚ_[p])‖ ≤ 1
      rw [norm_algebraMap']
      exact x.2⟩

theorem faithfulSMul_Ow (p : ℕ) [Fact p.Prime] {E : Type} [Field E] [NumberField E]
    {w : HeightOneSpectrum (𝓞 E)} [Algebra ℤ_[p] (Ow w)] : FaithfulSMul ℤ_[p] (Ow w) := by
  rw [faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot]
  by_contra h
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p h
  have h1 : ((p : ℤ_[p]) ^ n) ∈ RingHom.ker (algebraMap ℤ_[p] (Ow w)) := by
    rw [hn]; exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_pow, map_natCast] at h1
  have h2 : ((p : ℕ) : Ow w) ≠ 0 := by
    intro h0
    have h3 := congrArg (fun y : Ow w => Valued.v (algebraMap (Ow w) (w.adicCompletion E) y)) h0
    rw [← map_natCast (algebraMap (𝓞 E) (Ow w)), valued_algebraMap, map_zero, map_zero] at h3
    exact w.intValuation_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h3
  exact pow_ne_zero n h2 h1

theorem exists_placeRing : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (τ₀ : NumberField.RingOfIntegers E →+* 𝓞_ℂ_[p]), ∃ (Λ : Type) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsDiscreteValuationRing Λ) (_ : Algebra ℤ_[p] Λ) (_ : Module.Finite ℤ_[p] Λ) (_ : FaithfulSMul ℤ_[p] Λ) (π : ℤ_[p] ⊗[ℤ] NumberField.RingOfIntegers E →ₐ[ℤ_[p]] Λ) (e : ℤ_[p] ⊗[ℤ] NumberField.RingOfIntegers E) (t₀ : Λ →+* 𝓞_ℂ_[p]), IsIdempotentElem e ∧ Function.Surjective π ∧ RingHom.ker π = Ideal.span {1 - e} ∧ (∀ a, t₀ (π (1 ⊗ₜ a)) = τ₀ a) ∧ ∀ τ : NumberField.RingOfIntegers E →+* 𝓞_ℂ_[p], (∀ a, ‖(τ a : ℂ_[p])‖ < 1 ↔ ‖(τ₀ a : ℂ_[p])‖ < 1) → ∃ t : Λ →+* 𝓞_ℂ_[p], ∀ a, t (π (1 ⊗ₜ a)) = τ a := by
  intro E _ _ p _ τ₀
  obtain ⟨φ⟩ := exists_padicInt_hom p
  letI : Algebra ℤ_[p] 𝓞_ℂ_[p] := φ.toAlgebra
  have hpP : (p : 𝓞 E) ∈ (IsLocalRing.maximalIdeal 𝓞_ℂ_[p]).comap τ₀ := by
    rw [Ideal.mem_comap, map_natCast]
    exact natCast_mem_maximalIdeal p
  obtain ⟨w, hwP⟩ : ∃ w : HeightOneSpectrum (𝓞 E),
      w.asIdeal = (IsLocalRing.maximalIdeal 𝓞_ℂ_[p]).comap τ₀ := by
    refine ⟨⟨_, Ideal.comap_isPrime _ _, fun h => ?_⟩, rfl⟩
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hpP
    exact (Fact.out : p.Prime).ne_zero hpP
  have hw : GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.IsOver p w := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.IsOver
    rwa [hwP]
  obtain ⟨_, -⟩ := exists_toCompletion hw
  obtain ⟨e, he⟩ := exists_isPlaceIdem hw
  let π : ℤ_[p] ⊗[ℤ] 𝓞 E →ₐ[ℤ_[p]] Ow w := tauExt (p := p) (algebraMap (𝓞 E) (Ow w))
  have hπ : Function.Surjective π := toCompletion_surjective hw
  have hπe : π e = 1 := tauExt_eq_one hw he _ (mem_iff_algebraMap w)
  have hker : RingHom.ker π = Ideal.span {1 - e} := by
    ext x
    constructor
    · intro hx
      have h : e * x = 0 := mul_eq_zero_of_toCompletion hw he hx
      exact Ideal.mem_span_singleton'.2 ⟨x, by linear_combination -h⟩
    · intro hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      rw [RingHom.mem_ker, map_mul, map_sub, map_one, hπe, sub_self, mul_zero]
  have hext : ∀ τ : 𝓞 E →+* 𝓞_ℂ_[p], (∀ a, ‖(τ a : ℂ_[p])‖ < 1 ↔ ‖(τ₀ a : ℂ_[p])‖ < 1) →
      ∃ t : Ow w →+* 𝓞_ℂ_[p], ∀ a, t (π (1 ⊗ₜ a)) = τ a := by
    intro τ hτ
    have h1 : tauExt (p := p) τ e = 1 := tauExt_eq_one hw he τ fun a => by
      rw [hwP, Ideal.mem_comap, mem_maximalIdeal_iff_norm_lt, mem_maximalIdeal_iff_norm_lt, hτ]
    have hk : RingHom.ker π.toRingHom ≤ RingHom.ker (tauExt (p := p) τ).toRingHom := by
      intro x hx
      have hx' : x ∈ Ideal.span {1 - e} := hker ▸ hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
      change tauExt (p := p) τ (a * (1 - e)) = 0
      rw [map_mul, map_sub, map_one, h1, sub_self, mul_zero]
    refine ⟨π.toRingHom.liftOfSurjective hπ ⟨(tauExt (p := p) τ).toRingHom, hk⟩, fun a => ?_⟩
    exact (RingHom.liftOfRightInverse_comp_apply π.toRingHom _ _
      ⟨(tauExt (p := p) τ).toRingHom, hk⟩ (1 ⊗ₜ a)).trans (tauExt_toPadic τ a)
  obtain ⟨t₀, ht₀⟩ := hext τ₀ fun _ => Iff.rfl
  exact ⟨Ow w, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.Finite.of_surjective π.toLinearMap hπ, faithfulSMul_Ow p, π, e, t₀, he.1, hπ, hker, ht₀,
    hext⟩

end GlobalTheory.PlaceRing
