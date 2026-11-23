import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallLeExp
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.TraceCompl

theorem le_one_iff_of_mul_eq_one {Γ : Type} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} (hab : a * b = 1)
    (hb : b ≤ 1) : a ≤ 1 ↔ b = 1 := by
  constructor
  · intro ha
    by_contra hb1
    have hlt : b < 1 := lt_of_le_of_ne hb hb1
    have : (1 : Γ) < 1 := calc
      (1 : Γ) = a * b := hab.symm
      _ ≤ 1 * b := by gcongr
      _ = b := one_mul b
      _ < 1 := hlt
    exact lt_irrefl _ this
  · rintro rfl
    rw [mul_one] at hab
    exact hab.le

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

theorem algebraMap_int_mem (A : ValuationSubring Ω) (x : 𝓞 K) : algebraMap K Ω x ∈ A := by
  have h1 : IsIntegral ℤ (algebraMap K Ω x) := x.2.map (algebraMap K Ω).toIntAlgHom
  have h2 : IsIntegral A (algebraMap K Ω x) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact hy ▸ y.2

theorem algebraMap_mem_iff {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)
    (x : K) : algebraMap K Ω x ∈ A ↔ v.valuation K x ≤ 1 := by
  have key : ∀ n : 𝓞 K, A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) ≤ 1 ∧
      v.valuation K (algebraMap (𝓞 K) K n) ≤ 1 ∧
      (A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) = 1 ↔
        v.valuation K (algebraMap (𝓞 K) K n) = 1) := by
    intro n
    have h1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) ≤ 1 :=
      (A.valuation_le_one_iff _).2 (algebraMap_int_mem A n)
    have h2 : v.valuation K (algebraMap (𝓞 K) K n) ≤ 1 := v.valuation_le_one n
    have h3 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) < 1 ↔ n ∈ v.asIdeal := h n
    have h4 : v.valuation K (algebraMap (𝓞 K) K n) < 1 ↔ n ∈ v.asIdeal := v.valuation_lt_one_iff_mem n
    refine ⟨h1, h2, ?_⟩
    have e1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) = 1 ↔ n ∉ v.asIdeal := by
      rw [← h3, not_lt]; exact ⟨fun e => e.ge, fun e => le_antisymm h1 e⟩
    have e2 : v.valuation K (algebraMap (𝓞 K) K n) = 1 ↔ n ∉ v.asIdeal := by
      rw [← h4, not_lt]; exact ⟨fun e => e.ge, fun e => le_antisymm h2 e⟩
    exact e1.trans e2.symm
  obtain ⟨n, d, hd | hd⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := K) x
  · have hd1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      have := (v.valuation_lt_one_iff_mem (K := K) (d : 𝓞 K)).not.2 d.2
      exact le_antisymm (v.valuation_le_one _) (not_lt.1 this)
    have hA1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K d)) = 1 := ((key d).2.2).2 hd1
    have e1 := congrArg (fun y => A.valuation (algebraMap K Ω y)) hd
    have e2 := congrArg (v.valuation K) hd
    simp only [map_mul, hA1, hd1, mul_one] at e1 e2
    rw [← A.valuation_le_one_iff, e1, e2]
    exact iff_of_true (key n).1 (key n).2.1
  · have hd1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      have := (v.valuation_lt_one_iff_mem (K := K) (d : 𝓞 K)).not.2 d.2
      exact le_antisymm (v.valuation_le_one _) (not_lt.1 this)
    have hA1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K d)) = 1 := ((key d).2.2).2 hd1
    have e1 := congrArg (fun y => A.valuation (algebraMap K Ω y)) hd
    have e2 := congrArg (v.valuation K) hd
    simp only [map_mul, hA1, hd1] at e1 e2
    rw [← A.valuation_le_one_iff, le_one_iff_of_mul_eq_one e1 (key n).1,
      le_one_iff_of_mul_eq_one e2 (key n).2.1]
    exact (key n).2.2

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem trace_mem {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)
    (hL : IsLocalExt L h) (z : L) (hz : algebraMap L Ω z ∈ A) :
    algebraMap K Ω (Algebra.trace K L z) ∈ A := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  rw [trace_eq_sum_embeddings Ω]
  refine sum_mem fun s _ => ?_
  obtain ⟨τ, hτ⟩ := hL (AlgEquiv.ofBijective (s.liftNormal Ω) (AlgHom.normal_bijective K Ω Ω _))
  have e : s z = (τ : G K Ω) (algebraMap L Ω z) := ((hτ z).trans (s.liftNormal_commutes Ω z)).symm
  rw [e]
  exact (apply_mem_iff_of_mem_Dec (Weil_le_Dec h τ.2) _).2 hz

theorem valuation_trace_le {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (hL : IsLocalExt L h)
    {c : K} (hc : c ≠ 0) {z : L} (hz : v'.valuation L z ≤ v'.valuation L (algebraMap K L c)) :
    v.valuation K (Algebra.trace K L z) ≤ v.valuation K c := by
  have hc' : algebraMap K L c ≠ 0 := (_root_.map_ne_zero _).2 hc
  have h1 : v'.valuation L (z * (algebraMap K L c)⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ hz zero_le'
  have h2 := trace_mem h hL _ ((algebraMap_mem_iff h' _).2 h1)
  rw [algebraMap_mem_iff h, ← map_inv₀, mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul,
    map_mul, map_inv₀] at h2
  have hv : v.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  calc v.valuation K (Algebra.trace K L z)
      = (v.valuation K c)⁻¹ * v.valuation K (Algebra.trace K L z) * v.valuation K c := by
        rw [mul_comm _ (v.valuation K c), ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    _ ≤ 1 * v.valuation K c := by gcongr
    _ = v.valuation K c := one_mul _

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

open WithZero

variable (K : Type) {L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def traceMap (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) :
    WithVal (v'.valuation L) →+ v.adicCompletion K :=
  ((algebraMap K (v.adicCompletion K)).toAddMonoidHom.comp (Algebra.trace K L).toAddMonoidHom).comp
    (WithVal.equiv (v'.valuation L)).toAddMonoidHom

variable {K} {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  [IsScalarTower K L Ω]

theorem continuous_traceMap {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (hL : IsLocalExt L h) :
    Continuous (traceMap K v v') := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hc0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := (_root_.map_ne_zero _).2 γ.ne_zero
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt hc0
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hp0 : algebraMap (𝓞 K) K (π ^ n) ≠ 0 :=
    (_root_.map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (pow_ne_zero n hπ0)
  have hpv : v.valuation K (algebraMap (𝓞 K) K (π ^ n)) ≤ exp (-(n : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact Ideal.pow_mem_pow hπ n
  have hd : v'.valuation L (algebraMap K L (algebraMap (𝓞 K) K (π ^ n))) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((_root_.map_ne_zero _).2 hp0)
  rw [Filter.mem_map, Valued.mem_nhds_zero]
  refine ⟨Units.mk0 ((Valued.v : Valuation (WithVal (v'.valuation L)) ℤᵐ⁰).restrict
    (WithVal.toVal _ (algebraMap K L (algebraMap (𝓞 K) K (π ^ n))))) ?_, fun z hz => hγ ?_⟩
  · simpa using hd
  · rw [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
    rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    have e : traceMap K v v' z = algebraMap K _ (Algebra.trace K L (WithVal.ofVal z)) := rfl
    rw [e, GlobalTheory.Idele.valued_algebraMap]
    exact (valuation_trace_le h h' hL hp0 hz.le).trans_lt (hpv.trans_lt hn)

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

theorem exists_trace_extension : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'), IsLocalExt L h → ∃ T : v'.adicCompletion L →+ v.adicCompletion K, Continuous T ∧ ∀ z : L, T (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' hL
  refine ⟨(AddMonoidHom.extension (traceMap K v v') (continuous_traceMap h h' hL)).comp
    (HeightOneSpectrum.adicCompletion.equiv L v').toAddMonoidHom, ?_, fun z => ?_⟩
  · exact (AddMonoidHom.continuous_extension _ (continuous_traceMap h h' hL)).comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion L v')
  · exact AddMonoidHom.extension_coe _ (continuous_traceMap h h' hL) (WithVal.toVal _ z)

end GlobalTheory.LocLanglands.TraceCompl
