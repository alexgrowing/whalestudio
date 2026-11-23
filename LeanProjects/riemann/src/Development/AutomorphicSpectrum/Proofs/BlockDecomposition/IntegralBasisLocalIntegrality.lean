import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.GENSL
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
import GroundTheory.HeightsAndTheta.Theta.WeilNonarchProps
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3.R (G2 Jd md KA LInv pri dia2 pt)
open scoped NumberField.AdeleRing ValuativeRel ComplexConjugate
open GroundTheory.Global.AdicLiesOver
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.IntCoord

variable {K : Type} [Field K] [NumberField K]

theorem mem_O_iff (w : HeightOneSpectrum (𝓞 K)) (x : w.adicCompletion K) :
    x ∈ 𝒪[w.adicCompletion K] ↔ Valued.v x ≤ 1 :=
  (mem_valuationInteger_iff w x).trans (HeightOneSpectrum.mem_adicCompletionIntegers _ _ w)

theorem val_alg (w : HeightOneSpectrum (𝓞 K)) (k : K) :
    Valued.v (algebraMap K (w.adicCompletion K) k) = w.valuation K k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w k

theorem val_le_of_integral (w : HeightOneSpectrum (𝓞 K)) {b : K} (h : IsIntegral ℤ b) :
    w.valuation K b ≤ 1 :=
  HeightOneSpectrum.valuation_le_one (K := K) w (⟨b, h⟩ : 𝓞 K)

theorem val_int (w : HeightOneSpectrum (𝓞 K)) (z : ℤ) : w.valuation K (z : K) =
    w.valuation K (algebraMap (𝓞 K) K (z : 𝓞 K)) := by
  simp

theorem exists_factor (v : Pl) (d : ℤ) (hd : d ≠ 0) : ∃ (p m : ℤ) (n : ℕ),
    v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} ∧ (m : 𝓞 ℚ) ∉ v.asIdeal ∧ d = p ^ n * m := by
  have hcast : ∀ u : 𝓞 ℚ, ((Rat.ringOfIntegersEquiv u : ℤ) : 𝓞 ℚ) = u := fun u => by
    rw [← map_intCast Rat.ringOfIntegersEquiv.symm, Int.cast_id, RingEquiv.symm_apply_apply]
  haveI : IsPrincipalIdealRing (𝓞 ℚ) :=
    IsPrincipalIdealRing.of_surjective (Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ).toRingHom
      (Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ).surjective
  obtain ⟨π, hπ⟩ : ∃ π : 𝓞 ℚ, v.asIdeal = Ideal.span {π} :=
    (IsPrincipalIdealRing.principal v.asIdeal).principal
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact v.ne_bot (by simpa using hπ)
  have hprime : Prime π := (Ideal.span_singleton_prime hπ0).1 (hπ ▸ v.isPrime)
  have ha0 : (d : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hd
  obtain ⟨n, m, hm, ha⟩ := WfDvdMonoid.max_power_factor ha0 hprime.irreducible
  refine ⟨Rat.ringOfIntegersEquiv π, Rat.ringOfIntegersEquiv m, n, ?_, ?_, ?_⟩
  · rw [hcast]; exact hπ
  · rw [hcast, hπ, Ideal.mem_span_singleton]; exact hm
  · have := congrArg Rat.ringOfIntegersEquiv ha
    simpa using this

theorem liesOver_of_mem (v : Pl) (w : PlK K) {p : ℤ} (hp : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)})
    (h : (p : 𝓞 K) ∈ w.asIdeal) : w.asIdeal.LiesOver v.asIdeal := by
  refine ⟨v.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) ?_⟩
  rw [hp, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_intCast]
  exact h

theorem smul_int (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] {a : Qv v} {b : Kv K w}
    (ha : a ∈ 𝒪[Qv v]) (hb : b ∈ 𝒪[Kv K w]) : a • b ∈ 𝒪[Kv K w] := by
  rw [Algebra.smul_def]
  refine mul_mem ?_ hb
  rw [mem_O_iff, valued_algebraMap_adicCompletion v w a]
  exact pow_le_one' ((mem_O_iff v a).1 ha) _

theorem rat_case (v : Pl) (β : Module.Basis (Fin 2) ℚ K) (hβ : IntB β) (ξ : K)
    (h : ∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], algebraMap K (Kv K w) ξ ∈ 𝒪[Kv K w])
    (i : Fin 2) : algebraMap ℚ (Qv v) (β.repr ξ i) ∈ 𝒪[Qv v] := by
  obtain ⟨d, hd0, hd⟩ : ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : K) * ξ) := by
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors ℤ) ξ
      (Algebra.IsIntegral.isIntegral (R := ℚ) ξ)
    refine ⟨m, nonZeroDivisors.coe_ne_zero m, ?_⟩
    rwa [Submonoid.smul_def, zsmul_eq_mul] at hm
  obtain ⟨p, m, n, hp, hm, hdm⟩ := exists_factor v d hd0
  have hall : ∀ w : PlK K, w.valuation K ((m : K) * ξ) ≤ 1 := by
    intro w
    by_cases hw : w.asIdeal.LiesOver v.asIdeal
    · haveI := hw
      rw [map_mul]
      refine mul_le_one' ?_ ?_
      · rw [val_int]; exact HeightOneSpectrum.valuation_le_one w _
      · rw [← val_alg]; exact (mem_O_iff w _).1 (h w)
    · have hpw : (p : 𝓞 K) ∉ w.asIdeal := fun hh => hw (liesOver_of_mem v w hp hh)
      have hv1 : w.valuation K (p : K) = 1 := by
        rw [val_int]
        exact le_antisymm (HeightOneSpectrum.valuation_le_one w _)
          (not_lt.1 (mt (HeightOneSpectrum.valuation_lt_one_iff_mem w _).1 hpw))
      have h1 := val_le_of_integral w hd
      rw [hdm] at h1
      push_cast at h1
      rw [mul_assoc, map_mul, map_pow, hv1, one_pow, one_mul] at h1
      exact h1
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K _ hall
  have hint : IsIntegral ℤ ((m : K) * ξ) := by
    rw [← hy]; exact y.isIntegral_coe
  obtain ⟨k, hk⟩ := (hβ _).1 hint i
  have hsm : (m : K) * ξ = (m : ℚ) • ξ := by
    rw [Algebra.smul_def]; simp
  rw [hsm, map_smul, Finsupp.smul_apply, smul_eq_mul] at hk
  have hq : ((m : ℤ) : Qv v) * algebraMap ℚ (Qv v) (β.repr ξ i) = ((k : ℤ) : Qv v) := by
    have := congrArg (algebraMap ℚ (Qv v)) hk
    simpa using this
  have hvz : ∀ z : ℤ, Valued.v ((z : ℤ) : Qv v) = v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (z : 𝓞 ℚ)) := by
    intro z
    have e : ((z : ℤ) : Qv v) = @algebraMap ℚ (v.adicCompletion ℚ) _ _ (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v) (z : ℚ) :=
      (map_intCast (@algebraMap ℚ (v.adicCompletion ℚ) _ _ (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v)) z).symm
    rw [e, val_alg, val_int]
  have hvm : Valued.v ((m : ℤ) : Qv v) = 1 := by
    rw [hvz]
    exact le_antisymm (HeightOneSpectrum.valuation_le_one v _)
      (not_lt.1 (mt (HeightOneSpectrum.valuation_lt_one_iff_mem v _).1 hm))
  have hvk : Valued.v ((k : ℤ) : Qv v) ≤ 1 := by
    rw [hvz]; exact HeightOneSpectrum.valuation_le_one v _
  rw [mem_O_iff v]
  have := congrArg Valued.v hq
  rw [map_mul, hvm, one_mul] at this
  exact this ▸ hvk

theorem exists_rat_near (v : Pl) (x : Qv v) : ∃ q : ℚ, x - algebraMap ℚ (Qv v) q ∈ 𝒪[Qv v] := by
  have hc : Continuous (fun y : Qv v => x - y) := continuous_const.sub continuous_id
  have ho := (Valued.isOpen_integer (Qv v)).preimage hc
  obtain ⟨q, hq⟩ := (HeightOneSpectrum.denseRange_algebraMap ℚ v).exists_mem_open ho
    ⟨x, by simp [Valuation.mem_integer_iff]⟩
  refine ⟨q, ?_⟩
  rw [mem_O_iff v]
  have e : algebraMap ℚ (Qv v) q = @algebraMap ℚ (v.adicCompletion ℚ) _ _ (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v) q :=
    (eq_ratCast _ q).trans (eq_ratCast _ q).symm
  rw [e]
  exact hq

theorem coords_integral_iff : ∀ (K : Type) [Field K] [NumberField K] (v : Pl) (β : Module.Basis (Fin 2) ℚ K), IntB β → ∀ x : Fin 2 → Qv v, (∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], (∑ i, x i • algebraMap K (Kv K w) (β i)) ∈ 𝒪[Kv K w]) ↔ ∀ i, x i ∈ 𝒪[Qv v] := by
  intro K _ _ v β hβ x
  have hb : ∀ (w : PlK K) (i : Fin 2), algebraMap K (Kv K w) (β i) ∈ 𝒪[Kv K w] := by
    intro w i
    have hi : IsIntegral ℤ (β i) := (hβ _).2 fun j => by
      by_cases hij : i = j
      · exact ⟨1, by simp [hij]⟩
      · exact ⟨0, by simp [Finsupp.single_apply, hij]⟩
    rw [mem_O_iff, val_alg]
    exact val_le_of_integral w hi
  constructor
  · intro h
    choose r hr using fun i => exists_rat_near v (x i)
    have hrep : ∀ i, β.repr (∑ j, r j • β j) i = r i := fun i => by
      rw [Module.Basis.repr_sum_self]
    have hint : ∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal],
        algebraMap K (Kv K w) (∑ j, r j • β j) ∈ 𝒪[Kv K w] := by
      intro w _
      have e : algebraMap K (Kv K w) (∑ j, r j • β j) =
          (∑ i, x i • algebraMap K (Kv K w) (β i)) -
            ∑ i, (x i - algebraMap ℚ (Qv v) (r i)) • algebraMap K (Kv K w) (β i) := by
        rw [← Finset.sum_sub_distrib, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← sub_smul, sub_sub_cancel, Algebra.smul_def (r i), map_mul, Algebra.smul_def,
          ← IsScalarTower.algebraMap_apply ℚ (Qv v) (Kv K w),
          ← IsScalarTower.algebraMap_apply ℚ K (Kv K w)]
      rw [e]
      exact sub_mem (h w) (sum_mem fun i _ => smul_int v w (hr i) (hb w i))
    intro i
    have h1 := rat_case v β hβ _ hint i
    rw [hrep] at h1
    have := add_mem (hr i) h1
    simpa using this
  · intro h w _
    exact sum_mem fun i _ => smul_int v w (h i) (hb w i)

end GlobalTheory.CompanionTheory.IntCoord
