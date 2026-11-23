import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictPlan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.DedekindLFunctions

noncomputable section

namespace PIW.AdelClassFin

open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix

namespace DictRing

variable {F : Type} [Field F] [NumberField F]

theorem nonempty_places : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩

theorem nontrivial : Nontrivial (Af F) := by
  obtain ⟨v⟩ := nonempty_places (F := F)
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h2 : (0 : v.adicCompletion F) = 1 := congrArg (fun a : Af F => a v) h
  exact zero_ne_one h2

theorem algebraMap_injective : Function.Injective (algebraMap F (Af F)) := by
  haveI := nontrivial (F := F)
  exact (algebraMap F (Af F)).injective

theorem comp_algebraMap (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap (𝓞 F) (Af F) r) v = algebraMap (𝓞 F) (v.adicCompletion F) r := by
  rfl

theorem int_mem (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    algebraMap (𝓞 F) (v.adicCompletion F) r ∈ v.adicCompletionIntegers F := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
  have h : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) =
      v.valuation F (algebraMap (𝓞 F) F r) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F r)
  rw [h]
  exact v.valuation_le_one r

theorem val_alg (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x := by exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem val_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = v.valuation F (algebraMap (𝓞 F) F r) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), val_alg]

theorem cancel {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {ν x : Γ} (hν : ν ≠ 0) (h : ν * x ≤ ν) : x ≤ 1 := by
  have h1 : ν * x ≤ ν * 1 := by rwa [mul_one]
  exact le_of_mul_le_mul_left h1 (zero_lt_iff.mpr hν)

theorem af_denom (a : Af F) : ∃ m : ℕ, 0 < m ∧ (m : Af F) * a ∈ Formalism.UG.intAd F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ (a v ∈ v.adicCompletionIntegers F)}.Finite :=
    Filter.eventually_cofinite.mp a.2
  choose b hb0 hb using fun v : HeightOneSpectrum (𝓞 F) =>
    HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
  let T := hfin.toFinset
  let mv : HeightOneSpectrum (𝓞 F) → ℕ := fun v => Ideal.absNorm (Ideal.span {b v})
  have hmv : ∀ v, 0 < mv v := fun v => by
    refine Nat.pos_of_ne_zero ?_
    simp only [mv, ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero (hb0 v)
  refine ⟨∏ v ∈ T, mv v, Finset.prod_pos fun v _ => hmv v, ?_⟩
  have key : ∀ v : HeightOneSpectrum (𝓞 F),
      ((∏ w ∈ T, mv w : ℕ) : Af F) v * a v ∈ v.adicCompletionIntegers F := by
    intro v
    have hcast : ((∏ w ∈ T, mv w : ℕ) : Af F) = algebraMap (𝓞 F) (Af F) ((∏ w ∈ T, mv w : ℕ) : 𝓞 F) :=
      (map_natCast _ _).symm
    rw [hcast, comp_algebraMap]
    by_cases hv : v ∈ T
    · have hdvd : (b v : 𝓞 F) ∣ ((∏ w ∈ T, mv w : ℕ) : 𝓞 F) := by
        have h1 : ((mv v : ℕ) : 𝓞 F) ∈ Ideal.span {b v} := Ideal.absNorm_mem _
        rw [Ideal.mem_span_singleton] at h1
        exact h1.trans (Nat.cast_dvd_cast (Finset.dvd_prod_of_mem mv hv))
      obtain ⟨d, hd⟩ := hdvd
      rw [hd, map_mul, mul_comm (algebraMap (𝓞 F) (v.adicCompletion F) (b v)), mul_assoc]
      exact mul_mem (int_mem d v) (by rw [mul_comm]; exact hb v)
    · have : a v ∈ v.adicCompletionIntegers F := by simpa [T] using hv
      exact mul_mem (int_mem _ v) this
  exact key

theorem af_approx (a : Af F) (ha : a ∈ Formalism.UG.intAd F) (N : ℕ) (hN : 0 < N) :
    ∃ β : 𝓞 F, ∃ y ∈ Formalism.UG.intAd F, a = algebraMap (𝓞 F) (Af F) β + (N : Af F) * y := by
  classical
  have ha' : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (a v) ≤ 1 := ha
  set n : 𝓞 F := (N : 𝓞 F) with hn
  have hn0 : n ≠ 0 := by rw [hn]; exact_mod_cast hN.ne'
  have hnF : algebraMap (𝓞 F) F n ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hn0
  have hTfin : {v : HeightOneSpectrum (𝓞 F) | v.valuation F (algebraMap (𝓞 F) F n) < 1}.Finite := by
    simp_rw [HeightOneSpectrum.valuation_lt_one_iff_dvd]
    apply Ideal.finite_factors
    simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
  let T := hTfin.toFinset
  have hν0 : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) ≠ 0 := by
    intro v
    rw [val_int]
    exact (Valuation.ne_zero_iff _).2 hnF
  have hν1 : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) ≤ 1 := by
    intro v
    rw [val_int]
    exact v.valuation_le_one n
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ k : F,
      Valued.v (algebraMap F (v.adicCompletion F) k - a v) <
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) := by
    intro v
    have hx0 : algebraMap (𝓞 F) (v.adicCompletion F) n ≠ 0 := (Valuation.ne_zero_iff _).1 (hν0 v)
    have hs : {x : v.adicCompletion F | Valued.v (x - a v) <
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n)} ∈ nhds (a v) :=
      Valued.mem_nhds.mpr ⟨Units.mk0 (Valued.v.restrict (algebraMap (𝓞 F) (v.adicCompletion F) n))
        ((Valuation.ne_zero_iff _).2 hx0), fun y hy => by simpa [Valuation.restrict_lt_iff] using hy⟩
    obtain ⟨_, hy, ⟨k, rfl⟩⟩ :=
      mem_closure_iff_nhds.mp (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) (v := v) (a v)) _ hs
    exact ⟨k, hy⟩
  choose k hk using hloc
  obtain ⟨t, ht1, ht2⟩ := PI.StrongApproxE.DedekindLFunctions.sa (R := 𝓞 F) (K := F) T k
    (fun _ => algebraMap (𝓞 F) F n) (fun _ _ => hnF)

  have hclose : ∀ v ∈ T, Valued.v (a v - algebraMap F (v.adicCompletion F) t) ≤
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) := by
    intro v hv
    have e : a v - algebraMap F (v.adicCompletion F) t =
        -(algebraMap F (v.adicCompletion F) (k v) - a v) + algebraMap F (v.adicCompletion F) (k v - t) := by
      rw [map_sub]; ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [Valuation.map_neg]; exact (hk v).le
    · rw [val_alg, Valuation.map_sub_swap, val_int]; exact ht1 v hv
  have htint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F t ≤ 1 := by
    intro v
    by_cases hv : v ∈ T
    · rw [← val_alg]
      have e : algebraMap F (v.adicCompletion F) t = a v - (a v - algebraMap F (v.adicCompletion F) t) := by ring
      rw [e]
      exact (Valuation.map_sub _ _ _).trans (max_le (ha' v) ((hclose v hv).trans (hν1 v)))
    · exact ht2 v hv
  obtain ⟨β, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) t htint
  have hu : IsUnit (algebraMap (𝓞 F) (Af F) n) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (Af F)]
    exact (Ne.isUnit hnF).map (algebraMap F (Af F))
  set y : Af F := ↑hu.unit⁻¹ * (a - algebraMap (𝓞 F) (Af F) β) with hy
  have hNy : algebraMap (𝓞 F) (Af F) n * y = a - algebraMap (𝓞 F) (Af F) β := by
    rw [hy, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have hNcast : (N : Af F) = algebraMap (𝓞 F) (Af F) n := by rw [hn, map_natCast]
  refine ⟨β, y, ?_, by rw [hNcast, hNy]; ring⟩
  have key : ∀ v : HeightOneSpectrum (𝓞 F), y v ∈ v.adicCompletionIntegers F := by
    intro v
    have hv' : algebraMap (𝓞 F) (v.adicCompletion F) n * y v =
        a v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F β) := by
      have := congrArg (fun z : Af F => z v) hNy
      rw [← IsScalarTower.algebraMap_apply, ← comp_algebraMap, ← comp_algebraMap]
      exact this
    have hle : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) * Valued.v (y v) ≤
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) := by
      rw [← Valuation.map_mul, hv']
      by_cases hv : v ∈ T
      · exact hclose v hv
      · have h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) n) = 1 := by
          refine le_antisymm (hν1 v) (not_lt.mp ?_)
          rw [val_int]
          simpa [T] using hv
        rw [h1]
        refine (Valuation.map_sub _ _ _).trans (max_le (ha' v) ?_)
        rw [val_alg]; exact htint v
    exact cancel (hν0 v) hle
  exact key

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem tmul_mem {x : E} (hx : x ∈ Formalism.UG.intOE E) {y : Af F} (hy : y ∈ Formalism.UG.intAd F) :
    x ⊗ₜ[F] y ∈ IntAf F E := by
  have h1 : x ⊗ₜ[F] (1 : Af F) ∈ IntAf F E := Subring.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)
  have h2 : (1 : E) ⊗ₜ[F] y ∈ IntAf F E := Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  have h3 := mul_mem h1 h2
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h3

theorem incl_mem (a : 𝓞 E) : Formalism.UG.inclE (F := F) (Af F) (a : E) ∈ IntAf F E :=
  Subring.subset_closure (Or.inl ⟨⟨(a : E), a, rfl⟩, rfl⟩)

theorem incl_add (a b : 𝓞 E) : Formalism.UG.inclE (F := F) (Af F) ((a + b : 𝓞 E) : E) =
    Formalism.UG.inclE (F := F) (Af F) (a : E) + Formalism.UG.inclE (F := F) (Af F) (b : E) := by simp

theorem incl_mul (a b : 𝓞 E) : Formalism.UG.inclE (F := F) (Af F) ((a * b : 𝓞 E) : E) =
    Formalism.UG.inclE (F := F) (Af F) (a : E) * Formalism.UG.inclE (F := F) (Af F) (b : E) := by simp

theorem incl_neg (a : 𝓞 E) : Formalism.UG.inclE (F := F) (Af F) ((-a : 𝓞 E) : E) =
    -Formalism.UG.inclE (F := F) (Af F) (a : E) := by simp

theorem incl_zero : Formalism.UG.inclE (F := F) (Af F) ((0 : 𝓞 E) : E) = 0 := by simp

theorem incl_one : Formalism.UG.inclE (F := F) (Af F) ((1 : 𝓞 E) : E) = 1 := by simp

theorem e_denom (e : E) : ∃ m : ℕ, 0 < m ∧ (m : E) * e ∈ Formalism.UG.intOE E := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
  have hi := hy e (Finset.mem_singleton_self e)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  have hi' : IsIntegral ℤ ((y.natAbs : E) * e) := by
    rcases Int.natAbs_eq y with h | h
    · rw [h, zsmul_eq_mul] at hi
      simpa using hi
    · rw [h, zsmul_eq_mul] at hi
      simpa using hi.neg
  exact ⟨⟨_, hi'⟩, rfl⟩

end DictRing

theorem dual_denominator : DDenom := by
  intro F E _ _ _ _ _ r
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [mul_zero]; exact zero_mem _⟩
  | tmul e a =>
    obtain ⟨m₁, hm₁, he⟩ := DictRing.e_denom e
    obtain ⟨m₂, hm₂, ha⟩ := DictRing.af_denom a
    refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, ?_⟩
    have hc : ((m₁ * m₂ : ℕ) : E ⊗[F] Af F) = (m₁ : E) ⊗ₜ[F] (m₂ : Af F) := by
      rw [Nat.cast_mul, Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.natCast_def',
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hc, Algebra.TensorProduct.tmul_mul_tmul]
    exact DictRing.tmul_mem he ha
  | add x y hx hy =>
    obtain ⟨m₁, hm₁, h₁⟩ := hx
    obtain ⟨m₂, hm₂, h₂⟩ := hy
    refine ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, ?_⟩
    have e : ((m₁ * m₂ : ℕ) : E ⊗[F] Af F) * (x + y) =
        (m₂ : E ⊗[F] Af F) * ((m₁ : E ⊗[F] Af F) * x) + (m₁ : E ⊗[F] Af F) * ((m₂ : E ⊗[F] Af F) * y) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) h₁) (mul_mem (natCast_mem _ _) h₂)

theorem dual_dense : DDense := by
  intro F E _ _ _ _ _ N hN r hr
  have hr' : r ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
      Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) := hr
  clear hr
  induction hr' using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · exact ⟨a, 0, zero_mem _, by rw [mul_zero, add_zero]; rfl⟩
    · obtain ⟨β, y', hy', hyeq⟩ := DictRing.af_approx y hy N hN
      let b : 𝓞 E := ⟨algebraMap F E (algebraMap (𝓞 F) F β), (RingOfIntegers.isIntegral_coe β).algebraMap⟩
      refine ⟨b, (1 : E) ⊗ₜ[F] y', DictRing.tmul_mem (one_mem _) hy', ?_⟩
      show (1 : E) ⊗ₜ[F] y = algebraMap F E (algebraMap (𝓞 F) F β) ⊗ₜ[F] (1 : Af F) +
        (N : E ⊗[F] Af F) * ((1 : E) ⊗ₜ[F] y')
      rw [hyeq, TensorProduct.tmul_add, Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, IsScalarTower.algebraMap_apply (𝓞 F) F (Af F), Algebra.algebraMap_eq_smul_one (R := F) (A := Af F),
        Algebra.algebraMap_eq_smul_one (R := F) (A := E), TensorProduct.smul_tmul]
  | zero => exact ⟨0, 0, zero_mem _, by rw [DictRing.incl_zero, mul_zero, add_zero]⟩
  | one => exact ⟨1, 0, zero_mem _, by rw [DictRing.incl_one, mul_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a₁, r₁, hr₁, e₁⟩ := hx
    obtain ⟨a₂, r₂, hr₂, e₂⟩ := hy
    exact ⟨a₁ + a₂, r₁ + r₂, add_mem hr₁ hr₂, by rw [e₁, e₂, DictRing.incl_add]; ring⟩
  | neg x _ hx =>
    obtain ⟨a₁, r₁, hr₁, e₁⟩ := hx
    exact ⟨-a₁, -r₁, neg_mem hr₁, by rw [e₁, DictRing.incl_neg]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a₁, r₁, hr₁, e₁⟩ := hx
    obtain ⟨a₂, r₂, hr₂, e₂⟩ := hy
    refine ⟨a₁ * a₂, r₁ * Formalism.UG.inclE (F := F) (Af F) (a₂ : E) + Formalism.UG.inclE (F := F) (Af F) (a₁ : E) * r₂ +
      (N : E ⊗[F] Af F) * r₁ * r₂, ?_, by rw [e₁, e₂, DictRing.incl_mul]; ring⟩
    exact add_mem (add_mem (mul_mem hr₁ (DictRing.incl_mem a₂)) (mul_mem (DictRing.incl_mem a₁) hr₂))
      (mul_mem (mul_mem (natCast_mem _ N) hr₁) hr₂)

end PIW.AdelClassFin
