import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PadicPlaceBound

open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

def smallIdeal {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) : Ideal (𝓞 K) where
  carrier := {a | ‖φ (a : K)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    have h := IsUltrametricDist.norm_add_le_max (φ (a : K)) (φ (b : K))
    have h2 : φ ((a + b : 𝓞 K) : K) = φ (a : K) + φ (b : K) := by simp
    change ‖φ ((a + b : 𝓞 K) : K)‖ < 1
    rw [h2]
    exact h.trans_lt (max_lt ha hb)
  smul_mem' := by
    intro c a ha
    have h2 : φ ((c • a : 𝓞 K) : K) = φ (c : K) * φ (a : K) := by simp
    change ‖φ ((c • a : 𝓞 K) : K)‖ < 1
    rw [h2, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral
      (map_isIntegral_int φ c.isIntegral_coe))).trans_lt ha

theorem mem_smallIdeal {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) (a : 𝓞 K) :
    a ∈ smallIdeal φ ↔ ‖φ (a : K)‖ < 1 := Iff.rfl

theorem norm_int_le_one {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) (a : 𝓞 K) :
    ‖φ (a : K)‖ ≤ 1 :=
  GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int φ a.isIntegral_coe)

theorem smallIdeal_isPrime {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C) :
    (smallIdeal φ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro a b hab
    by_contra h
    rw [not_or, mem_smallIdeal, mem_smallIdeal, not_lt, not_lt] at h
    have h2 : φ ((a * b : 𝓞 K) : K) = φ (a : K) * φ (b : K) := by simp
    rw [mem_smallIdeal, h2, norm_mul] at hab
    exact absurd (one_le_mul_of_one_le_of_one_le h.1 h.2) (not_le.2 hab)

theorem exists_embedding_smallIdeal_eq {C : Type} [NormedField C] [IsUltrametricDist C] [IsAlgClosed C]
    [CharZero C] {l : ℕ} (hl : l.Prime) (hlC : ‖(l : C)‖ < 1) (w : HeightOneSpectrum (𝓞 K))
    (hw : (l : 𝓞 K) ∈ w.asIdeal) : ∃ φ : K →+* C, smallIdeal φ = w.asIdeal := by
  have hsub : (w.asIdeal : Set (𝓞 K)) ⊆
      ⋃ φ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] C)) : Set (K →ₐ[ℚ] C)), (smallIdeal φ.toRingHom : Set (𝓞 K)) := by
    intro a ha
    by_contra hna
    simp only [Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, SetLike.mem_coe,
      not_exists, mem_smallIdeal, not_lt] at hna
    have h1 : ∀ φ : K →ₐ[ℚ] C, ‖φ (a : K)‖ = 1 := fun φ =>
      le_antisymm (norm_int_le_one φ.toRingHom a) (hna φ)
    have h2 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ C (a : K))
    rw [norm_prod, Finset.prod_eq_one (fun φ _ => h1 φ), ← Algebra.coe_norm_int, map_intCast] at h2
    have h3 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : 𝓞 K) ∈ w.asIdeal :=
      (Ideal.span_singleton_le_iff_mem _).2 ha (Ideal.absNorm_mem _)
    rw [Ideal.absNorm_span_singleton] at h3
    have h4 : l ∣ (Algebra.norm ℤ a).natAbs := by
      by_contra hnd
      have hc : IsCoprime (l : 𝓞 K) (((Algebra.norm ℤ a).natAbs : ℕ) : 𝓞 K) :=
        Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hl).2 hnd)
      obtain ⟨u, v, huv⟩ := hc
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (huv ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left u hw) (w.asIdeal.mul_mem_left v h3)))
    obtain ⟨c, hc⟩ := Int.natCast_dvd.2 h4
    rw [hc, Int.cast_mul, Int.cast_natCast, norm_mul] at h2
    have h5 := (mul_le_of_le_one_right (norm_nonneg (l : C))
      (IsUltrametricDist.norm_intCast_le_one C c)).trans_lt hlC
    exact absurd h2 h5.ne
  have φ₀ : K →ₐ[ℚ] C := IsAlgClosed.lift
  obtain ⟨φ, -, hφ⟩ := (Ideal.subset_union_prime φ₀ φ₀
    (fun φ _ _ _ => smallIdeal_isPrime φ.toRingHom)).1 hsub
  exact ⟨φ.toRingHom, (w.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top hφ).symm⟩

theorem norm_le_one_of_valuation_le_one {C : Type} [NormedField C] [IsUltrametricDist C] (φ : K →+* C)
    (w : HeightOneSpectrum (𝓞 K)) (hφ : smallIdeal φ = w.asIdeal) (y : K) (hy : w.valuation K y ≤ 1) :
    ‖φ y‖ ≤ 1 := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer y hy
  have hd' : d ∉ smallIdeal φ := by rw [hφ]; exact hd
  rw [mem_smallIdeal, not_lt] at hd'
  have h1 : ‖φ y‖ * ‖φ (d : K)‖ = ‖φ (n : K)‖ := by
    rw [← norm_mul, ← map_mul]
    exact congrArg (fun z => ‖φ z‖) hnd
  calc ‖φ y‖ ≤ ‖φ y‖ * ‖φ (d : K)‖ := le_mul_of_one_le_right (norm_nonneg _) hd'
    _ = ‖φ (n : K)‖ := h1
    _ ≤ 1 := norm_int_le_one φ n

theorem exists_lamC_eq {l : ℕ} [Fact l.Prime] (σ : K →+* ℂ) (φ : K →+* ℂ_[l]) :
    ∃ lam : Qbar →+* ℂ_[l], ∀ x : K, lamC lam (σ x) = φ x := by
  have hmem : ∀ x : K, σ x ∈ Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)
  let σ' : K →+* Qbar := σ.codRestrict Qbar hmem
  letI : Algebra K Qbar := σ'.toAlgebra
  letI : Algebra K ℂ_[l] := φ.toAlgebra
  haveI : IsScalarTower ℚ K Qbar := IsScalarTower.of_algebraMap_eq fun q =>
    ((eq_ratCast (algebraMap ℚ Qbar) q).trans (map_ratCast σ' q).symm).trans
      (congrArg σ' (eq_ratCast (algebraMap ℚ K) q).symm)
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic K Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let lam : Qbar →ₐ[K] ℂ_[l] := IsAlgClosed.lift
  refine ⟨lam.toRingHom, fun x => ?_⟩
  unfold lamC
  rw [dif_pos (hmem x)]
  exact lam.commutes x

theorem norm_prime_padicComplex (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)),
    ← Padic.norm_p]
  exact PadicAlgCl.norm_extends l _

theorem neg_mul_vw_le_vw : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (x : K) (l : ℕ) [Fact l.Prime] (w : Formalism.PairingDivisionLocalBalance.Pl K) (e : ℝ), x ≠ 0 → (l : 𝓞 K) ∈ w.asIdeal → (∀ lam : Qbar →+* ℂ_[l], ‖lamC lam (σ x)‖ ≤ (l : ℝ) ^ e) → -(e * (Formalism.DivisionValues.vw w (l : K) : ℝ)) ≤ (Formalism.DivisionValues.vw w x : ℝ) := by
  intro K _ _ σ x l hl w e hx hw h
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := one_pos.trans hl1
  have hlK : (l : K) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  obtain ⟨φ, hφ⟩ := exists_embedding_smallIdeal_eq (C := ℂ_[l]) hl.out
    (by rw [norm_prime_padicComplex]; exact inv_lt_one_of_one_lt₀ hl1) w hw
  obtain ⟨lam, hlam⟩ := exists_lamC_eq σ φ
  have hb := h lam
  rw [hlam] at hb
  have hvx : w.valuation K x = WithZero.exp (-Formalism.DivisionValues.vw w x) := GlobalTheory.Idele.valuation_eq_exp_neg_count w hx
  have hvl : w.valuation K (l : K) = WithZero.exp (-Formalism.DivisionValues.vw w (l : K)) :=
    GlobalTheory.Idele.valuation_eq_exp_neg_count w hlK
  set n := Formalism.DivisionValues.vw w x
  set m := Formalism.DivisionValues.vw w (l : K)
  have hm : 0 ≤ m := by
    have h1 : w.valuation K (l : K) ≤ 1 := by
      simpa using w.valuation_le_one (K := K) (l : 𝓞 K)
    rw [hvl, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  have hy : w.valuation K ((l : K) ^ n / x ^ m) ≤ 1 := by
    rw [map_div₀, map_zpow₀, map_zpow₀, hvx, hvl, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul,
      ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
    simp only [smul_eq_mul]
    nlinarith
  have h1 := norm_le_one_of_valuation_le_one φ w hφ _ hy
  have hφx : 0 < ‖φ x‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hx)
  rw [map_div₀, map_zpow₀, map_zpow₀, norm_div, norm_zpow, norm_zpow, map_natCast,
    norm_prime_padicComplex, div_le_one (zpow_pos hφx _)] at h1
  have h2 : ‖φ x‖ ^ m ≤ ((l : ℝ) ^ e) ^ m := zpow_le_zpow_left₀ hm hφx.le hb
  have h3 := h1.trans h2
  rw [inv_zpow', ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hl0.le,
    Real.rpow_le_rpow_left_iff hl1] at h3
  push_cast at h3
  linarith

end GlobalTheory.PadicPlaceBound
