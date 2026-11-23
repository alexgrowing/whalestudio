import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] in

theorem eval₂_scale_of_isWeightedHomogeneous {S : Type*} [CommRing S] [Fintype ι] (w : ι → S)
    (x : Coord n → S) {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    eval₂ (Int.castRingHom S) (fun v ↦ w v.1 * x v) f =
      (∏ k, w k ^ δ k) * eval₂ (Int.castRingHom S) x f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [eval₂_sum, eval₂_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ ↦ ?_
  have hw : Finsupp.weight (coordDeg n) μ = δ := hf (mem_support_iff.mp hμ)
  have hδ : ∀ k, δ k = ∑ v ∈ μ.support with v.1 = k, μ v := by
    intro k
    rw [← hw, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    simp only [coordDeg, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  have hprod : (μ.prod fun v e ↦ w v.1 ^ e) = ∏ k, w k ^ δ k := by
    rw [Finsupp.prod]
    symm
    calc ∏ k, w k ^ δ k = ∏ k, ∏ v ∈ μ.support with v.1 = k, w v.1 ^ μ v := by
          refine Finset.prod_congr rfl fun k _ ↦ ?_
          rw [hδ k, ← Finset.prod_pow_eq_pow_sum]
          refine Finset.prod_congr rfl fun v hv ↦ ?_
          rw [(Finset.mem_filter.mp hv).2]
      _ = ∏ v ∈ μ.support, w v.1 ^ μ v := Finset.prod_fiberwise _ _ _
  rw [← hprod]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  ring

namespace ArithVariety

variable (P : ArithVariety n)

omit [Fintype ι] in

theorem exists_chart :
    ∃ c : (k : ι) → Fin (n k + 1), ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal :=
  ⟨fun k ↦ (P.relevant k).choose, fun k ↦ (P.relevant k).choose_spec⟩

abbrev CoordRing : Type := MvPolynomial (Coord n) ℤ ⧸ P.ideal

instance isPrime_ideal : P.ideal.IsPrime := P.isPrime

instance : IsDomain P.CoordRing := Ideal.Quotient.isDomain _

instance : CharZero P.CoordRing :=
  charZero_of_inj_zero fun m hm ↦ by
    have h : (C (m : ℤ) : MvPolynomial (Coord n) ℤ) ∈ P.ideal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa using hm
    exact_mod_cast P.horizontal _ h

abbrev FunField : Type := FractionRing P.CoordRing

def mkF : MvPolynomial (Coord n) ℤ →+* P.FunField :=
  (algebraMap P.CoordRing P.FunField).comp (Ideal.Quotient.mk P.ideal)

omit [Fintype ι] in
theorem mkF_eq_zero_iff (f : MvPolynomial (Coord n) ℤ) : P.mkF f = 0 ↔ f ∈ P.ideal := by
  rw [mkF, RingHom.comp_apply, ← Ideal.Quotient.eq_zero_iff_mem,
    (IsFractionRing.injective P.CoordRing P.FunField).eq_iff' (map_zero _)]

variable (c : (k : ι) → Fin (n k + 1))

def chartCoord (v : Coord n) : P.FunField := P.mkF (X v) / P.mkF (X ⟨v.1, c v.1⟩)

def chartMap : MvPolynomial (Coord n) ℚ →ₐ[ℚ] P.FunField := aeval (P.chartCoord c)

abbrev ChartAlg : Subalgebra ℚ P.FunField := (P.chartMap c).range

instance : Algebra.FiniteType ℚ (P.ChartAlg c) :=
  Algebra.FiniteType.of_surjective (P.chartMap c).rangeRestrict (AlgHom.rangeRestrict_surjective _)

omit [Fintype ι] in

theorem chartMap_map (f : MvPolynomial (Coord n) ℤ) :
    P.chartMap c (map (Int.castRingHom ℚ) f) = eval₂ (Int.castRingHom _) (P.chartCoord c) f := by
  rw [chartMap, aeval_def, eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

theorem chart_homogeneous (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    (∏ k, P.mkF (X ⟨k, c k⟩) ^ δ k) * eval₂ (Int.castRingHom _) (P.chartCoord c) f = P.mkF f := by
  rw [← eval₂_scale_of_isWeightedHomogeneous _ _ hf]
  have hne : ∀ k, P.mkF (X ⟨k, c k⟩) ≠ 0 := fun k h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)
  have : (fun v : Coord n ↦ P.mkF (X ⟨v.1, c v.1⟩) * P.chartCoord c v) = fun v ↦ P.mkF (X v) := by
    funext v
    rw [chartCoord, mul_div_cancel₀ _ (hne v.1)]
  rw [this]
  conv_rhs => rw [← eval₂_eta f]
  rw [eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

def chartPoint (ψ : P.ChartAlg c →ₐ[ℚ] AlgebraicClosure ℚ) : Cone n (AlgebraicClosure ℚ) :=
  fun k i ↦ ψ ((P.chartMap c).rangeRestrict (X ⟨k, i⟩))

omit [Fintype ι] in

theorem evalCone_chartPoint (ψ : P.ChartAlg c →ₐ[ℚ] AlgebraicClosure ℚ)
    (f : MvPolynomial (Coord n) ℤ) :
    evalCone (P.chartPoint c ψ) f =
      ψ ((P.chartMap c).rangeRestrict (map (Int.castRingHom ℚ) f)) := by
  set χ : MvPolynomial (Coord n) ℚ →ₐ[ℚ] AlgebraicClosure ℚ := ψ.comp (P.chartMap c).rangeRestrict
  change _ = χ (map (Int.castRingHom ℚ) f)
  rw [aeval_unique χ, aeval_def, eval₂_map, evalCone]
  congr 1

theorem chartMap_eq_zero (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ P.ideal) :
    P.chartMap c (map (Int.castRingHom ℚ) f) = 0 := by
  classical
  rw [chartMap_map]
  have hcomp : ∀ m : ι → ℕ,
      eval₂ (Int.castRingHom _) (P.chartCoord c) (weightedHomogeneousComponent (coordDeg n) m f) = 0 := by
    intro m
    have h := P.chart_homogeneous c hc (weightedHomogeneousComponent_isWeightedHomogeneous m f)
    rw [(P.mkF_eq_zero_iff _).mpr (P.homogeneous f hf m)] at h
    have hne : (∏ k, P.mkF (X ⟨k, c k⟩) ^ m k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ fun h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)
    exact (mul_eq_zero.mp h).resolve_left hne
  conv_lhs => rw [← sum_weightedHomogeneousComponent (coordDeg n) f]
  rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), eval₂_sum]
  exact Finset.sum_eq_zero fun m _ ↦ hcomp m

theorem chartPoint_mem (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal)
    (ψ : P.ChartAlg c →ₐ[ℚ] AlgebraicClosure ℚ) :
    P.chartPoint c ψ ∈ P.points (AlgebraicClosure ℚ) := by
  refine ⟨fun k h ↦ ?_, fun f hf ↦ ?_⟩
  · have h1 : (P.chartMap c).rangeRestrict (X ⟨k, c k⟩) = 1 := by
      apply Subtype.ext
      change P.chartMap c (X ⟨k, c k⟩) = 1
      rw [chartMap, aeval_X, chartCoord]
      exact div_self fun h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)
    have h2 : P.chartPoint c ψ k (c k) = 1 := by
      rw [chartPoint, h1, map_one]
    rw [h] at h2
    exact zero_ne_one h2
  · rw [evalCone_chartPoint]
    have : (P.chartMap c).rangeRestrict (map (Int.castRingHom ℚ) f) = 0 :=
      Subtype.ext (P.chartMap_eq_zero c hc hf)
    rw [this, map_zero]

theorem chartMap_ne_zero (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ)
    (hfP : f ∉ P.ideal) : (P.chartMap c).rangeRestrict (map (Int.castRingHom ℚ) f) ≠ 0 := by
  intro h
  have h0 : P.chartMap c (map (Int.castRingHom ℚ) f) = 0 := congrArg Subtype.val h
  rw [chartMap_map] at h0
  have h1 := P.chart_homogeneous c hc hf
  rw [h0, mul_zero, eq_comm, P.mkF_eq_zero_iff] at h1
  exact hfP h1

end ArithVariety

end

end GroundTheory.Heights₂.Heights
