import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSmoothHomogeneousHasSumUnitSmul
open NumberField MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory
namespace UnitLogPartition

open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace

theorem exists_nonneg_hasSum_lattice_translates (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ η : V → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ z, 0 ≤ η z) ∧
      ∀ y, HasSum (fun l : L => η (y + l)) 1 := by
  obtain ⟨R, hR, hcov⟩ := GlobalTheory.exists_radius_lattice_translate_norm_le V L
  let b : ContDiffBump (0 : V) := ⟨R, R + 1, hR, by linarith⟩
  have hφc : HasCompactSupport (b : V → ℝ) := b.hasCompactSupport
  have hφs : ContDiff ℝ ∞ (b : V → ℝ) := b.contDiff
  have hlf := GlobalTheory.PeriodicPartition.locallyFinite_support_translate L b hφc
  set S : V → ℝ := fun z => ∑ᶠ l : L, b (z + l) with hS
  have hSs : ContDiff ℝ ∞ S := by
    rw [← contMDiff_iff_contDiff]
    refine contMDiff_finsum (f := fun (l : L) (z : V) => b (z + l)) (fun l => ?_) hlf
    rw [contMDiff_iff_contDiff]
    exact hφs.comp (contDiff_id.add contDiff_const)
  have hSp : ∀ (l : L) z, S (z + l) = S z := by
    intro l z
    show ∑ᶠ m : L, b (z + l + m) = ∑ᶠ m : L, b (z + m)
    rw [← finsum_comp_equiv (Equiv.addLeft l) (f := fun m : L => b (z + m))]
    simp [add_assoc]
  have hSpos : ∀ z, 0 < S z := by
    intro z
    obtain ⟨l, hl⟩ := hcov z
    have h1 := single_le_finsum (f := fun l : L => b (z + l)) l (hlf.point_finite z)
      (fun l => b.nonneg)
    have h2 : b (z + l) = 1 := b.one_of_mem_closedBall (by simpa using hl)
    simp only [h2] at h1
    exact lt_of_lt_of_le one_pos h1
  refine ⟨fun z => b z / S z, hφs.div hSs fun z => (hSpos z).ne', ?_,
    fun z => div_nonneg b.nonneg (hSpos z).le, fun y => ?_⟩
  · simp only [div_eq_mul_inv]
    exact hφc.mul_right
  · simp only [hSp]
    have hfin : (Function.support fun l : L => b (y + l)).Finite := hlf.point_finite y
    have h1 : HasSum (fun l : L => b (y + l)) (S y) := by
      have hs : Summable (fun l : L => b (y + l)) := summable_of_finite_support hfin
      have := hs.hasSum
      rwa [tsum_eq_finsum hfin] at this
    have := h1.div_const (S y)
    rwa [div_self (hSpos y).ne'] at this

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I] {φ : I → K →+* ℂ}

def idx (hφ : GlobalTheory.CMVal.IsCMType φ) (w : InfinitePlace K) : I := (hφ w.embedding).exists.choose

theorem idx_spec (hφ : GlobalTheory.CMVal.IsCMType φ) (w : InfinitePlace K) :
    w.embedding = φ (idx hφ w) ∨ w.embedding = ComplexEmbedding.conjugate (φ (idx hφ w)) :=
  (hφ w.embedding).exists.choose_spec

theorem apply_eq_norm (hφ : GlobalTheory.CMVal.IsCMType φ) (w : InfinitePlace K) (x : K) :
    w x = ‖φ (idx hφ w) x‖ := by
  rcases idx_spec hφ w with h | h
  · rw [← norm_embedding_eq, h]
  · rw [← norm_embedding_eq, h, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]

theorem idx_surjective (hφ : GlobalTheory.CMVal.IsCMType φ) (i : I) : ∃ w, idx hφ w = i := by
  refine ⟨InfinitePlace.mk (φ i), ?_⟩
  exact (hφ (InfinitePlace.mk (φ i)).embedding).unique (idx_spec hφ _) (embedding_mk_eq (φ i))

theorem ulog_idx [IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    GlobalTheory.HeckeTheta.ulog φ u (idx hφ w) = w.mult * Real.log (w (u : K)) := by
  unfold GlobalTheory.HeckeTheta.ulog
  rw [(IsTotallyComplex.isComplex w).mult_eq_two, ← apply_eq_norm hφ, Real.log_pow]

theorem sum_ulog_idx [IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) :
    ∑ w : InfinitePlace K, GlobalTheory.HeckeTheta.ulog φ u (idx hφ w) = 0 := by
  simp only [ulog_idx hφ]
  exact sum_mult_mul_log u

def mean (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) : ℝ :=
  (∑ w : InfinitePlace K, y (idx hφ w)) / Fintype.card (InfinitePlace K)

def proj (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) : logSpace K :=
  fun w => y (idx hφ w.1) - mean hφ y

theorem proj_add_ulog [IsTotallyComplex K] (hφ : GlobalTheory.CMVal.IsCMType φ) (y : I → ℝ) (u : (𝓞 K)ˣ) :
    proj hφ (y + GlobalTheory.HeckeTheta.ulog φ u) = proj hφ y + logEmbedding K (Additive.ofMul u) := by
  funext w
  have hm : mean hφ (y + GlobalTheory.HeckeTheta.ulog φ u) = mean hφ y := by
    unfold mean
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_ulog_idx hφ, add_zero]
  simp only [proj, hm, Pi.add_apply, logEmbedding_component, ← ulog_idx hφ]
  ring

theorem continuous_proj (hφ : GlobalTheory.CMVal.IsCMType φ) : Continuous (proj hφ) := by
  unfold proj mean
  fun_prop

end UnitLogPartition

open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace UnitLogPartition in

theorem exists_measurable_nonneg_hasSum_ulog_translates : ∀ (K : Type) [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ →
    ∃ p : (I → ℝ) → ℝ, Measurable p ∧ (∀ y, 0 ≤ p y) ∧
      (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) ∧
      ∃ R : ℝ, ∀ y, p y ≠ 0 → ∀ i j, y i - y j ≤ R := by
  classical
  intro K _ _ _ I _ φ hφ
  obtain ⟨η, hη, hc, h0, hs⟩ := exists_nonneg_hasSum_lattice_translates (logSpace K) (unitLattice K)
  refine ⟨fun y => η (proj hφ y) / Nat.card (torsion K), ?_, ?_, ?_, ?_⟩
  · exact ((hη.continuous.comp (continuous_proj hφ)).div_const _).measurable
  · intro y
    exact div_nonneg (h0 _) (Nat.cast_nonneg _)
  · intro y
    have h1 := ((Additive.ofMul.trans (logEmbeddingEquiv K).toEquiv).hasSum_iff).mpr (hs (proj hφ y))
    have h2 := GlobalTheory.UnitPartition.hasSum_quot (torsion K) _ _ h1
    convert h2 using 2 with u
    beta_reduce
    rw [proj_add_ulog hφ]
    rfl
  · obtain ⟨ρ, hρ⟩ := hc.isCompact.isBounded.exists_norm_le
    set n : ℝ := (Fintype.card (InfinitePlace K) : ℝ) with hn_def
    refine ⟨2 * (n * |ρ|), fun y hy i j => ?_⟩
    have hη0 : η (proj hφ y) ≠ 0 := fun h => hy (by simp [h])
    have hn : ‖proj hφ y‖ ≤ ρ := hρ _ (subset_tsupport _ hη0)
    set d : InfinitePlace K → ℝ := fun w => y (idx hφ w) - mean hφ y with hd
    have hn1 : (1 : ℝ) ≤ n := by
      rw [hn_def]; exact Nat.one_le_cast.mpr (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
    have hsub : ∀ w : {w : InfinitePlace K // w ≠ w₀}, |d w.1| ≤ |ρ| := fun w =>
      ((norm_le_pi_norm (proj hφ y) w).trans hn).trans (le_abs_self ρ)
    have hsum : ∑ w, d w = 0 := by
      have hn0 : n ≠ 0 := by positivity
      simp only [hd, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mean]
      rw [← hn_def, mul_div_cancel₀ _ hn0, sub_self]
    have hall : ∀ w, |d w| ≤ n * |ρ| := by
      intro w
      by_cases hw : w = w₀
      · rw [hw]
        rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hsum
        rw [eq_neg_of_add_eq_zero_left hsum, abs_neg]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ |ρ| fun v _ => hsub v).trans ?_
        rw [nsmul_eq_mul]
        gcongr
        rw [Finset.card_univ, hn_def]
        exact_mod_cast Fintype.card_subtype_le _
      · exact (hsub ⟨w, hw⟩).trans (le_mul_of_one_le_left (abs_nonneg _) hn1)
    obtain ⟨v, rfl⟩ := idx_surjective hφ i
    obtain ⟨v', rfl⟩ := idx_surjective hφ j
    have e : y (idx hφ v) - y (idx hφ v') = d v - d v' := by simp [hd]
    rw [e]
    linarith [le_abs_self (d v), neg_abs_le (d v'), hall v, hall v']

end GlobalTheory
