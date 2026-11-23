import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.RootLt

open Polynomial

theorem norm_iotaO_le_one (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a) :
    ‖GlobalTheory.TameFrob.iotaO l a w‖ ≤ 1 := by
  have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l a → Wq l a)) := by
    rw [span_teich]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    set ω := GlobalTheory.TameFrob.iotaO l a (WittVector.teichmuller l z)
    have hω : ω ^ l ^ a = ω := by
      simp only [ω]
      rw [← map_pow, ← map_pow, Fq.pow_card]
    by_contra h
    push_neg at h
    have h2 : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) (Fact.out : l.Prime).one_lt
    have h3 : ‖ω‖ ^ 1 < ‖ω‖ ^ l ^ a := pow_lt_pow_right₀ h h2
    rw [pow_one, ← norm_pow, hω] at h3
    exact lt_irrefl _ h3
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [Algebra.smul_def, map_mul, GlobalTheory.TameFrob.iotaO_algebraMap, norm_mul]
    have hc : ‖algebraMap ℚ_[l] (Om l) (c : ℚ_[l])‖ ≤ 1 :=
      (PadicAlgCl.norm_extends l (c : ℚ_[l])).le.trans c.2
    calc _ ≤ 1 * 1 := mul_le_mul hc hx (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

theorem norm_lt_one_of_isRoot : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P : Polynomial (Wq l a)), P.Monic →
    (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) → ∀ x : Om l, (P.map (GlobalTheory.TameFrob.iotaO l a)).IsRoot x → ‖x‖ < 1 := by
  intro l _ a _ P hP hdiv x hx
  set d := P.natDegree with hd
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · have : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hP h0
    rw [this, Polynomial.map_one] at hx
    simp [Polynomial.IsRoot] at hx
  by_contra hge
  push_neg at hge
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt

  have hnl : ‖GlobalTheory.TameFrob.iotaO l a (l : Wq l a)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hcoef : ∀ i < d, ‖GlobalTheory.TameFrob.iotaO l a (P.coeff i)‖ ≤ (l : ℝ)⁻¹ := by
    intro i hi
    obtain ⟨c, hc⟩ := hdiv i hi
    rw [hc, map_mul, norm_mul, hnl]
    calc _ ≤ (l : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left (norm_iotaO_le_one l a c) (by positivity)
      _ = _ := mul_one _
  have hxd : (1 : ℝ) ≤ ‖x‖ ^ d := one_le_pow₀ hge

  have heq : x ^ d + ∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i = 0 := by
    have h := hx
    rw [Polynomial.IsRoot, hP.as_sum] at h
    simpa [Polynomial.eval_finset_sum, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_sum,
      Polynomial.map_mul] using h
  have hsum : ‖∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i‖ ≤ (l : ℝ)⁻¹ * ‖x‖ ^ d := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [norm_mul, norm_pow]
    exact mul_le_mul (hcoef i hi') (pow_le_pow_right₀ hge hi'.le) (by positivity) (by positivity)
  have hxeq : x ^ d = -∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left heq
  have h1 : ‖x‖ ^ d ≤ (l : ℝ)⁻¹ * ‖x‖ ^ d := by
    calc ‖x‖ ^ d = ‖x ^ d‖ := (norm_pow _ _).symm
      _ = ‖∑ i ∈ Finset.range d, GlobalTheory.TameFrob.iotaO l a (P.coeff i) * x ^ i‖ := by rw [hxeq, norm_neg]
      _ ≤ _ := hsum
  have h2 : (l : ℝ)⁻¹ * ‖x‖ ^ d < ‖x‖ ^ d := by
    have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
    nlinarith
  exact lt_irrefl _ (h1.trans_lt h2)

end GlobalTheory.RootLt
