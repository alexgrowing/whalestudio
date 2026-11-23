import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TiltAbs

variable {l : ℕ} [Fact l.Prime]

lemma rootT_pow (x : Per.Fl l) (n : ℕ) : rootT x n ^ l ^ n = x.untilt :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n

lemma untilt_add (x y : Per.Fl l) :
    ∃ t : Per.OC l, (x + y).untilt = x.untilt + y.untilt + (l : Per.OC l) * t := by
  have h : Ideal.Quotient.mk (Ideal.span {(l : Per.OC l)}) (x + y).untilt =
      Ideal.Quotient.mk (Ideal.span {(l : Per.OC l)}) (x.untilt + y.untilt) := by
    rw [PreTilt.mk_untilt_eq_coeff_zero, map_add, map_add, PreTilt.mk_untilt_eq_coeff_zero,
      PreTilt.mk_untilt_eq_coeff_zero]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by rw [← ht]; ring⟩

lemma rootT_add (x y : Per.Fl l) (n : ℕ) :
    ∃ t : Per.OC l, rootT (x + y) n = rootT x n + rootT y n + (l : Per.OC l) * t := by
  unfold rootT
  rw [iterate_map_add]
  exact untilt_add _ _

lemma norm_le_one (t : Per.OC l) : ‖(t : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 t.2

lemma norm_l_lt : ‖((l : ℕ) : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt

lemma bound (x y : Per.Fl l) (n : ℕ) :
    ‖(((x + y).untilt : Per.OC l) : ℂ_[l])‖ ≤
      max (max ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ‖((y.untilt : Per.OC l) : ℂ_[l])‖)
        (‖((l : ℕ) : ℂ_[l])‖ ^ l ^ n) := by
  obtain ⟨t, ht⟩ := rootT_add x y n
  rw [← rootT_pow (x + y) n, ← rootT_pow x n, ← rootT_pow y n]
  have h1 : ‖((rootT (x + y) n : Per.OC l) : ℂ_[l])‖ ≤
      max (max ‖((rootT x n : Per.OC l) : ℂ_[l])‖ ‖((rootT y n : Per.OC l) : ℂ_[l])‖)
        ‖((l : ℕ) : ℂ_[l])‖ := by
    rw [ht]
    push_cast
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max
      (IsUltrametricDist.norm_add_le_max _ _) ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one t)
  push_cast
  simp only [norm_pow]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 (l ^ n)
  refine h2.trans ?_
  rcases max_choice (max ‖((rootT x n : Per.OC l) : ℂ_[l])‖ ‖((rootT y n : Per.OC l) : ℂ_[l])‖)
    ‖((l : ℕ) : ℂ_[l])‖ with h | h <;> rw [h]
  · refine le_trans ?_ (le_max_left _ _)
    rcases max_choice ‖((rootT x n : Per.OC l) : ℂ_[l])‖ ‖((rootT y n : Per.OC l) : ℂ_[l])‖
      with h | h <;> rw [h]
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact le_max_right _ _

lemma eq_zero_of_untilt (x : Per.Fl l) (hx : x.untilt = 0) : x = 0 := by
  apply Perfection.ext
  intro n
  have h1 : (((frobeniusEquiv (Per.Fl l) l).symm^[n]) x).untilt = 0 := by
    have h := rootT_pow x n
    rw [hx] at h
    exact pow_eq_zero_iff (pow_ne_zero n (Fact.out : l.Prime).ne_zero) |>.1 h
  have h2 := PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm^[n]) x)
  rw [h1, map_zero] at h2
  have h3 := PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n x
  rw [zero_add] at h3
  have hc : PreTilt.coeff n x = PreTilt.coeff n 0 := by rw [map_zero, ← h3, ← h2]
  simpa only [PreTilt.coeff_def] using hc

theorem untilt_ultrametric_definite (l : ℕ) [Fact l.Prime] (x y : Per.Fl l) :
    ‖(((x + y).untilt : Per.OC l) : ℂ_[l])‖ ≤
      max ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ‖((y.untilt : Per.OC l) : ℂ_[l])‖ ∧
    (x.untilt = 0 → x = 0) := by
  refine ⟨?_, eq_zero_of_untilt x⟩
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have ht : Filter.Tendsto (fun n : ℕ => ‖((l : ℕ) : ℂ_[l])‖ ^ l ^ n) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) norm_l_lt).comp
      (tendsto_pow_atTop_atTop_of_one_lt hl)
  have h2 := (tendsto_const_nhds (x := max ‖((x.untilt : Per.OC l) : ℂ_[l])‖
    ‖((y.untilt : Per.OC l) : ℂ_[l])‖)).max ht
  have h3 := ge_of_tendsto' h2 (bound x y)
  rwa [max_eq_left (le_max_of_le_left (norm_nonneg _))] at h3

end GlobalTheory.TiltAbs
