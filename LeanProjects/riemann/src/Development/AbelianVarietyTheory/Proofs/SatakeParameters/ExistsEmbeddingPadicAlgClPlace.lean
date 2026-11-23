import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSumLt
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem norm_finset_sum_lt_of_forall_lt {K : Type*} [NormedField K] [IsUltrametricDist K]
    (s : Finset ℕ) (f : ℕ → K) {r : ℝ} (hr : 0 < r) (h : ∀ i ∈ s, ‖f i‖ < r) :
    ‖∑ i ∈ s, f i‖ < r := by
  first
  | exact @_root_.GlobalTheory.NormSumLt.main
  | exact _root_.GlobalTheory.NormSumLt.main
  | (apply _root_.GlobalTheory.NormSumLt.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormSumLt.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormSumLt.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormSumLt.main ..)

theorem norm_le_one_of_isIntegral_int {K : Type*} [NormedField K] [IsUltrametricDist K]
    {z : K} (hz : IsIntegral ℤ z) : ‖z‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := hz
  by_contra hlt
  push_neg at hlt
  set n := p.natDegree
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree,
    hm.leadingCoeff, map_one, one_mul] at hp
  set S := ∑ i ∈ Finset.range n, (algebraMap ℤ K) (p.coeff i) * z ^ i
  have hS : ‖S‖ < ‖z‖ ^ n := by
    refine norm_finset_sum_lt_of_forall_lt _ _ (pow_pos (by linarith) n) ?_
    intro i hi
    rw [norm_mul, norm_pow]
    have h1 : ‖(algebraMap ℤ K) (p.coeff i)‖ ≤ 1 := by
      rw [eq_intCast]; exact IsUltrametricDist.norm_intCast_le_one K _
    calc ‖(algebraMap ℤ K) (p.coeff i)‖ * ‖z‖ ^ i ≤ 1 * ‖z‖ ^ i :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg _) _)
      _ = ‖z‖ ^ i := one_mul _
      _ < ‖z‖ ^ n := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  have h2 : z ^ n = -S := by linear_combination hp
  have h3 : ‖z‖ ^ n = ‖S‖ := by rw [← norm_pow, h2, norm_neg]
  linarith

theorem exists_embedding_padicAlgCl_place (E : Type) [Field E] [NumberField E] (l : ℕ)
    [Fact l.Prime] : ∃ (τ : E →+* PadicAlgCl l) (w : HeightOneSpectrum (𝓞 E)),
      ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal := by
  let τ : E →+* PadicAlgCl l := (IsAlgClosed.lift : E →ₐ[ℚ] PadicAlgCl l).toRingHom
  have hle : ∀ x : 𝓞 E, ‖τ (x : E)‖ ≤ 1 := fun x =>
    norm_le_one_of_isIntegral_int ((x.isIntegral_coe).map τ.toIntAlgHom)
  let I : Ideal (𝓞 E) :=
    { carrier := {x | ‖τ (x : E)‖ < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        push_cast
        rw [map_add]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        push_cast
        rw [map_mul, norm_mul]
        calc ‖τ (c : E)‖ * ‖τ (x : E)‖ ≤ 1 * ‖τ (x : E)‖ :=
              mul_le_mul_of_nonneg_right (hle c) (norm_nonneg _)
          _ < 1 := by rw [one_mul]; exact hx }
  have hmem : ∀ x : 𝓞 E, x ∈ I ↔ ‖τ (x : E)‖ < 1 := fun x => Iff.rfl
  have hprime : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hmem]
      simp
    · intro x y hxy
      rw [hmem] at hxy
      rw [hmem, hmem]
      by_contra h
      push_neg at h
      have : 1 ≤ ‖τ ((x * y : 𝓞 E) : E)‖ := by
        push_cast
        rw [map_mul, norm_mul]
        exact one_le_mul_of_one_le_of_one_le h.1 h.2
      linarith
  have hne : I ≠ ⊥ := by
    intro hbot
    have hl : ((l : 𝓞 E)) ∈ I := by
      rw [hmem]
      have h1 : ((l : 𝓞 E) : E) = (l : E) := by push_cast; rfl
      rw [h1, map_natCast, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)) l,
        PadicAlgCl.norm_extends]
      exact Padic.norm_p_lt_one
    rw [hbot, Ideal.mem_bot] at hl
    have h2 : ((l : 𝓞 E) : E) = 0 := by rw [hl]; rfl
    have h3 : ((l : 𝓞 E) : E) = (l : E) := by push_cast; rfl
    rw [h3] at h2
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)
  exact ⟨τ, ⟨I, hprime, hne⟩, fun x => (hmem x).symm⟩

end GlobalTheory
