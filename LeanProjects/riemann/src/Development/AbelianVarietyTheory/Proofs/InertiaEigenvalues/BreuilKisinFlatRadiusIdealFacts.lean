import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.FlatDisc
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem exists_eq_add (bk : BK K) : ∃ Q : Polynomial (Wq l bk.a),
    bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * Q := by
  have hd : ∀ i ∈ Finset.range bk.Ep.natDegree, ∃ c, bk.Ep.coeff i = (l : Wq l bk.a) * c :=
    fun i hi => bk.dvd_coeff i (Finset.mem_range.1 hi)
  choose d hd using hd
  refine ⟨∑ i ∈ (Finset.range bk.Ep.natDegree).attach, Polynomial.C (d i.1 i.2) * Polynomial.X ^ i.1, ?_⟩
  refine bk.monic.as_sum.trans (congrArg (Polynomial.X ^ bk.Ep.natDegree + ·) ?_)
  rw [Finset.mul_sum, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd i.1 i.2, Polynomial.C_mul, mul_assoc]

theorem exists_E_eq (bk : BK K) : ∃ Q : Polynomial (Wq l bk.a),
    bk.E = (X : bk.S) ^ bk.Ep.natDegree + (l : bk.S) * (Q : bk.S) := by
  obtain ⟨Q, hQ⟩ := exists_eq_add bk
  refine ⟨Q, ?_⟩
  change ((bk.Ep : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) = _
  conv_lhs => rw [hQ]
  rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C, map_natCast]

theorem ev_coe (bk : BK K) (p : Polynomial (Wq l bk.a)) :
    bk.ev (p : bk.S) = p.eval₂ (bk.ev.comp (C (R := Wq l bk.a))) (bk.ev X) := by
  have h : bk.ev.comp (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) =
      Polynomial.eval₂RingHom (bk.ev.comp (C (R := Wq l bk.a))) (bk.ev X) := by
    refine Polynomial.ringHom_ext (fun w => ?_) ?_
    · simp [Polynomial.coeToPowerSeries.ringHom_apply]
    · simp [Polynomial.coeToPowerSeries.ringHom_apply]
  exact RingHom.congr_fun h p

theorem theta_ev_E (bk : BK K) : Per.θ l (bk.ev bk.E) = 0 := by
  have h : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := by
    rw [← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  exact h

theorem natCast_l_ne_zero : ((l : ℕ) : Per.OC l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero

theorem flat_ne_zero (bk : BK K) : bk.flat ≠ 0 := by
  intro h0
  have hX : bk.ev X = 0 := by rw [bk.ev_X, h0, WittVector.teichmuller_zero]
  have h := theta_ev_E bk
  rw [BK.E, ev_coe, hX, Polynomial.eval₂_at_zero, RingHom.comp_apply, bk.ev_C] at h
  obtain ⟨w, hw⟩ := bk.coeff_zero
  rw [hw, map_mul, map_natCast, map_mul, map_natCast] at h
  have hu : IsUnit (Per.θ l (wA l bk.a (w : Wq l bk.a))) := (w.isUnit.map (wA l bk.a)).map (Per.θ l)
  exact natCast_l_ne_zero ((mul_eq_zero.1 h).resolve_right hu.ne_zero)

theorem not_isUnit_flat (bk : BK K) : ¬ IsUnit bk.flat := by
  intro hu
  obtain ⟨Q, hQ⟩ := exists_E_eq bk
  have h := theta_ev_E bk
  rw [hQ, map_add, map_mul, map_pow, map_natCast, bk.ev_X, map_add, map_mul, map_pow, map_natCast] at h
  have h1 : IsUnit (Per.θ l (WittVector.teichmuller l bk.flat) ^ bk.Ep.natDegree) :=
    ((hu.map (WittVector.teichmuller l)).map (Per.θ l)).pow _
  rw [eq_neg_of_add_eq_zero_left h, IsUnit.neg_iff] at h1
  exact OC_l_not_unit l (isUnit_of_mul_isUnit_left h1)

theorem rho_spec (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by
    rw [neg_lt_zero]; positivity), ?_⟩
  rw [BK.ρ₀, ← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he.ne', NNReal.rpow_neg_one]

theorem J_eq (bk : BK K) :
    Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S) ^ bk.Ep.natDegree} = bk.J := by
  obtain ⟨Q, hQ⟩ := exists_E_eq bk
  have hl : (l : bk.S) * (Q : bk.S) ∈ Ideal.span {(l : bk.S)} := Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  · rw [Ideal.span_singleton_le_iff_mem]
    have : (X : bk.S) ^ bk.Ep.natDegree = bk.E - (l : bk.S) * (Q : bk.S) := by rw [hQ]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hl)
  · rw [Ideal.span_singleton_le_iff_mem, hQ]
    exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) (Ideal.mem_sup_left hl)

end GlobalTheory.BSP.FlatDisc

theorem GlobalTheory.BSP.flat_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), bk.flat ≠ 0 ∧ ¬ IsUnit bk.flat ∧
    (0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹) ∧
    Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S) ^ bk.Ep.natDegree} = bk.J :=
  fun _ _ _ bk => ⟨FlatDisc.flat_ne_zero bk, FlatDisc.not_isUnit_flat bk, FlatDisc.rho_spec bk, FlatDisc.J_eq bk⟩
