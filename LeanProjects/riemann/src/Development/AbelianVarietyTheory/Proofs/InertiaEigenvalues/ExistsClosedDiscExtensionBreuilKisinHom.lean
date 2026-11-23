import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscPrism

variable {l : ℕ} [hl : Fact l.Prime]

theorem breuilKisinDatum_radius_pow_degree_eq_inv {K : FinExt l} (bk : BK K) : bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  have he : (bk.Ep.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.2 bk.deg_pos.ne'
  unfold BK.ρ₀
  rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he, NNReal.rpow_neg_one]

theorem breuilKisinDatum_radius_le_one {K : FinExt l} (bk : BK K) : bk.ρ₀ ≤ 1 := by
  unfold BK.ρ₀
  exact NNReal.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hl.out.one_lt.le)
    (neg_nonpos.2 (by positivity))

theorem breuilKisinDatum_radius_pos {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ := by
  unfold BK.ρ₀
  exact NNReal.rpow_pos (by exact_mod_cast hl.out.pos)

theorem inv_le_rho {K : FinExt l} (bk : BK K) {ρ : ℝ≥0} (h : bk.ρ₀ ≤ ρ) : (l : ℝ≥0)⁻¹ ≤ ρ := by
  rw [← breuilKisinDatum_radius_pow_degree_eq_inv]
  exact (pow_le_of_le_one (by positivity) (breuilKisinDatum_radius_le_one bk) bk.deg_pos.ne').trans h

theorem E_eq {K : FinExt l} (bk : BK K) : ∃ q : bk.S, bk.E = X ^ bk.Ep.natDegree + (l : bk.S) * q := by
  have hm : bk.Ep - Polynomial.X ^ bk.Ep.natDegree ∈ (Ideal.span {(l : Wq l bk.a)}).map Polynomial.C := by
    rw [Ideal.mem_map_C_iff]
    intro n
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy n bk.Ep.natDegree with hn | hn | hn
    · rw [if_neg hn.ne, sub_zero]
      exact Ideal.mem_span_singleton.2 (bk.dvd_coeff n hn)
    · subst hn
      rw [if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact zero_mem _
    · rw [if_neg hn.ne', Polynomial.coeff_eq_zero_of_natDegree_lt hn, sub_zero]; exact zero_mem _
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hm
  obtain ⟨q, hq⟩ := hm
  refine ⟨(q : bk.S), ?_⟩
  have h1 : bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q := by
    rw [← hq]; ring
  have h2 : (bk.Ep : bk.S) =
      ((Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q : Polynomial (Wq l bk.a)) : bk.S) :=
    congrArg _ h1
  show (bk.Ep : bk.S) = _
  rw [h2, Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C, map_natCast]

theorem gauge_mono_le {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (a b : ℕ) {r : ℝ} (hr : 0 < r)
    (h : (ρ : ℝ) ^ b ≤ r * (l : ℝ) ^ a) :
    ‖algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b)‖ ≤ r :=
  gauge_le l u ρ hr (Submodule.subset_span ⟨a, b, 0, by simpa using h, by simp⟩)

end GlobalTheory.BSP.DiscPrism

namespace GlobalTheory.BSP.DiscPrism

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_toDisc_hf_le {K : FinExt l} (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ρ : ℝ≥0)
    (h0 : bk.ρ₀ ≤ ρ) (h1 : ρ ≤ 1) : ‖toDisc l (BK.hf f X) ρ (BK.hf g X)‖ ≤ ρ := by
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.2 ((breuilKisinDatum_radius_pos bk).trans_le h0)
  have hρ1 : (ρ : ℝ) ≤ 1 := by exact_mod_cast h1
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hlρ : (1 : ℝ) ≤ ρ * l := by
    have h := inv_le_rho bk h0
    have h' : ((l : ℝ))⁻¹ ≤ ρ := by exact_mod_cast h
    rw [inv_le_iff_one_le_mul₀ hl0] at h'
    linarith [mul_comm (l : ℝ) ρ]
  set u := BK.hf f X with hu
  let am := algebraMap B.A (PreDisc l u ρ)
  have um : ∀ x y : PreDisc l u ρ, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := gauge_add_le_max l u ρ
  have hX : ‖am u‖ ≤ ρ := by
    simpa using gauge_mono_le (l := l) u ρ 0 1 hρ (by simp)
  have hE : ‖am (BK.hf f bk.E)‖ ≤ ρ := by
    obtain ⟨q, hq⟩ := E_eq bk
    have e1 : BK.hf f bk.E = u ^ bk.Ep.natDegree + (l : B.A) ^ 1 * u ^ 0 * BK.hf f q := by
      rw [hq, map_add, map_pow, map_mul, map_natCast, hu]; ring
    rw [e1, map_add, map_mul]
    refine (um _ _).trans (max_le ?_ ?_)
    · have := gauge_mono_le (l := l) u ρ 0 bk.Ep.natDegree hρ
        (by simpa using pow_le_of_le_one hρ.le hρ1 bk.deg_pos.ne')
      simpa using this
    · refine (norm_mul_le _ _).trans ?_
      have h2 := gauge_mono_le (l := l) u ρ 1 0 hρ (by simpa using hlρ)
      have h3 := norm_algebraMap_le (l := l) (u := u) (ρ := ρ) (BK.hf f q)
      calc _ ≤ (ρ : ℝ) * 1 := mul_le_mul h2 h3 (norm_nonneg _) hρ.le
        _ = ρ := mul_one _
  have hmem : BK.hf g X - BK.hf f X ∈ B.I := by
    have hs : Ideal.Quotient.mk bk.prism.I (X : bk.S) = bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ X)) :=
      (bk.str.apply_symm_apply _).symm
    exact Ideal.Quotient.eq.1 ((g.f_str _ _ hs).trans (f.f_str _ _ hs).symm)
  have hI : B.I = Ideal.span {BK.hf f bk.E} := by
    rw [← GlobalTheory.T.prism_hom_map_ideal_eq l ↥(OL K) bk.prism B f]
    show (Ideal.span {bk.E}).map (BK.hf f) = _
    rw [Ideal.map_span, Set.image_singleton]
  rw [hI, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have e2 : BK.hf g X = u + BK.hf f bk.E * c := by rw [← hc, hu]; ring
  show ‖ofPre l u ρ (am (BK.hf g X))‖ ≤ ρ
  rw [norm_ofPre, ← norm_preDisc, e2, map_add, map_mul]
  refine (um _ _).trans (max_le hX ?_)
  refine (norm_mul_le _ _).trans ?_
  calc _ ≤ (ρ : ℝ) * 1 := mul_le_mul hE (norm_algebraMap_le _) (norm_nonneg _) hρ.le
    _ = ρ := mul_one _

theorem disc_map_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ (B : Obj l ↥(OL K))
    (f g : Hom bk.prism B) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ ≤ 1 →
    ∃ F : bk.DS ρ →+* Disc l (BK.hf f X) ρ, IsDiscMap (BK.hf g) F := by
  intro l _ K bk B f g ρ h0 h1
  exact ⟨Disc.map (BK.hf g) (norm_toDisc_hf_le bk B f g ρ h0 h1), isDiscMap_map _ _⟩

end GlobalTheory.BSP.DiscPrism
