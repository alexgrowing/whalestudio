import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

namespace GlobalTheory.HTLevelSq

theorem mem_latHT_iff_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → ∀ (N : ℕ) (c : Fin N → TorsChar t x (p ^ 2)) (h : Fin N → Fin g → ↥(intO ℂ_[p])), (∀ c' : TorsChar t x (p ^ 2), ∃ j, Agree c' (c j)) → (∀ j, DlogIs t p 2 (c j) e (h j)) → ∀ (a : Fin g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left), IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) a w → (w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) ↔ ∀ j, ‖∑ i, (h j i : ℂ_[p]) * a i‖ ≤ 1) ∧ (w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) → ∀ i, ‖(p : ℂ_[p]) * a i‖ ≤ 1) := by
  intro E _ _ _ H X _ t hX p hp x g e he N c h hAll hdl
  have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := PadicComplexHost.norm_p p
  have hx : ∀ x' : Sp ↥(intO ℂ_[p]) ⟶ X,
      spMap (intO ℂ_[p]).subtype ≫ x' = spMap (intO ℂ_[p]).subtype ≫ x → x' = x :=
    fun x' h' => GlobalTheory.LineNorm.WedgeMax.ext_intO hX x x' h'
  have hc1 : ∀ c₁ : TorsChar t x (p ^ 1), ∃ j, DlogIs t p 1 c₁ e (h j) := fun c₁ => by
    obtain ⟨c', hc'⟩ := GlobalTheory.T.torsionChar_extends_divisible_level E H X t ℂ_[p] x (p ^ 1) (p ^ 2) (pow_ne_zero _ hp.out.ne_zero)
      (pow_dvd_pow _ (by norm_num)) c₁
    obtain ⟨j, hj⟩ := hAll c'
    exact ⟨j, GlobalTheory.HTLevel.dlog_down (by norm_num) c' c₁ hc' he.1 (GlobalTheory.HTMap.dlog_congr he.1 hj (hdl j))⟩
  have hj1 : ∀ j, ∃ c₁ : TorsChar t x (p ^ 1), DlogIs t p 1 c₁ e (h j) := fun j =>
    ⟨GlobalTheory.HTLevel.res (pow_dvd_pow p (by norm_num : 1 ≤ 2)) (c j),
      GlobalTheory.HTLevel.dlog_down (by norm_num : 1 ≤ 2) (c j) (GlobalTheory.HTLevel.res (pow_dvd_pow p (by norm_num : 1 ≤ 2)) (c j))
        (fun _ _ _ _ _ _ => rfl) he.1 (hdl j)⟩
  have L1 := fun a w hw => GlobalTheory.HTLevel.mem_latHT_iff GlobalTheory.ShFam.Pad.HTBound.htBound E H X t p ℂ_[p] hn x hx g e he N h
    hc1 hj1 a w hw
  have heC := fun i => GlobalTheory.FactorDepth.isTanAtG_map t (intO ℂ_[p]).subtype (he.1 i)
  have step : ∀ (a : Fin g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left),
      IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) a w →
      (∀ j, ‖∑ i, (h j i : ℂ_[p]) * a i‖ ≤ 1) → (∀ i, ‖(p : ℂ_[p]) ^ 2 * a i‖ ≤ 1) →
      w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) := by
    intro a w hw h1 h2
    let b : Fin g → ↥(intO ℂ_[p]) := fun i => ⟨(p : ℂ_[p]) ^ 2 * a i, h2 i⟩
    obtain ⟨vO, hv, hbv⟩ := Guard.exists_comb he.1 b
    refine ⟨x, rfl, 2, vO, hv, ?_, fun k c₀ w' hw' => ?_⟩
    · exact Guard.comb_unique heC (GlobalTheory.LatDRFree.comb_map t (intO ℂ_[p]).subtype hbv) (Guard.comb_smul heC hw _)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : Subsingleton (↥(intO ℂ_[p]) ⧸ Ideal.span {(p : ↥(intO ℂ_[p])) ^ 0}) := by
        rw [Ideal.Quotient.subsingleton_iff, pow_zero, Ideal.span_singleton_one]
      rw [Subsingleton.elim (TrivSqZeroExt.snd _) 0]
      exact Ideal.zero_mem _
    obtain ⟨j, D, hD, hδ⟩ : ∃ j, ∃ D : Fin g → ↥(intO ℂ_[p]), DlogIs t p k c₀ e D ∧
        ∀ i, D i - h j i ∈ Ideal.span {(p : ↥(intO ℂ_[p])) ^ 2} := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · obtain rfl : k = 1 := by omega
        obtain ⟨j, hj⟩ := hc1 c₀
        exact ⟨j, h j, hj, fun i => by simp⟩
      · obtain ⟨⟨D, hD⟩, -⟩ := GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x p k c₀ g e he.1
        obtain ⟨j, hj⟩ := hAll (GlobalTheory.HTLevel.res (pow_dvd_pow p hk2) c₀)
        exact ⟨j, D, hD, (GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x p 2 _ g e he.1).2 D (h j)
          (GlobalTheory.HTLevel.dlog_down hk2 c₀ (GlobalTheory.HTLevel.res (pow_dvd_pow p hk2) c₀) (fun _ _ _ _ _ _ => rfl) he.1 hD) (GlobalTheory.HTMap.dlog_congr he.1 hj (hdl j))⟩
    choose δ hδ using fun i => Ideal.mem_span_singleton'.1 (hδ i)
    let s : ↥(intO ℂ_[p]) := ⟨∑ i, (h j i : ℂ_[p]) * a i, h1 j⟩
    have h3 : ∑ i, D i * b i = (s + ∑ i, δ i * b i) * (p : ↥(intO ℂ_[p])) ^ 2 := by
      apply (intO ℂ_[p]).subtype_injective
      simp only [map_mul, map_pow, map_natCast, map_sum, map_add, Subring.subtype_apply, s, b]
      rw [← Finset.sum_add_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrArg (intO ℂ_[p]).subtype (hδ i)
      simp only [map_mul, map_pow, map_natCast, map_sub, Subring.subtype_apply] at this
      linear_combination (-(p : ℂ_[p]) ^ 2 * a i) * this
    rw [hD b vO hbv w' hw', h3, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  intro a w hw
  refine ⟨⟨fun hL => ((L1 a w hw).1 hL).1, fun hd => ?_⟩, fun hL => ((L1 a w hw).1 hL).2⟩
  by_cases hbig : ∀ i, ‖(p : ℂ_[p]) ^ 2 * a i‖ ≤ 1
  · exact step a w hw hd hbig
  exfalso
  push_neg at hbig
  obtain ⟨i₀, hi₀⟩ := hbig
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖a i‖) ⟨i₀, Finset.mem_univ _⟩
  have hai : 1 < ‖(p : ℂ_[p]) ^ 2 * a i‖ := by
    refine lt_of_lt_of_le hi₀ ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hi i₀ (Finset.mem_univ _)) (norm_nonneg _)
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have ha0 : a i ≠ 0 := fun h0 => by rw [h0, mul_zero, norm_zero] at hai; linarith
  have hl1 : ‖((p : ℂ_[p]) ^ 2 * a i)⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hai.le
  have hlw := Guard.comb_smul heC hw ((p : ℂ_[p]) ^ 2 * a i)⁻¹
  have hd' : ∀ j, ‖∑ k, (h j k : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k)‖ ≤ 1 := fun j => by
    have e2 : ∑ k, (h j k : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k) =
        ((p : ℂ_[p]) ^ 2 * a i)⁻¹ * ∑ k, (h j k : ℂ_[p]) * a k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [e2, norm_mul]
    exact mul_le_one₀ hl1 (norm_nonneg _) (hd j)
  have hb' : ∀ k, ‖(p : ℂ_[p]) ^ 2 * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k)‖ ≤ 1 := fun k => by
    have e3 : (p : ℂ_[p]) ^ 2 * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k) = a k / a i := by field_simp
    rw [e3, norm_div]
    exact div_le_one_of_le₀ (hi k (Finset.mem_univ _)) (norm_nonneg _)
  have hmem := step _ _ hlw hd' hb'
  have h4 := ((L1 _ _ hlw).1 hmem).2 i
  have e1 : (p : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a i) = (p : ℂ_[p])⁻¹ := by field_simp
  rw [e1, norm_inv, hn, inv_inv] at h4
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  linarith

end GlobalTheory.HTLevelSq
