import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormLeOfDistinct
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeriesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEllipticFunctionMulProdEqXyStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartHatCoeffBoundsStatement

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TransNorm

variable {q : ℕ} [Fact q.Prime]

lemma bd_add {f g : ℂ_[q]⟦X⟧} {B : ℝ} (hf : Bd B f) (hg : Bd B g) : Bd B (f + g) := by
  simpa using ((sup_norm_laws q).1 f g B B hf hg).1

lemma bd_mul_one {f g : ℂ_[q]⟦X⟧} {B : ℝ} (hf : Bd B f) (hg : Bd 1 g) : Bd B (f * g) := by
  simpa using ((sup_norm_laws q).1 f g B 1 hf hg).2

lemma bd_C {a : ℂ_[q]} {B : ℝ} (ha : ‖a‖ ≤ B) : Bd B (C a : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact ha
  · simpa using (norm_nonneg a).trans ha

lemma bd_one : Bd 1 (1 : ℂ_[q]⟦X⟧) := by
  simpa using (bd_C (a := (1 : ℂ_[q])) (B := 1) (by simp))

lemma bd_X : Bd 1 (X : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_X]
  split_ifs <;> simp

lemma bd_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (n : ℕ) : Bd 1 (f ^ n) := by
  induction n with
  | zero => simpa using bd_one
  | succ n ih => rw [pow_succ]; exact bd_mul_one ih hf

lemma bd_sum {α : Type} (s : Finset α) (f : α → ℂ_[q]⟦X⟧) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, Bd B (f i)) : Bd B (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (Bd B) (fun _ _ => bd_add) ?_ hf
  intro n
  simpa using hB

lemma bd_prod {α : Type} (s : Finset α) (f : α → ℂ_[q]⟦X⟧)
    (hf : ∀ i ∈ s, Bd 1 (f i)) : Bd 1 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (Bd 1) (fun _ _ => bd_mul_one) bd_one hf

lemma bd_sub_C {f : ℂ_[q]⟦X⟧} {a : ℂ_[q]} (hf : Bd 1 f) (ha : ‖a‖ ≤ 1) : Bd 1 (f - C a) := by
  have := bd_add hf (bd_C (a := -a) (by simpa using ha))
  simpa [sub_eq_add_neg] using this

lemma bd_cancel {f g : ℂ_[q]⟦X⟧} {B : ℝ} (hf : Bdd f) (hg : Bd 1 g)
    (hg' : ∀ r : ℝ, r < 1 → ∃ n, r < ‖coeff n g‖) (h : Bd B (f * g)) : Bd B f := by
  intro i
  have key := (sup_norm_laws q).2.2.2.1 f g B hf ⟨1, hg⟩ h i
  by_contra hlt
  push Not at hlt
  have hB : 0 ≤ B := (norm_nonneg _).trans (h 0)
  have hpos : 0 < ‖coeff i f‖ := hB.trans_lt hlt
  obtain ⟨n, hn⟩ := hg' (B / ‖coeff i f‖) ((div_lt_one hpos).2 hlt)
  have := key n
  rw [div_lt_iff₀ hpos] at hn
  nlinarith

lemma bd_cancel_prod {α : Type} (s : Finset α) (g : α → ℂ_[q]⟦X⟧) {B : ℝ}
    (hg : ∀ i, Bd 1 (g i)) (hg' : ∀ i, ∀ r : ℝ, r < 1 → ∃ n, r < ‖coeff n (g i)‖)
    {f : ℂ_[q]⟦X⟧} (hf : Bdd f) (h : Bd B (f * ∏ i ∈ s, g i)) : Bd B f := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert a s ha ih =>
    apply ih
    rw [Finset.prod_insert ha, mul_comm (g a), ← mul_assoc] at h
    obtain ⟨C, hC⟩ := hf
    exact bd_cancel ⟨C, bd_mul_one hC (bd_prod s g fun i _ => hg i)⟩ (hg a) (hg' a) h

lemma analyticAt_eval (p : Polynomial ℂ) {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) :
    AnalyticAt ℂ (fun z => p.eval (F z)) z := by
  simp only [Polynomial.eval_eq_sum_range]
  exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul (hF.pow i)

lemma hat_eval (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hℓ : constantCoeff ℓ = 0) (p : Polynomial ℂ)
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    hat ι ℓ (fun z => p.eval (F z)) =
      p.eval₂ ((C : ℂ_[q] →+* ℂ_[q]⟦X⟧).comp (ι : ℂ →+* ℂ_[q])) (hat ι ℓ F) := by
  obtain ⟨h1, h2, -⟩ := TaylorRead.hat_laws q ι ℓ hℓ
  induction p using Polynomial.induction_on with
  | C a => simpa using h2 a
  | add p r hp hr =>
    simp only [Polynomial.eval_add, Polynomial.eval₂_add]
    rw [(h1 _ _ (analyticAt_eval p hF) (analyticAt_eval r hF)).1, hp, hr]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc]
    simp only [Polynomial.eval_mul (q := Polynomial.X), Polynomial.eval_X, Polynomial.eval₂_mul_X]
    rw [(h1 _ _ (analyticAt_eval _ hF) hF).2.1, ih]

lemma bd_eval₂ (ι : ℂ ≃+* ℂ_[q]) (p : Polynomial ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hp : ∀ i ≤ p.natDegree, ‖ι (p.coeff i)‖ ≤ B) {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) :
    Bd B (p.eval₂ ((C : ℂ_[q] →+* ℂ_[q]⟦X⟧).comp (ι : ℂ →+* ℂ_[q])) f) := by
  rw [Polynomial.eval₂_eq_sum_range]
  refine bd_sum _ _ hB fun i hi => bd_mul_one (bd_C ?_) (bd_pow hf i)
  exact hp i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

lemma norm_coeff_prod (ι : ℂ ≃+* ℂ_[q]) {m : ℕ} (a : Fin m → ℂ) (ha : ∀ i, ‖ι (a i)‖ ≤ 1) (n : ℕ) :
    ‖ι ((∏ i, (Polynomial.X - Polynomial.C (a i))).coeff n)‖ ≤ 1 := by
  have h : Bd 1 (∏ i, (X - C (ι (a i)) : ℂ_[q]⟦X⟧)) :=
    bd_prod _ _ fun i _ => bd_sub_C bd_X (ha i)
  have e : (∏ i, (X - C (ι (a i)) : ℂ_[q]⟦X⟧)) =
      Polynomial.coeToPowerSeries.ringHom
        ((∏ i, (Polynomial.X - Polynomial.C (a i))).map (ι : ℂ →+* ℂ_[q])) := by
    simp [Polynomial.map_prod, map_prod]
  have := h n
  rw [e] at this
  simpa only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, Polynomial.coeff_map, RingHom.coe_coe] using this

lemma analyticAt_x_of_not_mem_lattice (M : Mdl q) {t : ℂ} (ht : t ∉ M.L.lattice) : AnalyticAt ℂ M.x t := by
  have := M.L.analyticOnNhd_weierstrassP t ht
  unfold Mdl.x
  fun_prop

lemma analyticAt_y (M : Mdl q) {t : ℂ} (ht : t ∉ M.L.lattice) : AnalyticAt ℂ M.y t := by
  have := M.L.analyticOnNhd_derivWeierstrassP t ht
  have := analyticAt_x_of_not_mem_lattice M ht
  unfold Mdl.y
  fun_prop

lemma analyticAt_shift {F : ℂ → ℂ} {t : ℂ} (hF : AnalyticAt ℂ F t) :
    AnalyticAt ℂ (fun z => F (z + t)) 0 :=
  AnalyticAt.comp_of_eq (g := F) (f := fun z => z + t) hF (by fun_prop) (by simp)

theorem translate_norm_le : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ) (t : ℂ) (B : ℝ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → AnalyticAt ℂ φ t → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → ¬ M.Small t → Bdd (hat M.ι ℓ (fun z => φ (z + t))) → Bd B (hat M.ι ℓ φ) → Bd B (hat M.ι ℓ (fun z => φ (z + t))) := by
  intro q _ M ℓ φ t B hc hE h0 ht hpole hts hbdd hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hℓ := hc.2.1
  obtain ⟨hl1, hl2, -⟩ := TaylorRead.hat_laws q M.ι ℓ hℓ
  obtain ⟨m, P, A, B', hP, hid⟩ := GlobalTheory.T.exists_ellipticFunction_mul_prod_eq_xy q M φ hc.1 hE
  have hPx : ∀ i, ‖M.ι (M.x (P i))‖ ≤ 1 := fun i =>
    not_lt.1 fun h => hpole _ (hP i).2 (Or.inr h)
  obtain ⟨-, v, xs, ys, -, hxs, hys, -, hxs0, hys0, -, -, -, hread⟩ := GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M ℓ hc
  set D : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hD
  set k := max A.natDegree B'.natDegree with hk
  have e0 := hread φ A B' k h0 (le_max_left _ _) (le_max_right _ _) (fun _ => 1) analyticAt_const
    D D.natDegree le_rfl (by simpa only [one_mul] using hid 0)
  have hS : Bd B (∑ i ∈ Finset.range (k + 1),
      (C (M.ι (A.coeff i)) * X ^ (2 * (k - i) + 3) * xs ^ i +
        C (M.ι (B'.coeff i)) * X ^ (2 * (k - i)) * xs ^ i * ys)) := by
    refine (sup_norm_laws q).2.2.2.2.2 _ 1 (2 * D.natDegree) B bd_one (by simp) ?_
    rw [hl2, map_one, map_one, one_mul] at e0
    rw [mul_one, ← e0]
    refine bd_mul_one (bd_mul_one hB (bd_pow bd_X _)) (bd_sum _ _ zero_le_one fun i _ => ?_)
    exact bd_mul_one (bd_mul_one (bd_C (norm_coeff_prod M.ι _ hPx i)) (bd_pow bd_X _)) (bd_pow hxs _)
  have hco := Triang.coeff_norm_le q xs ys k (fun i => M.ι (A.coeff i)) (fun i => M.ι (B'.coeff i)) B
    hxs hys hxs0 hys0 hS
  obtain ⟨hxt, hyt, hbig⟩ := GlobalTheory.T.chart_hat_coeff_bounds q M ℓ t hc hts
  have htl : t ∉ M.L.lattice := fun h => hts (Or.inl h)
  have ax := analyticAt_shift (analyticAt_x_of_not_mem_lattice M htl)
  have ay := analyticAt_shift (analyticAt_y M htl)
  have aφ := analyticAt_shift ht
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), φ (z + t) * D.eval (M.x (z + t)) =
      A.eval (M.x (z + t)) + B'.eval (M.x (z + t)) * M.y (z + t) := by
    have tt : Filter.Tendsto (fun z : ℂ => z + t) (𝓝[≠] 0) (𝓝[≠] t) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Filter.Tendsto (fun z : ℂ => z + t) (𝓝 0) (𝓝 (0 + t)) :=
          (continuous_id.add continuous_const).tendsto 0
        rw [zero_add] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa using hz
    exact tt.eventually (hid t)
  have e1 := (hl1 _ _ (aφ.mul (analyticAt_eval D ax))
    ((analyticAt_eval A ax).add ((analyticAt_eval B' ax).mul ay))).2.2.1 hev
  have e2 := (hl1 _ _ aφ (analyticAt_eval D ax)).2.1
  have e3 := (hl1 _ _ (analyticAt_eval A ax) ((analyticAt_eval B' ax).mul ay)).1
  have e4 := (hl1 _ _ (analyticAt_eval B' ax) ay).2.1
  have e5 : hat M.ι ℓ (fun z => φ (z + t)) * hat M.ι ℓ (fun z => D.eval (M.x (z + t))) =
      hat M.ι ℓ (fun z => A.eval (M.x (z + t))) +
        hat M.ι ℓ (fun z => B'.eval (M.x (z + t))) * hat M.ι ℓ (fun z => M.y (z + t)) := by
    rw [← e2, ← e4]
    exact e1.trans e3
  rw [hat_eval _ _ hℓ D ax, hat_eval _ _ hℓ A ax, hat_eval _ _ hℓ B' ax] at e5
  have e6 : D.eval₂ ((C : ℂ_[q] →+* ℂ_[q]⟦X⟧).comp (M.ι : ℂ →+* ℂ_[q]))
      (hat M.ι ℓ (fun z => M.x (z + t))) =
      ∏ i, (hat M.ι ℓ (fun z => M.x (z + t)) - C (M.ι (M.x (P i)))) := by
    rw [hD, Polynomial.eval₂_finsetProd]
    simp
  rw [e6] at e5
  refine bd_cancel_prod Finset.univ _ (fun i => bd_sub_C hxt (hPx i)) (fun i r hr => ?_) hbdd ?_
  · obtain ⟨n, hn, hn'⟩ := hbig r hr
    refine ⟨n, ?_⟩
    rwa [map_sub, coeff_C, if_neg hn.ne', sub_zero]
  · rw [e5]
    exact bd_add (bd_eval₂ _ _ hB0 (fun i hi => (hco i (hi.trans (le_max_left _ _))).1) hxt)
      (bd_mul_one (bd_eval₂ _ _ hB0 (fun i hi => (hco i (hi.trans (le_max_right _ _))).2) hxt) hyt)

end GlobalTheory.MomOne.TransNorm
