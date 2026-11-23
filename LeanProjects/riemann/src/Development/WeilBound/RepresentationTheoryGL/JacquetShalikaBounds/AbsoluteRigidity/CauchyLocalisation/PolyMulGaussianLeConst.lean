import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc

noncomputable section

open scoped ComplexConjugate
open Classical

namespace PositivityTheory.RgJS.CauchySplitting

section Gen

variable {ι L : Type} [Zero L]

def Φ (F : ι → L → ℂ) (l : ι →₀ L) : ℂ := ∏ w ∈ l.support, F w (l w)

theorem Φ_eq (F : ι → L → ℂ) (h0 : ∀ w, F w 0 = 1) (l : ι →₀ L) (T : Finset ι) (hT : l.support ⊆ T) :
    Φ F l = ∏ w ∈ T, F w (l w) := by
  unfold Φ
  refine Finset.prod_subset hT fun w _ hw => ?_
  rw [Finsupp.notMem_support_iff.1 hw, h0]

def splitE (a : ι) (T : Finset ι) (ha : a ∉ T) :
    {l : ι →₀ L // l.support ⊆ insert a T} ≃ {l : ι →₀ L // l.support ⊆ T} × L where
  toFun l := (⟨l.1.erase a, fun w hw => by
      rw [Finsupp.support_erase, Finset.mem_erase] at hw
      exact (Finset.mem_insert.1 (l.2 hw.2)).resolve_left hw.1⟩, l.1 a)
  invFun p := ⟨p.1.1.update a p.2, fun w hw => by
      rw [Finsupp.mem_support_iff, Finsupp.update_apply] at hw
      by_cases h : w = a
      · exact Finset.mem_insert.2 (Or.inl h)
      · rw [if_neg h] at hw
        exact Finset.mem_insert.2 (Or.inr (p.1.2 (Finsupp.mem_support_iff.2 hw)))⟩
  left_inv l := Subtype.ext (by
    ext w
    by_cases h : w = a
    · subst h; simp [Finsupp.update_apply]
    · simp [Finsupp.update_apply, Finsupp.erase_apply, h])
  right_inv p := by
    have hpa : p.1.1 a = 0 := Finsupp.notMem_support_iff.1 fun h => ha (p.1.2 h)
    refine Prod.ext (Subtype.ext ?_) ?_
    · ext w
      by_cases h : w = a
      · subst h; simp [Finsupp.erase_apply, hpa]
      · simp [Finsupp.update_apply, Finsupp.erase_apply, h]
    · simp [Finsupp.update_apply]

theorem Φ_split (F : ι → L → ℂ) (h0 : ∀ w, F w 0 = 1) (a : ι) (T : Finset ι) (ha : a ∉ T)
    (l : {l : ι →₀ L // l.support ⊆ insert a T}) :
    Φ F l.1 = Φ F (splitE a T ha l).1.1 * F a (splitE a T ha l).2 := by
  rw [Φ_eq F h0 l.1 _ l.2, Φ_eq F h0 _ T (splitE a T ha l).1.2, Finset.prod_insert ha, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  have hwa : w ≠ a := fun e => ha (e ▸ hw)
  simp [splitE, Finsupp.erase_apply, hwa]

variable (F : ι → L → ℂ) (h0 : ∀ w, F w 0 = 1) (hs : ∀ w, Summable fun l => ‖F w l‖)
include h0 hs

theorem fin (T : Finset ι) :
    Summable (fun l : {l : ι →₀ L // l.support ⊆ T} => ‖Φ F l.1‖) ∧
    HasSum (fun l : {l : ι →₀ L // l.support ⊆ T} => Φ F l.1) (∏ w ∈ T, ∑' l, F w l) ∧
    HasSum (fun l : {l : ι →₀ L // l.support ⊆ T} => ‖Φ F l.1‖) (∏ w ∈ T, ∑' l, ‖F w l‖) := by
  induction T using Finset.induction_on with
  | empty =>
    have hu : ∀ l : {l : ι →₀ L // l.support ⊆ ∅}, l.1 = 0 := fun l =>
      Finsupp.support_eq_empty.1 (Finset.subset_empty.1 l.2)
    haveI : Unique {l : ι →₀ L // l.support ⊆ ∅} := ⟨⟨⟨0, by simp⟩⟩, fun l => Subtype.ext (hu l)⟩
    have hΦ : ∀ l : {l : ι →₀ L // l.support ⊆ ∅}, Φ F l.1 = 1 := fun l => by rw [hu l]; simp [Φ]
    have e1 := hasSum_unique (fun l : {l : ι →₀ L // l.support ⊆ ∅} => Φ F l.1)
    have e2 := hasSum_unique (fun l : {l : ι →₀ L // l.support ⊆ ∅} => ‖Φ F l.1‖)
    rw [hΦ] at e1
    rw [hΦ, norm_one] at e2
    simp only [Finset.prod_empty]
    exact ⟨e2.summable, e1, e2⟩
  | insert a T ha ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    let e := splitE (L := L) a T ha
    have hp1 : Summable fun p : {l : ι →₀ L // l.support ⊆ T} × L => Φ F p.1.1 * F a p.2 :=
      summable_mul_of_summable_norm (f := fun l : {l : ι →₀ L // l.support ⊆ T} => Φ F l.1) (g := F a) ih1 (hs a)
    have hH := ih2.mul (hs a).of_norm.hasSum hp1
    have hp2 : Summable fun p : {l : ι →₀ L // l.support ⊆ T} × L => ‖Φ F p.1.1‖ * ‖F a p.2‖ :=
      summable_mul_of_summable_norm (f := fun l : {l : ι →₀ L // l.support ⊆ T} => ‖Φ F l.1‖)
        (g := fun x => ‖F a x‖) (by simp only [norm_norm]; exact ih1) (by simp only [norm_norm]; exact hs a)
    have hH' := ih3.mul (hs a).hasSum hp2
    have k1 : HasSum (fun l : {l : ι →₀ L // l.support ⊆ insert a T} => Φ F l.1)
        ((∏ w ∈ T, ∑' l, F w l) * ∑' l, F a l) := by
      have := (e.hasSum_iff (f := fun p : {l : ι →₀ L // l.support ⊆ T} × L => Φ F p.1.1 * F a p.2)).2 hH
      convert this using 1
      funext l
      exact Φ_split F h0 a T ha l
    have k2 : HasSum (fun l : {l : ι →₀ L // l.support ⊆ insert a T} => ‖Φ F l.1‖)
        ((∏ w ∈ T, ∑' l, ‖F w l‖) * ∑' l, ‖F a l‖) := by
      have := (e.hasSum_iff (f := fun p : {l : ι →₀ L // l.support ⊆ T} × L => ‖Φ F p.1.1‖ * ‖F a p.2‖)).2 hH'
      convert this using 1
      funext l
      simp only [Function.comp_apply]
      rw [Φ_split F h0 a T ha l, norm_mul]
    rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_comm (∑' l, F a l), mul_comm (∑' l, ‖F a l‖)]
    exact ⟨k2.summable, k1, k2⟩

theorem main (ht : Summable fun w => (∑' l, ‖F w l‖) - 1) :
    Summable (fun l : ι →₀ L => ‖Φ F l‖) ∧ HasSum (fun l : ι →₀ L => Φ F l) (∏' w, ∑' l, F w l) := by
  set c := Real.exp (∑' w, ((∑' l, ‖F w l‖) - 1)) with hc
  have hge : ∀ w, 1 ≤ ∑' l, ‖F w l‖ := fun w => by
    have := (hs w).le_tsum 0 (fun _ _ => norm_nonneg _)
    rwa [h0, norm_one] at this
  have hprod : ∀ T : Finset ι, ∏ w ∈ T, ∑' l, ‖F w l‖ ≤ c := fun T => by
    calc ∏ w ∈ T, ∑' l, ‖F w l‖ ≤ ∏ w ∈ T, Real.exp ((∑' l, ‖F w l‖) - 1) :=
          Finset.prod_le_prod (fun w _ => by linarith [hge w])
            (fun w _ => by linarith [Real.add_one_le_exp ((∑' l, ‖F w l‖) - 1)])
      _ = Real.exp (∑ w ∈ T, ((∑' l, ‖F w l‖) - 1)) := (Real.exp_sum _ _).symm
      _ ≤ c := Real.exp_le_exp.2 (ht.sum_le_tsum T (fun w _ => by linarith [hge w]))
  have hN : Summable (fun l : ι →₀ L => ‖Φ F l‖) := by
    refine summable_of_sum_le (c := c) (fun l => norm_nonneg _) fun u => ?_
    set T := u.biUnion fun l => l.support
    have hsub : ∀ l ∈ u, l.support ⊆ T := fun l hl => Finset.subset_biUnion_of_mem (fun l => l.support) hl
    obtain ⟨h1, -, h3⟩ := fin F h0 hs T
    calc ∑ l ∈ u, ‖Φ F l‖ = ∑ l ∈ u.subtype (fun l => l.support ⊆ T), ‖Φ F l.1‖ :=
          (Finset.sum_subtype_of_mem (fun l => ‖Φ F l‖) hsub).symm
      _ ≤ ∑' l : {l : ι →₀ L // l.support ⊆ T}, ‖Φ F l.1‖ := h1.sum_le_tsum _ (fun _ _ => norm_nonneg _)
      _ = ∏ w ∈ T, ∑' l, ‖F w l‖ := h3.tsum_eq
      _ ≤ c := hprod T
  have hS : Summable (fun l : ι →₀ L => Φ F l) := hN.of_norm
  refine ⟨hN, ?_⟩
  have hP : HasProd (fun w => ∑' l, F w l) (∑' l, Φ F l) := by
    change Filter.Tendsto (fun s : Finset ι => ∏ b ∈ s, ∑' l, F b l) Filter.atTop _
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨u, hu⟩ : ∃ u : Finset (ι →₀ L), ∑' l : {l // l ∉ u}, ‖Φ F l‖ < ε :=
      ((tendsto_tsum_compl_atTop_zero (fun l : ι →₀ L => ‖Φ F l‖)).eventually (gt_mem_nhds hε)).exists
    refine ⟨u.biUnion (·.support), fun T hT => ?_⟩
    obtain ⟨-, h2, -⟩ := fin F h0 hs T
    rw [dist_eq_norm, ← h2.tsum_eq, ← hS.tsum_subtype_add_tsum_subtype_compl {l | l.support ⊆ T},
      show (∑' b : {l : ι →₀ L // l.support ⊆ T}, Φ F b) = ∑' x : ↑{l : ι →₀ L | l.support ⊆ T}, Φ F x from rfl,
      sub_add_cancel_left, norm_neg]
    refine lt_of_le_of_lt ((norm_tsum_le_tsum_norm (hN.subtype _)).trans ?_) hu
    refine (hN.subtype _).tsum_le_tsum_of_inj (fun l => (⟨l.1, fun h => l.2 ?_⟩ : {l // l ∉ u}))
      (fun x y h => Subtype.ext (congrArg Subtype.val h : _)) (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hN.subtype _)
    exact (Finset.subset_biUnion_of_mem (·.support) h).trans hT
  rw [hP.tprod_eq]
  exact hS.hasSum

end Gen

theorem poly_mul_gaussian_le_const (N : ℕ) (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    ((1 - x)⁻¹) ^ N - 1 ≤ (2 * N * 2 ^ N) * x := by
  have hx1 : 0 < 1 - x := by linarith
  set a := (1 - x)⁻¹ with ha
  have ha1 : 1 ≤ a := by rw [ha]; exact one_le_inv₀ hx1 |>.2 (by linarith)
  have ha2 : a ≤ 2 := by rw [ha, inv_le_comm₀ hx1 (by norm_num)]; linarith
  have hax : a - 1 ≤ 2 * x := by
    have e : a - 1 = x / (1 - x) := by rw [ha]; field_simp; ring
    rw [e, div_le_iff₀ hx1]
    nlinarith
  have hg : a ^ N - 1 = (∑ i ∈ Finset.range N, a ^ i) * (a - 1) := (geom_sum_mul a N).symm
  have hs : ∑ i ∈ Finset.range N, a ^ i ≤ N * 2 ^ N := by
    calc ∑ i ∈ Finset.range N, a ^ i ≤ ∑ _i ∈ Finset.range N, (2 : ℝ) ^ N :=
          Finset.sum_le_sum fun i hi => (pow_le_pow_left₀ (by linarith) ha2 i).trans
            (pow_le_pow_right₀ (by norm_num) (Finset.mem_range.1 hi).le)
      _ = N * 2 ^ N := by simp
  rw [hg]
  calc _ ≤ (N * 2 ^ N) * (2 * x) :=
        mul_le_mul hs hax (by linarith) (by positivity)
    _ = _ := by ring

end PositivityTheory.RgJS.CauchySplitting

namespace PositivityTheory.RgJS

open CauchySplitting

theorem cauchy_of_local_prime : CauchyLoc → PrimeOff → CAUCHY := by
  intro hC hP E _ _ S m k α β s hkm hα hβ hs
  have hq := hP E S
  set F : Off E S → (Fin k → ℤ) → ℂ := fun w l => loc (nq w) (α w) (β w) s l with hF
  have hloc := fun w : Off E S => hC m k (nq w) (α w) (β w) s hkm (hq.two w) (hα w) (hβ w) (by linarith)
  set σ := s.re with hσ
  have hx : ∀ w : Off E S, 0 ≤ (nq w : ℝ) ^ (1 - σ) ∧ (nq w : ℝ) ^ (1 - σ) ≤ 1 / 2 := fun w => by
    have h2 : (2 : ℝ) ≤ nq w := by exact_mod_cast hq.two w
    refine ⟨Real.rpow_nonneg (by linarith) _, ?_⟩
    calc (nq w : ℝ) ^ (1 - σ) ≤ (nq w : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (nq w : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h2
  have hge : ∀ w, 1 ≤ ∑' l, ‖F w l‖ := fun w => by
    have := (hloc w).2.2.1.le_tsum 0 (fun _ _ => norm_nonneg _)
    rwa [(hloc w).1, norm_one] at this
  have ht : Summable fun w => (∑' l, ‖F w l‖) - 1 := by
    refine Summable.of_nonneg_of_le (fun w => by linarith [hge w]) (fun w => ?_)
      ((hq.conv (σ - 1) (by linarith)).mul_left (2 * ((m * m : ℕ) : ℝ) * 2 ^ (m * m)))
    have e : (nq w : ℝ) ^ (-(σ - 1)) = (nq w : ℝ) ^ (1 - σ) := by congr 1; ring
    rw [e]
    exact (sub_le_sub_right (hloc w).2.2.2 1).trans (poly_mul_gaussian_le_const (m * m) _ (hx w).1 (hx w).2)
  obtain ⟨h1, h2⟩ := main F (fun w => (hloc w).1) (fun w => (hloc w).2.2.1) ht
  refine ⟨h1, ?_⟩
  have e : LS S α β s = ∏' w, ∑' l, F w l := by
    unfold LS eul
    congr 1
    funext w
    exact ((hloc w).2.1.tsum_eq).symm
  rw [e]
  exact h2

end PositivityTheory.RgJS
