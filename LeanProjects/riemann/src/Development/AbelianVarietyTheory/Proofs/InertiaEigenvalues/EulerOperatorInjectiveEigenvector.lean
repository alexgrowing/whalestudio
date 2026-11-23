import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableFinprodOfFiniteSupportEulerSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdOneSubBoundedBelowOfSummableStatement
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem eulerOp_Zbound : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (Z : ι → (H →L[ℂ] H)), (∀ v, a v (x0 v) = 1) → (∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, ‖a v x‖ ≤ s v) → (∀ f, ‖B f‖ ≤ 1) → B x0 = 1 → (∀ v (f : ∀ v, X v), {w | f w ≠ x0 w}.Finite → f v = x0 v → HasSum (fun x => a v x • B (Function.update f v x)) (B f * Z v)) → ∀ v, ‖Z v - 1‖ ≤ s v := by
  intro ι _ X x0 H _ _ _ a s B Z ha0 hC hB hB0 hZ v
  classical
  have h := hZ v x0 (by simp) rfl
  rw [hB0, one_mul] at h
  have ht0 : a v (x0 v) • B (Function.update x0 v (x0 v)) = 1 := by simp [ha0, hB0]
  have h2 := h.update (x0 v) 0
  rw [ht0] at h2
  let g : X v → ℝ := fun x => if x = x0 v then 0 else ‖a v x‖
  have hg0 : 0 ≤ g := fun x => by simp only [g]; split_ifs <;> simp
  have hgsum : ∀ u : Finset (X v), ∑ x ∈ u, g x ≤ s v := by
    intro u
    have e : ∑ x ∈ u, g x = ∑ x ∈ u.filter (fun x => ¬ x = x0 v), ‖a v x‖ := by
      simp only [g]; rw [Finset.sum_ite]; simp
    rw [e]; exact hC v _ (by simp)
  have hgs : Summable g := summable_of_sum_le hg0 hgsum
  have h3 := h2.norm_le_of_bounded hgs.hasSum (fun x => ?_)
  · calc ‖Z v - 1‖ = ‖0 - 1 + Z v‖ := by congr 1; abel
      _ ≤ ∑' x, g x := h3
      _ ≤ s v := hgs.tsum_le_of_sum_le hgsum
  · by_cases hx : x = x0 v
    · rw [hx]; simp [g]
    · rw [Function.update_of_ne hx]
      simp only [g, if_neg hx, norm_smul]
      exact (mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)).trans (by simp)

theorem eulerOp_rec : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (Z : ι → (H →L[ℂ] H)), (∀ v, a v (x0 v) = 1) → (∀ v (f : ∀ v, X v), {w | f w ≠ x0 w}.Finite → f v = x0 v → HasSum (fun x => a v x • B (Function.update f v x)) (B f * Z v)) → Summable (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ u, a u (f.1 u)) • B f.1) → ∀ (S : Finset ι) (v : ι), v ∉ S → HasSum (fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} => (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) ((∑' f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ S, f.1 w = x0 w}, (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) * Z v) := by
  intro ι _ X x0 H _ _ _ a s B Z ha0 hZ hsum S v hv
  classical
  have hprod : ∀ (T : Finset ι) (f : ∀ v, X v), (∀ w ∉ T, f w = x0 w) →
      (∏ᶠ u, a u (f u)) = ∏ u ∈ T, a u (f u) := by
    intro T f hf
    apply finprod_eq_prod_of_mulSupport_subset
    intro w hw
    rw [Function.mem_mulSupport] at hw
    by_contra h
    exact hw (by rw [hf w h, ha0])
  have hfinU : ∀ (g : ∀ v, X v) (x : X v), {w | g w ≠ x0 w}.Finite →
      {w | Function.update g v x w ≠ x0 w}.Finite := by
    intro g x hg
    apply (hg.insert v).subset
    intro w hw
    by_cases h : w = v
    · exact Or.inl h
    · right; simpa [Function.update_of_ne h] using hw
  let e : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ S, f.1 w = x0 w} × X v →
      {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} :=
    fun p => ⟨⟨Function.update p.1.1.1 v p.2, hfinU _ _ p.1.1.2⟩, fun w hw => by
      have h1 : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self _ _)
      have h2 : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
      simp only [Function.update_of_ne h1]; exact p.1.2 w h2⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨g, x⟩ ⟨g', x'⟩ h
      have h' : Function.update g.1.1 v x = Function.update g'.1.1 v x' :=
        congrArg (fun f => f.1.1) h
      have hx : x = x' := by simpa using congrFun h' v
      subst hx
      have hg : g.1.1 = g'.1.1 := by
        funext w
        by_cases hw : w = v
        · rw [hw, g.2 v hv, g'.2 v hv]
        · simpa [Function.update_of_ne hw] using congrFun h' w
      exact Prod.ext (Subtype.ext (Subtype.ext hg)) rfl
    · intro f
      refine ⟨(⟨⟨Function.update f.1.1 v (x0 v), hfinU _ _ f.1.2⟩, fun w hw => ?_⟩, f.1.1 v), ?_⟩
      · show Function.update f.1.1 v (x0 v) w = x0 w
        by_cases h : w = v
        · rw [h]; simp
        · rw [Function.update_of_ne h]; exact f.2 w (by simp [h, hw])
      · apply Subtype.ext; apply Subtype.ext; simp [e]
  have hsumI : Summable (fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} =>
      (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) :=
    hsum.comp_injective (f := fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ u, a u (f.1 u)) • B f.1) Subtype.val_injective
  have hsumS : Summable (fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ S, f.1 w = x0 w} =>
      (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) :=
    hsum.comp_injective (f := fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ u, a u (f.1 u)) • B f.1) Subtype.val_injective
  have hall := (Equiv.ofBijective e he).hasSum_iff.mpr hsumI.hasSum
  have hfib : ∀ g : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ S, f.1 w = x0 w},
      HasSum (fun x => ((fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} =>
        (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) ∘ (Equiv.ofBijective e he)) (g, x))
        (((∏ᶠ u, a u (g.1.1 u)) • B g.1.1) * Z v) := by
    intro g
    have hgv : g.1.1 v = x0 v := g.2 v hv
    have key : ∀ x, ((fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} =>
        (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) ∘ (Equiv.ofBijective e he)) (g, x) =
        (∏ᶠ u, a u (g.1.1 u)) • (a v x • B (Function.update g.1.1 v x)) := by
      intro x
      simp only [Function.comp, Equiv.ofBijective_apply, e]
      rw [smul_smul, hprod (insert v S) _ ?_, hprod S _ g.2, Finset.prod_insert hv]
      · congr 1
        rw [Function.update_self, mul_comm]
        congr 1
        apply Finset.prod_congr rfl
        intro w hw
        rw [Function.update_of_ne (by rintro rfl; exact hv hw)]
      · intro w hw
        have h1 : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self _ _)
        have h2 : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
        rw [Function.update_of_ne h1]; exact g.2 w h2
    simp_rw [key]
    rw [smul_mul_assoc]
    exact (hZ v g.1.1 g.1.2 hgv).const_smul _
  have h3 := hall.prod_fiberwise hfib
  have h4 := hsumS.hasSum.mul_right (Z v)
  rw [← h3.unique h4]
  exact hsumI.hasSum

theorem eulerOp_normSummable (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (ha0 : ∀ v, a v (x0 v) = 1) (hs : Summable s) (hC : ∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, ‖a v x‖ ≤ s v) (hB : ∀ f, ‖B f‖ ≤ 1) :
    Summable (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => ‖(∏ᶠ v, a v (f.1 v)) • B f.1‖) := by
  have h1 := GlobalTheory.T.summable_finprod_of_finite_support_euler_sum ι X x0 (fun v x => ‖a v x‖) s (fun v x => norm_nonneg _) (by intro v; simp [ha0]) hs hC
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun f => ?_) h1
  rw [norm_smul]
  have hfin := f.2
  have e1 : (∏ᶠ v, a v (f.1 v)) = ∏ v ∈ hfin.toFinset, a v (f.1 v) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro w hw
    rw [Function.mem_mulSupport] at hw
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h; exact hw (by simp [h, ha0])
  have e2 : (∏ᶠ v, ‖a v (f.1 v)‖) = ∏ v ∈ hfin.toFinset, ‖a v (f.1 v)‖ := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro w hw
    rw [Function.mem_mulSupport] at hw
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h; exact hw (by simp [h, ha0])
  rw [e1, e2, norm_prod]
  calc (∏ v ∈ hfin.toFinset, ‖a v (f.1 v)‖) * ‖B f.1‖ ≤ (∏ v ∈ hfin.toFinset, ‖a v (f.1 v)‖) * 1 :=
        mul_le_mul_of_nonneg_left (hB _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = _ := mul_one _

theorem eulerOp_injective_eigen : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (Z : ι → (H →L[ℂ] H)), (∀ v, a v (x0 v) = 1) → Summable s → (∀ v, s v < 1) → (∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, ‖a v x‖ ≤ s v) → (∀ f, ‖B f‖ ≤ 1) → B x0 = 1 → (∀ v (f : ∀ v, X v), {w | f w ≠ x0 w}.Finite → f v = x0 v → HasSum (fun x => a v x • B (Function.update f v x)) (B f * Z v)) → ∃ W : H →L[ℂ] H, HasSum (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ v, a v (f.1 v)) • B f.1) W ∧ Function.Injective W ∧ ∀ (y : H) (z : ι → ℂ), (∀ v, Z v y = z v • y) → W y = (∏' v, z v) • y := by
  intro ι _ X x0 H _ _ _ a s B Z ha0 hs hs1 hC hB hB0 hZ
  let t : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} → (H →L[ℂ] H) := fun f => (∏ᶠ v, a v (f.1 v)) • B f.1
  have hnorm : Summable (fun f => ‖t f‖) := eulerOp_normSummable ι X x0 H a s B ha0 hs hC hB
  have hsum : Summable t := hnorm.of_norm
  let A : Finset ι → Set {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} := fun S => {f | ∀ w ∉ S, f.1 w = x0 w}
  let WS : Finset ι → (H →L[ℂ] H) := fun S => ∑' f : A S, t f
  have hs0 : ∀ v, 0 ≤ s v := fun v => by simpa using hC v ∅ (by simp)
  have hZb := eulerOp_Zbound ι X x0 H a s B Z ha0 hC hB hB0 hZ
  have hrec : ∀ S v, v ∉ S → WS (insert v S) = WS S * Z v := fun S v hv =>
    (eulerOp_rec ι X x0 H a s B Z ha0 hZ hsum S v hv).tsum_eq
  have hbase : WS ∅ = 1 := by
    let f0 : A ∅ := ⟨⟨x0, by simp⟩, fun w _ => rfl⟩
    have hf0 : ∀ b : A ∅, b = f0 := fun b =>
      Subtype.ext (Subtype.ext (funext fun w => b.2 w (by simp)))
    show ∑' f : A ∅, t f = 1
    rw [tsum_eq_single f0 (fun b hb => absurd (hf0 b) hb)]
    simp [t, f0, ha0, hB0]
  have hlim : Tendsto WS atTop (𝓝 (∑' f, t f)) := by
    have e : WS = fun S => ∑' f, (A S).indicator t f := by
      funext S; exact tsum_subtype (A S) t
    rw [e]
    refine tendsto_tsum_of_dominated_convergence hnorm (fun f => ?_)
      (Eventually.of_forall fun S f => norm_indicator_le_norm_self _ _)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop f.2.toFinset] with S hS
    have hm : f ∈ A S := by
      intro w hw
      by_contra h
      exact hw (hS (by simpa using h))
    exact (Set.indicator_of_mem hm t).symm
  obtain ⟨δ, hδ, hδS⟩ := GlobalTheory.T.prod_one_sub_bounded_below_of_summable ι s hs0 hs1 hs
  have hlow : ∀ S : Finset ι, ∀ y, (∏ v ∈ S, (1 - s v)) * ‖y‖ ≤ ‖WS S y‖ := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro y; simp [hbase]
    | insert v S hv ih =>
      intro y
      rw [hrec S v hv, Finset.prod_insert hv, ContinuousLinearMap.mul_apply]
      have h1 : ‖(Z v - 1) y‖ ≤ s v * ‖y‖ :=
        ((Z v - 1).le_opNorm y).trans (mul_le_mul_of_nonneg_right (hZb v) (norm_nonneg _))
      have h2 : ‖y‖ ≤ ‖Z v y‖ + ‖(Z v - 1) y‖ := by
        calc ‖y‖ = ‖Z v y - (Z v - 1) y‖ := by simp
          _ ≤ _ := norm_sub_le _ _
      have hZy : (1 - s v) * ‖y‖ ≤ ‖Z v y‖ := by nlinarith
      have hP : 0 ≤ ∏ v ∈ S, (1 - s v) := Finset.prod_nonneg fun w _ => by linarith [hs1 w]
      calc (1 - s v) * (∏ v ∈ S, (1 - s v)) * ‖y‖ = (∏ v ∈ S, (1 - s v)) * ((1 - s v) * ‖y‖) := by ring
        _ ≤ (∏ v ∈ S, (1 - s v)) * ‖Z v y‖ := mul_le_mul_of_nonneg_left hZy hP
        _ ≤ _ := ih _
  have heig : ∀ S : Finset ι, ∀ y (z : ι → ℂ), (∀ v, Z v y = z v • y) → WS S y = (∏ v ∈ S, z v) • y := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro y z _; simp [hbase]
    | insert v S hv ih =>
      intro y z hyz
      rw [hrec S v hv, ContinuousLinearMap.mul_apply, hyz v, map_smul, ih y z hyz, Finset.prod_insert hv, smul_smul]
  have hWy : ∀ y, Tendsto (fun S => WS S y) atTop (𝓝 ((∑' f, t f) y)) := fun y =>
    ((ContinuousLinearMap.apply ℂ H y).continuous.tendsto _).comp hlim
  have hlowW : ∀ y, δ * ‖y‖ ≤ ‖(∑' f, t f) y‖ := fun y =>
    ge_of_tendsto (hWy y).norm (Eventually.of_forall fun S =>
      (mul_le_mul_of_nonneg_right (hδS S) (norm_nonneg y)).trans (hlow S y))
  refine ⟨∑' f, t f, hsum.hasSum, ?_, ?_⟩
  · intro y1 y2 h
    have h1 := hlowW (y1 - y2)
    rw [map_sub, h, sub_self, norm_zero] at h1
    have h2 : ‖y1 - y2‖ ≤ 0 := le_of_mul_le_mul_left (by rw [mul_zero]; exact h1) hδ
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  · intro y z hyz
    by_cases hy : y = 0
    · subst hy; simp
    obtain ⟨φ, -, hφ⟩ := exists_dual_vector ℂ y (norm_ne_zero_iff.mpr hy)
    have h1 : Tendsto (fun S => (∏ v ∈ S, z v) • y) atTop (𝓝 ((∑' f, t f) y)) :=
      Tendsto.congr (fun S => heig S y z hyz) (hWy y)
    have h2 : Tendsto (fun S => φ ((∏ v ∈ S, z v) • y)) atTop (𝓝 (φ ((∑' f, t f) y))) :=
      (φ.continuous.tendsto _).comp h1
    simp only [map_smul, hφ, smul_eq_mul] at h2
    have hy' : ((‖y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hy
    have h3 : Tendsto (fun S => ∏ v ∈ S, z v) atTop (𝓝 (φ ((∑' f, t f) y) / ‖y‖)) := by
      refine (h2.div_const ((‖y‖ : ℂ))).congr (fun S => ?_)
      exact mul_div_cancel_right₀ _ hy'
    have hP : HasProd z (φ ((∑' f, t f) y) / ‖y‖) := h3
    rw [hP.tprod_eq]
    exact tendsto_nhds_unique h1 (h3.smul_const y)

end GlobalTheory
