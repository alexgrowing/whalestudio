import Mathlib
import ReciprocityTheory.SemistableReduction.ShareDetA
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnQuotientOfDifferentiableOnSlice
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Filter Metric Set
open scoped Topology

namespace GlobalTheory.ThetaFamily

theorem exists_quotient_closure {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] {W : Set (V × V')}
    {f θ : V × V' → ℂ} (hW : IsOpen W) (hf : DifferentiableOn ℂ f W) (hθ : DifferentiableOn ℂ θ W) {S : Set V}
    (hS : ∀ b ∈ S, ∃ F : V' → ℂ, DifferentiableOn ℂ F {z | (b, z) ∈ W} ∧ ∀ z, (b, z) ∈ W → F z * θ (b, z) = f (b, z))
    {w : V × V'} (hw : w ∈ W) (hfr : ∃ᶠ z in 𝓝 w.2, θ (w.1, z) ≠ 0) :
    ∃ (U : Set (V × V')) (G : V × V' → ℂ), IsOpen U ∧ w ∈ U ∧ U ⊆ W ∧ DifferentiableOn ℂ G U ∧
      ∀ y ∈ U, y.1 ∈ closure S → G y * θ y = f y := by
  obtain ⟨v, r, hr, hin, hne⟩ := exists_circle_ne_zero_of_frequently_ne_zero
    (S := {z | (w.1, z) ∈ W}) (g := fun z => θ (w.1, z)) (z₀ := w.2)
    ((hW.preimage (f := fun z => (w.1, z)) (by fun_prop)).mem_nhds hw)
    (hθ.comp (f := fun z => (w.1, z)) (by fun_prop) fun z hz => hz) hfr
  let p : V × V' → ℂ → V × V' := fun y t => (y.1, y.2 + t • v)
  have hp : Continuous fun q : (V × V') × ℂ => p q.1 q.2 := by fun_prop
  have h1 : ∀ᶠ y in 𝓝 w, ∀ t ∈ closedBall (0 : ℂ) r, p y t ∈ W :=
    (isCompact_closedBall (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht =>
      hp.continuousAt.eventually (hW.mem_nhds (hin t ht))
  have h2 : ∀ᶠ y in 𝓝 w, ∀ t ∈ sphere (0 : ℂ) r, θ (p y t) ≠ 0 :=
    (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht => by
      have hc : ContinuousAt θ (p w t) :=
        (hθ.differentiableAt (hW.mem_nhds (hin t (sphere_subset_closedBall ht)))).continuousAt
      exact (ContinuousAt.comp (g := θ) (f := fun q : (V × V') × ℂ => p q.1 q.2) (x := (w, t))
        hc hp.continuousAt).eventually_ne (hne t ht)
  obtain ⟨U, hU, hUo, hwU⟩ := _root_.eventually_nhds_iff.1 (h1.and h2)
  have hp0 : ∀ y, p y 0 = y := fun y => by simp [p]
  have hUW : U ⊆ W := fun y hy => hp0 y ▸ (hU y hy).1 0 (mem_closedBall_self hr.le)
  have hcm : ∀ s : ℝ, circleMap 0 r s ∈ sphere (0 : ℂ) r := fun s =>
    circleMap_mem_sphere 0 hr.le s
  have hG := (differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
    (F := fun (s : ℝ) (y : V × V') => f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)))
    (a := 0) (b := 2 * Real.pi) hUo ?_ ?_).1
  · obtain ⟨G, hGd, hEq⟩ : ∃ G : V × V' → ℂ, DifferentiableOn ℂ G U ∧ ∀ y ∈ U, y.1 ∈ S → G y * θ y = f y := by
      refine ⟨fun y => ((2 * Real.pi)⁻¹ : ℝ) • ∫ s in (0 : ℝ)..2 * Real.pi,
        f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)), hG.const_smul ((2 * Real.pi)⁻¹ : ℝ), fun y hy hyS => ?_⟩
      obtain ⟨F, hFd, hF⟩ := hS _ hyS
      have hd : DifferentiableOn ℂ (fun t : ℂ => F (y.2 + t • v)) (closedBall 0 r) :=
        hFd.comp (f := fun t : ℂ => y.2 + t • v) (by fun_prop) fun t ht => (hU y hy).1 t ht
      have hdc : DiffContOnCl ℂ (fun t : ℂ => F (y.2 + t • v)) (ball 0 |r|) := by
        apply DifferentiableOn.diffContOnCl
        rwa [abs_of_pos hr, closure_ball _ hr.ne']
      have hav := hdc.circleAverage
      rw [Real.circleAverage_def, zero_smul, add_zero] at hav
      rw [← hF y.2 (hUW hy), ← hav]
      beta_reduce
      congr 2
      refine intervalIntegral.integral_congr fun s _ => ?_
      have hs := hcm s
      show _ / _ = _
      rw [div_eq_iff ((hU y hy).2 _ hs)]
      exact (hF _ ((hU y hy).1 _ (sphere_subset_closedBall hs))).symm
    refine ⟨U, G, hUo, hwU, hUW, hGd, fun y hy hyS => ?_⟩
    have hc : Continuous fun b : V => (b, y.2) := by fun_prop
    have c1 : ContinuousAt (fun b : V => G (b, y.2) * θ (b, y.2)) y.1 :=
      ContinuousAt.comp (g := fun q => G q * θ q) (f := fun b : V => (b, y.2)) (x := y.1)
        ((hGd.mul (hθ.mono hUW)).differentiableAt (hUo.mem_nhds hy)).continuousAt hc.continuousAt
    have c2 : ContinuousAt (fun b : V => f (b, y.2)) y.1 :=
      ContinuousAt.comp (g := f) (f := fun b : V => (b, y.2)) (x := y.1)
        (hf.differentiableAt (hW.mem_nhds (hUW hy))).continuousAt hc.continuousAt
    have hev : ∀ᶠ b in 𝓝 y.1, (b, y.2) ∈ U := hc.continuousAt.eventually (hUo.mem_nhds hy)
    exact tendsto_nhds_unique_of_frequently_eq c1 c2
      (((mem_closure_iff_frequently.1 hyS).and_eventually hev).mono fun b hb => hEq _ hb.2 hb.1)
  · have hq : Continuous fun q : ℝ × (V × V') => p q.2 (circleMap 0 r q.1) :=
      hp.comp (f := fun q : ℝ × (V × V') => (q.2, circleMap 0 r q.1)) (by fun_prop)
    have hm : ∀ q : ℝ × (V × V'), q ∈ uIcc 0 (2 * Real.pi) ×ˢ U →
        p q.2 (circleMap 0 r q.1) ∈ W := fun q hq =>
      (hU _ hq.2).1 _ (sphere_subset_closedBall (hcm _))
    exact (hf.continuousOn.comp hq.continuousOn hm).div
      (hθ.continuousOn.comp hq.continuousOn hm) fun q hq => (hU _ hq.2).2 _ (hcm _)
  · intro s _
    have hq : Differentiable ℂ fun y : V × V' => p y (circleMap 0 r s) := by fun_prop
    have hm : ∀ y ∈ U, p y (circleMap 0 r s) ∈ W := fun y hy =>
      (hU _ hy).1 _ (sphere_subset_closedBall (hcm _))
    simp only [div_eq_mul_inv]
    exact (hf.comp hq.differentiableOn hm).mul
      ((hθ.comp hq.differentiableOn hm).inv fun y hy => (hU _ hy).2 _ (hcm _))

theorem exists_entire_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {θ θ' : E → ℂ}
    (hfr : ∀ z, ∃ᶠ w in 𝓝 z, θ' w ≠ 0)
    (h : ∀ z, ∃ ρ : E → ℂ, ρ z ≠ 0 ∧ ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ρ w ∧ ρ w * θ' w = θ w) :
    ∃ ρ : E → ℂ, Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ∀ z, ρ z * θ' z = θ z := by
  choose ρ h0 h using h
  refine ⟨fun z => ρ z z, fun z => ?_, h0, fun z => (h z).self_of_nhds.2⟩
  refine (h z).self_of_nhds.1.congr_of_eventuallyEq ?_
  filter_upwards [(h z).eventually_nhds] with w hw
  refine tendsto_nhds_unique_of_frequently_eq (h w).self_of_nhds.1.continuousAt hw.self_of_nhds.1.continuousAt ?_
  exact (((hfr w).and_eventually (h w)).and_eventually hw).mono fun u hu =>
    mul_right_cancel₀ hu.1.1 (hu.1.2.2.trans hu.2.2.symm)

theorem eq_of_finite_of_closed_fibres {X Y : Type*} [TopologicalSpace X] {B : Set X} (hB : IsPreconnected B)
    {C : Set Y} (hC : C.Finite) (c : X → Y) (hc : ∀ b ∈ B, c b ∈ C)
    (h : ∀ k ∈ C, ∀ b ∈ B, b ∈ closure {b' ∈ B | c b' = k} → c b = k) : ∀ b ∈ B, ∀ b' ∈ B, c b = c b' := by
  have : PreconnectedSpace B := Subtype.preconnectedSpace hB
  have hl : IsLocallyConstant fun b : B => c b := fun s => by
    have e : ((fun b : B => c b) ⁻¹' s)ᶜ = ⋃ k ∈ C \ s, (Subtype.val ⁻¹' closure {b' ∈ B | c b' = k} : Set B) := by
      ext b
      simp only [mem_compl_iff, mem_preimage, mem_iUnion, mem_diff, exists_prop]
      exact ⟨fun hb => ⟨c b, ⟨hc b b.2, hb⟩, subset_closure ⟨b.2, rfl⟩⟩,
        fun ⟨k, hk, hb⟩ => (h k hk.1 b b.2 hb).symm ▸ hk.2⟩
    rw [← isClosed_compl_iff, e]
    exact (hC.subset diff_subset).isClosed_biUnion fun k _ => isClosed_closure.preimage continuous_subtype_val
  exact fun b hb b' hb' => hl.apply_eq_of_preconnectedSpace ⟨b, hb⟩ ⟨b', hb'⟩

theorem frequently_ne_zero_of_entire {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {θ : E → ℂ} (hd : Differentiable ℂ θ) (h0 : θ ≠ 0) (z : E) : ∃ᶠ w in 𝓝 z, θ w ≠ 0 := by
  intro h
  refine h0 (funext fun w => ?_)
  exact (SCV.analyticOnNhd_of_differentiable hd univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ z) (h.mono fun _ hu => not_not.1 hu) (mem_univ w)

theorem differentiableOn_left_inverse {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : Type} [Fintype n]
    [DecidableEq n] {B : Set V} {M h : V → Matrix n n ℂ} (hM : ∀ i j, DifferentiableOn ℂ (fun b => M b i j) B)
    (hh : ∀ b ∈ B, h b * M b = 1) (i j : n) : DifferentiableOn ℂ (fun b => h b i j) B := by
  have hdet : ∀ {N : V → Matrix n n ℂ}, (∀ i j, DifferentiableOn ℂ (fun b => N b i j) B) →
      DifferentiableOn ℂ (fun b => (N b).det) B := fun {N} hN => by
    exact ReciprocityTheory.MultiplicativeHeights.differentiableOn_det_of (F := fun i j b => N b i j) hN
  have hne : ∀ b ∈ B, (M b).det ≠ 0 := fun b hb => (Matrix.isUnit_det_of_left_inverse (hh b hb)).ne_zero
  refine (((hdet hM).inv hne).mul (hdet (N := fun b => (M b).updateRow j (Pi.single i 1)) fun k l => ?_)).congr
    fun b hb => ?_
  · by_cases hk : k = j
    · simp only [hk, Matrix.updateRow_self]; exact differentiableOn_const _
    · simp only [Matrix.updateRow_ne hk]; exact hM k l
  · rw [← Matrix.inv_eq_left_inv (hh b hb), Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply,
      Ring.inverse_eq_inv', smul_eq_mul]
    rfl

end GlobalTheory.ThetaFamily
