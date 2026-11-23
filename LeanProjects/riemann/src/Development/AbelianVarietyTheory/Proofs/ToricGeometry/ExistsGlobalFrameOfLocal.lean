import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.CubeFrame

theorem exists_glue {X J : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {U : Set X}
    {A : J → Set X} {F : J → X → ℂ} (hA : ∀ j, IsOpen (A j)) (hcov : ∀ x, ∃ j, x ∈ A j)
    (hF : ∀ j, DifferentiableOn ℂ (F j) (U ∩ A j))
    (hagree : ∀ j k x, x ∈ U → x ∈ A j → x ∈ A k → F j x = F k x) :
    ∃ G : X → ℂ, DifferentiableOn ℂ G U ∧ ∀ j x, x ∈ U → x ∈ A j → G x = F j x := by
  choose σ hσ using hcov
  have key : ∀ j x, x ∈ U → x ∈ A j → F (σ x) x = F j x :=
    fun j x hx hj => hagree _ _ x hx (hσ x) hj
  refine ⟨fun x => F (σ x) x, fun x hx => ?_, key⟩
  have h1 : DifferentiableWithinAt ℂ (fun y => F (σ y) y) (U ∩ A (σ x)) x :=
    ((hF (σ x)).congr fun y hy => key _ y hy.1 hy.2) x ⟨hx, hσ x⟩
  exact (differentiableWithinAt_inter ((hA _).mem_nhds (hσ x))).mp h1

theorem differentiableOn_prod_zpow {X α : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {U : Set X} (s : Finset α) {f : α → X → ℂ} (e : α → ℤ)
    (hf : ∀ a ∈ s, DifferentiableOn ℂ (f a) U) (h0 : ∀ a ∈ s, ∀ x ∈ U, f a x ≠ 0) :
    DifferentiableOn ℂ (fun x => ∏ a ∈ s, f a x ^ e a) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact ((hf a (Finset.mem_insert_self _ _)).zpow
      (Or.inl (h0 a (Finset.mem_insert_self _ _)))).mul
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
        fun b hb => h0 b (Finset.mem_insert_of_mem hb))

theorem differentiableOn_div {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {U : Set X} {f g : X → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (h0 : ∀ x ∈ U, g x ≠ 0) : DifferentiableOn ℂ (fun x => f x / g x) U := by
  simp only [div_eq_mul_inv]
  exact hf.mul (hg.inv h0)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {ι : Type} {W : ι → Set E} {c : ι → ι → E → ℂ}
  {T : (Finset (Fin 3) → ι) → (Fin 3 → E) → ℂ}

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
theorem isOpen_cubeChart {X : Type*} [TopologicalSpace X] {p : X → Fin 3 → E}
    (hp : Continuous p) {V : Finset (Fin 3) → Set E} (hV : ∀ I, IsOpen (V I)) :
    IsOpen {y | ∀ I : Finset (Fin 3), ∑ a ∈ I, p y a ∈ V I} := by
  rw [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun I => (hV I).preimage (by fun_prop)

theorem cube_eq_on_ball (hW : ∀ i, IsOpen (W i)) (hcov : ∀ z, ∃ i, z ∈ W i)
    (hc0 : ∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
    (hT : ∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))})
    (hTc : ∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) →
      T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
        T j' x)
    {r : ℝ} {fr : ι → E → ℂ} {κ : ℂ} (hr : 0 < r)
    (hfd : ∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r))
    (hf0 : ∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0)
    (hfc : ∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)
    (hev : ∀ᶠ x in 𝓝 (0 : Fin 3 → E), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) :
    ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ Metric.ball (0 : E) r) →
      T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card)) := by
  set U : Set (Fin 3 → E) := {x | ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ Metric.ball (0 : E) r}
    with hU
  have hUo : IsOpen U := isOpen_cubeChart (p := fun x => x) continuous_id fun _ => Metric.isOpen_ball
  have hUc : Convex ℝ U := by
    intro x hx y hy a b ha hb hab I
    have := convex_ball (0 : E) r (hx I) (hy I) ha hb hab
    simpa [Finset.sum_add_distrib, Finset.smul_sum] using this
  have hU0 : (0 : Fin 3 → E) ∈ U := fun I => by simpa using hr
  have hcov' : ∀ x : Fin 3 → E, ∃ j : Finset (Fin 3) → ι,
      x ∈ {x : Fin 3 → E | ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)} := fun x => by
    choose j hj using fun I : Finset (Fin 3) => hcov (∑ a ∈ I, x a)
    exact ⟨j, hj⟩
  have hne : ∀ (j : Finset (Fin 3) → ι) x, x ∈ U →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card)) ≠ 0 :=
    fun j x hx hj => Finset.prod_ne_zero_iff.mpr fun I _ => zpow_ne_zero _ (hf0 _ _ (hj I) (hx I))
  obtain ⟨G, hGd, hG⟩ := exists_glue (U := U)
    (A := fun j : Finset (Fin 3) → ι =>
      {x : Fin 3 → E | ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)})
    (F := fun j x => T j x /
      ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card)))
    (fun j => isOpen_cubeChart (p := fun x => x) continuous_id fun I => hW _) hcov'
    (fun j => by
      refine differentiableOn_div ((hT j).mono Set.inter_subset_right) ?_
        fun x hx => hne j x hx.1 hx.2
      refine differentiableOn_prod_zpow _ (f := fun I (x : Fin 3 → E) => fr (j I) (∑ a ∈ I, x a)) _
        (fun I _ => ?_) fun I _ x hx => hf0 _ _ (hx.2 I) (hx.1 I)
      exact (hfd (j I)).comp (by fun_prop) fun x hx => ⟨hx.2 I, hx.1 I⟩)
    (fun j k x hx hj hk => by
      have h1 : ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card)) =
          (∏ I : Finset (Fin 3), c (j I) (k I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
          ∏ I : Finset (Fin 3), fr (k I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card)) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun I _ => ?_
        rw [hfc _ _ _ (hj I) (hk I) (hx I), mul_zpow]
      have h2 : ∏ I : Finset (Fin 3), c (j I) (k I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))
          ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun I _ => zpow_ne_zero _ (hc0 _ _ _ (hj I) (hk I))
      rw [hTc j k x hj hk, h1, mul_div_mul_left _ _ h2])
  have hGκ : Set.EqOn G (fun _ => κ) U := by
    refine SCV.eqOn_of_eventuallyEq hUo hUc.isPreconnected hGd (differentiableOn_const κ) hU0 ?_
    filter_upwards [hev, hUo.mem_nhds hU0] with x hx hxU
    obtain ⟨j, hj⟩ := hcov' x
    rw [hG j x hxU hj, hx j hj, mul_div_cancel_right₀ _ (hne j x hxU hj)]
  intro j x hj hx
  have h1 := hGκ hx
  rw [hG j x hx hj] at h1
  exact (div_eq_iff (hne j x hx hj)).mp h1

noncomputable def halfPoint (w : E) : Fin 3 → E :=
  ![(2⁻¹ : ℂ) • w, (2⁻¹ : ℂ) • w, -((2⁻¹ : ℂ) • w)]

omit [FiniteDimensional ℂ E] in
theorem differentiable_halfPoint : Differentiable ℂ (halfPoint : E → Fin 3 → E) := by
  refine differentiable_pi.mpr fun a => ?_
  fin_cases a <;> simp [halfPoint] <;> fun_prop

omit [FiniteDimensional ℂ E] in
theorem sum_halfPoint (w : E) : ∑ a ∈ ({0, 1} : Finset (Fin 3)), halfPoint w a = w := by
  simp [halfPoint, ← add_smul]
  norm_num

omit [FiniteDimensional ℂ E] in
theorem norm_sum_halfPoint_le (w : E) {I : Finset (Fin 3)} (hI : I ≠ {0, 1}) :
    ‖∑ a ∈ I, halfPoint w a‖ ≤ ‖w‖ / 2 := by
  have h : ‖(2⁻¹ : ℂ) • w‖ = ‖w‖ / 2 := by
    rw [norm_smul]; simp; ring
  have h0 : (0 : ℝ) ≤ ‖w‖ / 2 := by positivity
  have hI' : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {2} ∨ I = {0, 2} ∨ I = {1, 2} ∨ I = {0, 1, 2} := by
    revert I
    decide
  rcases hI' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [halfPoint, h, h0]

theorem exists_double (hW : ∀ i, IsOpen (W i)) (hcov : ∀ z, ∃ i, z ∈ W i)
    (hcd : ∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j))
    (hc0 : ∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
    (hcc : ∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z)
    (hT : ∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))})
    (hT0 : ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0)
    (hTc : ∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) →
      T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
        T j' x)
    {r : ℝ} {fr : ι → E → ℂ} {κ : ℂ} (hr : 0 < r)
    (hfd : ∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r))
    (hf0 : ∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0)
    (hfc : ∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)
    (hall : ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ Metric.ball (0 : E) r) →
      T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) :
    ∃ fr' : ι → E → ℂ, (∀ i, DifferentiableOn ℂ (fr' i) (W i ∩ Metric.ball 0 (2 * r))) ∧
      (∀ i z, z ∈ W i → z ∈ Metric.ball 0 (2 * r) → fr' i z ≠ 0) ∧
      (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 (2 * r) → fr' i z = c i j z * fr' j z) ∧
      ∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr' i z = fr i z := by
  set D : Finset (Fin 3) := {0, 1} with hD
  set S : Finset (Finset (Fin 3)) := Finset.univ.erase D with hS
  have hκ : κ ≠ 0 := by
    obtain ⟨i, hi⟩ := hcov 0
    have h1 : ∀ I : Finset (Fin 3), ∑ a ∈ I, (0 : Fin 3 → E) a ∈ W ((fun _ => i) I) :=
      fun I => by simpa using hi
    have h2 := hT0 _ _ h1
    rw [hall _ _ h1 fun I => by simpa using hr] at h2
    exact left_ne_zero_of_mul h2
  have hcov' : ∀ w : E, ∃ j : Finset (Fin 3) → ι,
      w ∈ {w : E | ∀ I : Finset (Fin 3), ∑ a ∈ I, halfPoint w a ∈ W (j I)} := fun w => by
    choose j hj using fun I : Finset (Fin 3) => hcov (∑ a ∈ I, halfPoint w a)
    exact ⟨j, hj⟩
  have hball : ∀ w ∈ Metric.ball (0 : E) (2 * r), ∀ I ∈ S,
      ∑ a ∈ I, halfPoint w a ∈ Metric.ball (0 : E) r := fun w hw I hI => by
    rw [mem_ball_zero_iff] at hw ⊢
    have := norm_sum_halfPoint_le w (Finset.ne_of_mem_erase hI)
    linarith
  have hjD : ∀ (j : Finset (Fin 3) → ι) (w : E),
      (∀ I : Finset (Fin 3), ∑ a ∈ I, halfPoint w a ∈ W (j I)) → w ∈ W (j D) := fun j w hj => by
    have := hj D
    rwa [sum_halfPoint] at this
  have hsplit : ∀ (f : Finset (Fin 3) → E → ℂ) (w : E),
      ∏ I : Finset (Fin 3), f I (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card)) =
      (f D w)⁻¹ * ∏ I ∈ S, f I (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card)) := by
    intro f w
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ D), sum_halfPoint]
    have : D.card = 2 := rfl
    simp [this, hS]
  have hne : ∀ (j : Finset (Fin 3) → ι), ∀ w ∈ Metric.ball (0 : E) (2 * r),
      (∀ I : Finset (Fin 3), ∑ a ∈ I, halfPoint w a ∈ W (j I)) →
      ∏ I ∈ S, fr (j I) (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card)) ≠ 0 :=
    fun j w hw hj => Finset.prod_ne_zero_iff.mpr fun I hI =>
      zpow_ne_zero _ (hf0 _ _ (hj I) (hball w hw I hI))
  have hglue := fun i : ι => exists_glue (U := W i ∩ Metric.ball 0 (2 * r))
    (A := fun j : Finset (Fin 3) → ι =>
      {w : E | ∀ I : Finset (Fin 3), ∑ a ∈ I, halfPoint w a ∈ W (j I)})
    (F := fun j w => c i (j D) w * (κ *
      (∏ I ∈ S, fr (j I) (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card))) /
        T j (halfPoint w)))
    (fun j => isOpen_cubeChart differentiable_halfPoint.continuous fun I => hW _) hcov'
    (fun j => by
      have hp := differentiable_halfPoint (E := E)
      refine DifferentiableOn.mul ((hcd i (j D)).mono fun w hw => ⟨hw.1.1, hjD j w hw.2⟩)
        (differentiableOn_div (DifferentiableOn.const_mul ?_ κ) ?_ fun w hw => hT0 _ _ hw.2)
      · refine differentiableOn_prod_zpow _ (f := fun I w => fr (j I) (∑ a ∈ I, halfPoint w a)) _
          (fun I hI => ?_) fun I hI w hw => hf0 _ _ (hw.2 I) (hball w hw.1.2 I hI)
        exact (hfd (j I)).comp (by fun_prop) fun w hw => ⟨hw.2 I, hball w hw.1.2 I hI⟩
      · exact (hT j).comp hp.differentiableOn fun w hw => hw.2)
    (fun j k w hw hj hk => by
      have h1 : ∏ I ∈ S, fr (j I) (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card)) =
          (∏ I ∈ S, c (j I) (k I) (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
          ∏ I ∈ S, fr (k I) (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card)) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun I hI => ?_
        rw [hfc _ _ _ (hj I) (hk I) (hball w hw.2 I hI), mul_zpow]
      have h2 : ∏ I ∈ S, c (j I) (k I) (∑ a ∈ I, halfPoint w a) ^ ((-1 : ℤ) ^ (3 - I.card))
          ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun I _ => zpow_ne_zero _ (hc0 _ _ _ (hj I) (hk I))
      have h3 := hc0 _ _ _ (hjD j w hj) (hjD k w hk)
      have h4 := hT0 _ _ hk
      rw [hTc j k _ hj hk, h1, hsplit (fun I => c (j I) (k I)),
        ← hcc i (j D) (k D) w hw.1 (hjD j w hj) (hjD k w hk)]
      field_simp)
  choose fr' hd hfr' using hglue
  refine ⟨fr', hd, fun i z hi hz => ?_, fun i i' z hi hi' hz => ?_, fun i z hi hz => ?_⟩
  · obtain ⟨j, hj⟩ := hcov' z
    rw [hfr' i j z ⟨hi, hz⟩ hj]
    exact mul_ne_zero (hc0 _ _ _ hi (hjD j z hj))
      (div_ne_zero (mul_ne_zero hκ (hne j z hz hj)) (hT0 _ _ hj))
  · obtain ⟨j, hj⟩ := hcov' z
    rw [hfr' i j z ⟨hi, hz⟩ hj, hfr' i' j z ⟨hi', hz⟩ hj, ← mul_assoc,
      hcc i i' _ z hi hi' (hjD j z hj)]
  · obtain ⟨j, hj⟩ := hcov' z
    have hz2 : z ∈ Metric.ball (0 : E) (2 * r) := Metric.ball_subset_ball (by linarith) hz
    have hb : ∀ I : Finset (Fin 3), ∑ a ∈ I, halfPoint z a ∈ Metric.ball (0 : E) r := fun I => by
      by_cases hI : I = D
      · rw [hI, sum_halfPoint]; exact hz
      · exact hball z hz2 I (Finset.mem_erase.mpr ⟨hI, Finset.mem_univ I⟩)
    have h1 := hne j z hz2 hj
    have h2 := hf0 _ _ (hjD j z hj) hz
    rw [hfr' i j z ⟨hi, hz2⟩ hj, hall j _ hj hb, hsplit (fun I => fr (j I)),
      hfc i _ z hi (hjD j z hj) hz]
    field_simp

theorem exists_global_frame_of_local (hW : ∀ i, IsOpen (W i)) (hcov : ∀ z, ∃ i, z ∈ W i)
    (hcd : ∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j))
    (hc0 : ∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
    (hcc : ∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z)
    (hT : ∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))})
    (hT0 : ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0)
    (hTc : ∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) →
      T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
        T j' x)
    {r : ℝ} {fr : ι → E → ℂ} {κ : ℂ} (hr : 0 < r)
    (hfd : ∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r))
    (hf0 : ∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0)
    (hfc : ∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)
    (hev : ∀ᶠ x in 𝓝 (0 : Fin 3 → E), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) :
    ∃ fr' : ι → E → ℂ, (∀ i, DifferentiableOn ℂ (fr' i) (W i)) ∧
      (∀ i z, z ∈ W i → fr' i z ≠ 0) ∧
      (∀ i j z, z ∈ W i → z ∈ W j → fr' i z = c i j z * fr' j z) ∧
      (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr' i z = fr i z) ∧
      ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
        T j x = κ * ∏ I : Finset (Fin 3),
          fr' (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card)) := by
  let P : ℝ → (ι → E → ℂ) → Prop := fun ρ f =>
    (∀ i, DifferentiableOn ℂ (f i) (W i ∩ Metric.ball 0 ρ)) ∧
    (∀ i z, z ∈ W i → z ∈ Metric.ball 0 ρ → f i z ≠ 0) ∧
    (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 ρ → f i z = c i j z * f j z) ∧
    ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
      (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ Metric.ball (0 : E) ρ) →
      T j x = κ * ∏ I : Finset (Fin 3), f (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))
  have hP0 : P (2 ^ 0 * r) fr := by
    rw [pow_zero, one_mul]
    exact ⟨hfd, hf0, hfc, cube_eq_on_ball hW hcov hc0 hT hTc hr hfd hf0 hfc hev⟩
  have hstep : ∀ (n : ℕ) (f : {f // P (2 ^ n * r) f}), ∃ f' : {f // P (2 ^ (n + 1) * r) f},
      ∀ i z, z ∈ W i → z ∈ Metric.ball 0 (2 ^ n * r) → f'.1 i z = f.1 i z := by
    rintro n ⟨f, h1, h2, h3, h4⟩
    have hρ : 0 < 2 ^ n * r := by positivity
    obtain ⟨f', k1, k2, k3, k4⟩ := exists_double hW hcov hcd hc0 hcc hT hT0 hTc hρ h1 h2 h3 h4
    have e : (2 : ℝ) ^ (n + 1) * r = 2 * (2 ^ n * r) := by ring
    refine ⟨⟨f', ?_⟩, k4⟩
    rw [e]
    refine ⟨k1, k2, k3, cube_eq_on_ball hW hcov hc0 hT hTc (by positivity) k1 k2 k3 ?_⟩
    have ho : IsOpen {x : Fin 3 → E |
        ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ Metric.ball (0 : E) (2 ^ n * r)} :=
      isOpen_cubeChart (p := fun x => x) continuous_id fun _ => Metric.isOpen_ball
    filter_upwards [ho.mem_nhds (x := 0) fun I => by simpa using hρ] with x hx j hj
    rw [h4 j x hj hx]
    congr 1
    exact Finset.prod_congr rfl fun I _ => by rw [k4 _ _ (hj I) (hx I)]
  choose nxt hnxt using hstep
  let s : ∀ n : ℕ, {f // P (2 ^ n * r) f} := fun n => Nat.rec ⟨fr, hP0⟩ nxt n
  have hmono : ∀ {m n : ℕ}, m ≤ n →
      Metric.ball (0 : E) (2 ^ m * r) ⊆ Metric.ball 0 (2 ^ n * r) := fun h =>
    Metric.ball_subset_ball (by gcongr; norm_num)
  have hs : ∀ m n, m ≤ n → ∀ i z, z ∈ W i → z ∈ Metric.ball 0 (2 ^ m * r) →
      (s n).1 i z = (s m).1 i z := by
    intro m n hmn i z hi hz
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih => rw [← ih]; exact hnxt n (s n) i z hi (hmono hmn hz)
  have hbig : ∀ t : ℝ, ∃ n : ℕ, t < 2 ^ n * r := fun t => by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (t / r) (one_lt_two (α := ℝ))
    exact ⟨n, (div_lt_iff₀ hr).mp hn⟩
  have hcov' : ∀ z : E, ∃ n : ℕ, z ∈ Metric.ball (0 : E) (2 ^ n * r) := fun z => by
    simpa only [mem_ball_zero_iff] using hbig ‖z‖
  have hglue := fun i : ι => exists_glue (U := W i)
    (A := fun n : ℕ => Metric.ball (0 : E) (2 ^ n * r)) (F := fun n => (s n).1 i)
    (fun _ => Metric.isOpen_ball) hcov' (fun n => (s n).2.1 i)
    (fun m n z hi hm hn => by
      rcases le_total m n with h | h
      · exact (hs m n h i z hi hm).symm
      · exact hs n m h i z hi hn)
  choose fr' hd hfr' using hglue
  refine ⟨fr', hd, fun i z hi => ?_, fun i j z hi hj => ?_, fun i z hi hz => ?_, fun j x hj => ?_⟩
  · obtain ⟨n, hn⟩ := hcov' z
    rw [hfr' i n z hi hn]
    exact (s n).2.2.1 i z hi hn
  · obtain ⟨n, hn⟩ := hcov' z
    rw [hfr' i n z hi hn, hfr' j n z hj hn]
    exact (s n).2.2.2.1 i j z hi hj hn
  · exact hfr' i 0 z hi (by simpa using hz)
  · obtain ⟨n, hn⟩ := hbig (∑ a, ‖x a‖)
    have hb : ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ Metric.ball (0 : E) (2 ^ n * r) := fun I => by
      rw [mem_ball_zero_iff]
      exact ((norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ I) fun _ _ _ => norm_nonneg _)).trans_lt hn
    rw [(s n).2.2.2.2 j x hj hb]
    congr 1
    exact Finset.prod_congr rfl fun I _ => by rw [hfr' _ n _ (hj I) (hb I)]

theorem exists_global_frame :
    (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → (∃ (r : ℝ) (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), 0 < r ∧ ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r)) ∧ (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)) ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) → ∃ (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Set.univ)) ∧ (∀ i z, z ∈ W i → z ∈ Set.univ → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Set.univ → fr i z = c i j z * fr j z)) ∧ ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) := by
  rintro g ι W c hW hcov hcd hc0 hcc T hT hT0 hTc ⟨r, fr, κ, hr, ⟨hfd, hf0, hfc⟩, hev⟩
  obtain ⟨fr', h1, h2, h3, -, h5⟩ :=
    exists_global_frame_of_local hW hcov hcd hc0 hcc hT hT0 hTc hr hfd hf0 hfc hev
  exact ⟨fr', κ, ⟨fun i => (h1 i).mono Set.inter_subset_left, fun i z hi _ => h2 i z hi,
    fun i j z hi hj _ => h3 i j z hi hj⟩, h5⟩

end GlobalTheory.CubeFrame
