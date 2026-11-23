import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInvarianceOfDomain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBrouwerFixedPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace InvarianceOfDomain

open Metric Set MeasureTheory

variable {n : ℕ}

theorem brouwer_closedBall (hB : BrouwerFixedPoint.Statement) {a : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    {h : (Fin n → ℝ) → Fin n → ℝ} (hc : ContinuousOn h (closedBall a r))
    (hm : MapsTo h (closedBall a r) (closedBall a r)) : ∃ x ∈ closedBall a r, h x = x := by
  have haff : MapsTo (fun x : Fin n → ℝ => a + r • x) (closedBall 0 1) (closedBall a r) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    nlinarith [norm_nonneg x]
  have hcont : ContinuousOn (fun x : Fin n → ℝ => a + r • x) (closedBall 0 1) :=
    by fun_prop
  have hcomp : ContinuousOn (fun x : Fin n → ℝ => h (a + r • x)) (closedBall 0 1) := hc.comp hcont haff
  obtain ⟨x, hx, hfix⟩ := hB n (fun x => r⁻¹ • (h (a + r • x) - a)) (by fun_prop)
    (by
      intro x hx
      have hy := hm (haff hx)
      rw [mem_closedBall, dist_eq_norm] at hy
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le),
        inv_mul_le_iff₀ hr, mul_one]
      exact hy)
  refine ⟨a + r • x, haff hx, ?_⟩
  have h2 : r • (r⁻¹ • (h (a + r • x) - a)) = r • x := by rw [hfix]
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at h2
  exact sub_eq_iff_eq_add'.mp h2

def smoothSubalgebra (n : ℕ) : Subalgebra ℝ C(Fin n → ℝ, ℝ) where
  carrier := {g | ContDiff ℝ 1 (g : (Fin n → ℝ) → ℝ)}
  mul_mem' {g h} hg hh := by
    simp only [mem_ofPred_eq, ContinuousMap.coe_mul]
    exact ContDiff.mul hg hh
  add_mem' {g h} hg hh := by
    simp only [mem_ofPred_eq, ContinuousMap.coe_add]
    exact ContDiff.add hg hh
  algebraMap_mem' c := by
    simp only [mem_ofPred_eq]
    convert (contDiff_const (c := c) : ContDiff ℝ 1 fun _ : Fin n → ℝ => c) using 1
    ext x
    simp

theorem smoothSubalgebra_separatesPoints : (smoothSubalgebra n).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  refine ⟨fun z => z i, ⟨⟨fun z => z i, continuous_apply i⟩, ?_, rfl⟩, hi⟩
  show ContDiff ℝ 1 fun z : Fin n → ℝ => z i
  exact contDiff_apply ℝ ℝ i

theorem exists_differentiable_near {S : Set (Fin n → ℝ)} (hS : IsCompact S)
    (G : (Fin n → ℝ) → Fin n → ℝ) (hG : Continuous G) {η : ℝ} (hη : 0 < η) :
    ∃ P : (Fin n → ℝ) → Fin n → ℝ, Differentiable ℝ P ∧ ∀ y ∈ S, ‖P y - G y‖ < η := by
  have h : ∀ i : Fin n, ∃ g ∈ smoothSubalgebra n, ∀ y ∈ S, ‖(g : (Fin n → ℝ) → ℝ) y - G y i‖ < η :=
    fun i => ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      smoothSubalgebra_separatesPoints ⟨fun y => G y i, (continuous_apply i).comp hG⟩ hS hη
  choose g hg hgS using h
  refine ⟨fun y i => g i y, differentiable_pi.2 fun i => ?_, fun y hy => ?_⟩
  · exact (show ContDiff ℝ 1 (g i : (Fin n → ℝ) → ℝ) from hg i).differentiable one_ne_zero
  · rw [pi_norm_lt_iff hη]
    intro i
    simpa using hgS i y hy

theorem exists_small_avoid {P : (Fin n → ℝ) → Fin n → ℝ} (hP : Differentiable ℝ P) (c a : Fin n → ℝ)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∃ v : Fin n → ℝ, ‖v‖ < δ ∧ ∀ y ∈ sphere c ρ, P y ≠ a + v := by
  have hnull : volume (P '' sphere c ρ) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hP.differentiableOn
      (Measure.addHaar_sphere_of_ne_zero volume c hρ.ne')
  by_contra! hall
  have hsub : ball a δ ⊆ P '' sphere c ρ := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hall (z - a) (by rwa [mem_ball, dist_eq_norm] at hz)
    exact ⟨y, hy, by rw [hyz]; abel⟩
  have hle := measure_mono (μ := volume) hsub
  rw [hnull] at hle
  exact (measure_ball_pos volume a hδ).ne' (nonpos_iff_eq_zero.mp hle)

theorem exists_pos_le {s : Set (Fin n → ℝ)} (hs : IsCompact s) {g : (Fin n → ℝ) → ℝ}
    (hg : ContinuousOn g s) (hpos : ∀ y ∈ s, 0 < g y) : ∃ δ > 0, ∀ y ∈ s, δ ≤ g y := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨y0, hy0, hmin⟩ := hs.exists_isMinOn hne hg
    exact ⟨g y0, hpos y0 hy0, fun y hy => hmin hy⟩

noncomputable def radialPush (c : Fin n → ℝ) (ρ : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  c + max 1 (ρ / ‖y - c‖) • (y - c)

theorem radialPush_of_le {c y : Fin n → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hy : ρ ≤ dist y c) :
    radialPush c ρ y = y := by
  rw [dist_eq_norm] at hy
  have hpos : 0 < ‖y - c‖ := hρ.trans_le hy
  have h1 : ρ / ‖y - c‖ ≤ 1 := (div_le_one hpos).2 hy
  rw [radialPush, max_eq_left h1, one_smul, add_sub_cancel]

theorem radialPush_mem_sphere {c y : Fin n → ℝ} {ρ : ℝ} (hy : dist y c < ρ) (hyc : y ≠ c) :
    radialPush c ρ y ∈ sphere c ρ := by
  rw [dist_eq_norm] at hy
  have hpos : 0 < ‖y - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hyc)
  have h1 : 1 ≤ ρ / ‖y - c‖ := (one_le_div hpos).2 hy.le
  rw [mem_sphere, dist_eq_norm, radialPush, max_eq_right h1, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (div_nonneg (hpos.trans hy).le hpos.le), div_mul_cancel₀ ρ hpos.ne']

theorem continuousOn_radialPush (c : Fin n → ℝ) (ρ : ℝ) : ContinuousOn (radialPush c ρ) {y | y ≠ c} := by
  have hn : ContinuousOn (fun y : Fin n → ℝ => ρ / ‖y - c‖) {y | y ≠ c} := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro y hy
    exact norm_ne_zero_iff.2 (sub_ne_zero.2 hy)
  have hm : ContinuousOn (fun y : Fin n → ℝ => max 1 (ρ / ‖y - c‖)) {y | y ≠ c} :=
    continuousOn_const.sup hn
  unfold radialPush
  fun_prop

theorem mem_interior_image (hB : BrouwerFixedPoint.Statement) {f : (Fin n → ℝ) → Fin n → ℝ}
    {a : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (hc : ContinuousOn f (closedBall a r))
    (hi : InjOn f (closedBall a r)) : f a ∈ interior (f '' closedBall a r) := by
  have hK : IsCompact (closedBall a r) := isCompact_closedBall a r

  obtain ⟨G, hGf⟩ : ∃ G : C(Fin n → ℝ, Fin n → ℝ), ∀ x ∈ closedBall a r, G (f x) = x := by
    have : CompactSpace (closedBall a r) := isCompact_iff_compactSpace.mp hK
    have hce : Topology.IsClosedEmbedding ((closedBall a r).domRestrict f) :=
      hc.domRestrict.isClosedEmbedding hi.injective
    obtain ⟨G, hG⟩ := ContinuousMap.exists_extension' hce ⟨Subtype.val, continuous_subtype_val⟩
    exact ⟨G, fun x hx => congrFun hG ⟨x, hx⟩⟩
  have hGa : G (f a) = a := hGf a (mem_closedBall_self hr.le)
  by_contra hno

  obtain ⟨ρ3, hρ3, hρG⟩ := Metric.continuousAt_iff.mp G.continuous.continuousAt (r / 4) (by positivity)
  obtain ⟨ρ, hρ, hρlt⟩ : ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ < ρ3 := ⟨ρ3 / 3, by positivity, by linarith⟩
  have hGnear : ∀ y, dist y (f a) ≤ 2 * ρ → dist (G y) a < r / 4 := fun y hy => by
    have h1 := hρG (show dist y (f a) < ρ3 by linarith)
    rwa [hGa] at h1

  obtain ⟨c, hcball, hcK⟩ : ∃ c, dist c (f a) < ρ ∧ c ∉ f '' closedBall a r := by
    by_contra! hall
    exact hno (mem_interior_iff_mem_nhds.2
      (Metric.mem_nhds_iff.2 ⟨ρ, hρ, fun c hc => hall c (mem_ball.1 hc)⟩))
  have hfK : IsCompact (f '' closedBall a r) := hK.image_of_continuousOn hc
  have hS1c : IsCompact (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) :=
    hfK.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hSc : IsCompact ((f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ) :=
    hS1c.union (isCompact_sphere c ρ)

  have hS1pos : ∀ y ∈ f '' closedBall a r ∩ {y | ρ ≤ dist y c}, 0 < dist (G y) a := by
    rintro _ ⟨⟨x, hx, rfl⟩, hy⟩
    rw [hGf x hx, dist_pos]
    intro hxa
    subst hxa
    rw [mem_ofPred_eq, dist_comm] at hy
    linarith
  obtain ⟨δ0, hδ0, hδ0le⟩ :=
    exists_pos_le hS1c (G.continuous.dist continuous_const).continuousOn hS1pos
  obtain ⟨δ, hδ, hδδ0, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ r / 4 :=
    ⟨min δ0 (r / 4), lt_min hδ0 (by positivity), min_le_left _ _, min_le_right _ _⟩

  obtain ⟨P, hPd, hPS⟩ := exists_differentiable_near hSc G G.continuous (half_pos hδ)
  obtain ⟨v, hv, hPv⟩ := exists_small_avoid hPd c a hρ (half_pos hδ)
  have hQG : ∀ y ∈ (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ,
      ‖P y - v - G y‖ < δ := fun y hy => by
    have h1 := hPS y hy
    calc ‖P y - v - G y‖ = ‖(P y - G y) - v‖ := by congr 1; abel
      _ ≤ ‖P y - G y‖ + ‖v‖ := norm_sub_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add h1 hv
      _ = δ := add_halves δ
  have hQne : ∀ y ∈ (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ, P y - v ≠ a := by
    rintro y (hy | hy) hQa
    · have h1 := hQG y (Or.inl hy)
      have h2 := hδ0le y hy
      rw [hQa, norm_sub_rev] at h1
      rw [dist_eq_norm] at h2
      linarith
    · exact hPv y hy (eq_add_of_sub_eq hQa)

  have hfc : ∀ x ∈ closedBall a r, f x ≠ c := fun x hx h => hcK ⟨x, hx, h⟩
  have hΦS : ∀ x ∈ closedBall a r,
      radialPush c ρ (f x) ∈ (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ := by
    intro x hx
    by_cases hle : ρ ≤ dist (f x) c
    · rw [radialPush_of_le hρ hle]
      exact Or.inl ⟨⟨x, hx, rfl⟩, hle⟩
    · exact Or.inr (radialPush_mem_sphere (not_le.1 hle) (hfc x hx))
  have hΦc : ContinuousOn (fun x => radialPush c ρ (f x)) (closedBall a r) :=
    (continuousOn_radialPush c ρ).comp hc (fun x hx => hfc x hx)
  have hPΦ : ContinuousOn (fun x => P (radialPush c ρ (f x))) (closedBall a r) :=
    hPd.continuous.comp_continuousOn hΦc
  have hH : ContinuousOn (fun x => x - (P (radialPush c ρ (f x)) - v - a)) (closedBall a r) := by
    have h1 := (hPΦ.sub (continuousOn_const (c := v))).sub (continuousOn_const (c := a))
    exact continuousOn_id.sub h1

  obtain ⟨x, hxK, hfix⟩ := brouwer_closedBall hB (a := a) hr
    (h := fun x => x - (P (radialPush c ρ (f x)) - v - a)) hH (by
      intro x hx
      have hGx : G (f x) = x := hGf x hx
      rw [mem_closedBall, dist_eq_norm]
      show ‖x - (P (radialPush c ρ (f x)) - v - a) - a‖ ≤ r
      by_cases hle : ρ ≤ dist (f x) c
      · rw [radialPush_of_le hρ hle]
        have h1 := hQG (f x) (Or.inl ⟨⟨x, hx, rfl⟩, hle⟩)
        rw [hGx] at h1
        calc ‖x - (P (f x) - v - a) - a‖ = ‖-(P (f x) - v - x)‖ := by congr 1; abel
          _ = ‖P (f x) - v - x‖ := norm_neg _
          _ ≤ r := by linarith
      · have hzS := radialPush_mem_sphere (not_le.1 hle) (hfc x hx)
        have hxa : dist x a < r / 4 := by
          rw [← hGx]
          apply hGnear
          calc dist (f x) (f a) ≤ dist (f x) c + dist c (f a) := dist_triangle _ _ _
            _ ≤ 2 * ρ := by linarith [not_le.1 hle]
        generalize radialPush c ρ (f x) = z at hzS ⊢
        have h1 := hQG z (Or.inr hzS)
        have hza : dist (G z) a < r / 4 := by
          apply hGnear
          have hzc : dist z c = ρ := mem_sphere.mp hzS
          calc dist z (f a) ≤ dist z c + dist c (f a) := dist_triangle _ _ _
            _ ≤ 2 * ρ := by linarith
        rw [dist_eq_norm] at hxa hza
        calc ‖x - (P z - v - a) - a‖ = ‖(x - a) - (P z - v - G z) - (G z - a)‖ := by congr 1; abel
          _ ≤ ‖(x - a) - (P z - v - G z)‖ + ‖G z - a‖ := norm_sub_le _ _
          _ ≤ ‖x - a‖ + ‖P z - v - G z‖ + ‖G z - a‖ := by
            gcongr
            exact norm_sub_le _ _
          _ ≤ r := by linarith)
  exact hQne _ (hΦS x hxK) (sub_eq_zero.mp (sub_eq_self.mp hfix))

theorem proof (hB : BrouwerFixedPoint.Statement) : InvarianceOfDomain.Statement := by
  intro n U f hU hc hi
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hsub : closedBall x (r / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hball
  have h := mem_interior_image hB (half_pos hr) (hc.mono hsub) (hi.mono hsub)
  exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp h)
    (Set.image_mono hsub)

end InvarianceOfDomain

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
