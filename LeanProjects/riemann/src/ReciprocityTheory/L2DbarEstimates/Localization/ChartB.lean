import ReciprocityTheory.L2DbarEstimates.Localization.ChartA

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

section Main

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}

theorem chT_div (hExt : ExtendStatement n M) (hz : IsLocalHomeomorph z) (he : IsChart n z e)
    (G : M → V n) (D : M → ℂ) (hG : AEStronglyMeasurable G (vol n z))
    (hD : AEStronglyMeasurable D (vol n z)) (hGs : tsupport G ⊆ e.source)
    (hDs : tsupport D ⊆ e.source) (hDiv : IsWeakDiv n z G D) (ρ : V n → ℝ)
    (hρd : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρt : tsupport ρ ⊆ e.target)
    (O : Set (V n)) (hOo : IsOpen O) (h1 : ∀ y ∈ O, ρ y = 1)
    (hO : ∀ y ∈ e.target, e.symm y ∈ tsupport G ∪ tsupport D → y ∈ O)
    (φ : V n → ℂ) (hφd : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ y, ∑ j, e.target.indicator (G ∘ e.symm) y j * wd n j φ y =
      -∫ y, e.target.indicator (D ∘ e.symm) y * φ y := by
  set ψ : V n → ℂ := fun y => (ρ y : ℂ) * φ y with hψdef
  obtain ⟨hψd, hψc, hψt⟩ := chT_mulρ ρ hρd hρc e.target hρt φ hφd
  obtain ⟨hT, hval, -⟩ := chT_test hExt hz he ψ hψd hψc hψt
  have hX := (hExt z hz e ψ he hψd hψc hψt).2.2.2
  have hms : MeasurableSet e.source := e.open_source.measurableSet
  have hmt : MeasurableSet e.target := e.open_target.measurableSet
  have hGz : ∀ x, x ∉ e.source → G x = 0 := fun x hx => by
    by_contra h
    exact hx (hGs (subset_tsupport _ (Function.mem_support.2 h)))
  have h2z : ∀ x, x ∉ e.source → D x = 0 := fun x hx => by
    by_contra h
    exact hx (hDs (subset_tsupport _ (Function.mem_support.2 h)))
  have hGO : ∀ y ∈ e.target, G (e.symm y) ≠ 0 → y ∈ O := fun y hy h =>
    hO y hy (Or.inl (subset_tsupport _ (Function.mem_support.2 h)))
  have h2O : ∀ y ∈ e.target, D (e.symm y) ≠ 0 → y ∈ O := fun y hy h =>
    hO y hy (Or.inr (subset_tsupport _ (Function.mem_support.2 h)))
  have hcf := hψd.continuous_fderiv (by simp)
  have hind : ∀ (g : V n → ℂ), Continuous g →
      AEStronglyMeasurable (e.source.indicator (fun x => g (e x))) (vol n z) :=
    fun g hg => (aestronglyMeasurable_indicator_iff hms).2
      ((hg.comp_continuousOn e.continuousOn).aestronglyMeasurable hms)
  have hwdc : ∀ j, Continuous (wd n j ψ) := fun j =>
    ((hcf.clm_apply continuous_const).sub (continuous_const.mul (hcf.clm_apply continuous_const))).div_const 2
  have hw := hDiv _ hT

  have hL : ∫ x, ∑ j, G x j * d n z j (e.source.indicator (ψ ∘ e)) x ∂vol n z =
      ∫ y, ∑ j, e.target.indicator (G ∘ e.symm) y j * wd n j φ y := by
    calc _ = ∫ x, ∑ j, G x j * e.source.indicator (fun x => wd n j ψ (e x)) x ∂vol n z := by
          congr 1
          funext x
          by_cases hx : x ∈ e.source
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [Set.indicator_of_mem hx, (hX j x hx).1]
          · simp [hGz x hx]
      _ = ∫ y in e.target, ∑ j, G (e.symm y) j *
            e.source.indicator (fun x => wd n j ψ (e x)) (e.symm y) :=
          chT_int hz he _ (Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
            (chT_comp (vol n z) G hG j).mul (hind _ (hwdc j))) (fun x hx => by simp [hGz x hx])
      _ = ∫ y, ∑ j, e.target.indicator (G ∘ e.symm) y j * wd n j φ y := by
          rw [← integral_indicator hmt]
          congr 1
          funext y
          by_cases hy : y ∈ e.target
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Set.indicator_of_mem (e.map_target hy), e.right_inv hy, Function.comp_apply]
            by_cases hG0 : G (e.symm y) = 0
            · simp [hG0]
            · rw [(chT_wd ρ φ O hOo h1 y (hGO y hy hG0) j).1]
          · simp [Set.indicator_apply, hy]
  have hR : ∫ x, D x * e.source.indicator (ψ ∘ e) x ∂vol n z =
      ∫ y, e.target.indicator (D ∘ e.symm) y * φ y := by
    calc _ = ∫ y in e.target, D (e.symm y) * e.source.indicator (ψ ∘ e) (e.symm y) :=
          chT_int hz he _ (hD.mul (hind ψ hψd.continuous)) (fun x hx => by simp [h2z x hx])
      _ = _ := by
          rw [← integral_indicator hmt]
          congr 1
          funext y
          by_cases hy : y ∈ e.target
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hval y hy, Function.comp_apply]
            by_cases hD0 : D (e.symm y) = 0
            · simp [hD0]
            · simp [hψdef, h1 y (h2O y hy hD0)]
          · simp [Set.indicator_apply, hy]
  rw [hL, hR] at hw
  exact hw

theorem chT_S (hExt : ExtendStatement n M) (hz : IsLocalHomeomorph z) (he : IsChart n z e)
    (G : M → V n) (S : M → Fin n → Fin n → ℂ) (hG : AEStronglyMeasurable G (vol n z))
    (hS : AEStronglyMeasurable S (vol n z)) (hGs : tsupport G ⊆ e.source)
    (hSs : tsupport S ⊆ e.source) (hSw : IsWeakS n z G S) (ρ : V n → ℝ)
    (hρd : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρt : tsupport ρ ⊆ e.target)
    (O : Set (V n)) (hOo : IsOpen O) (h1 : ∀ y ∈ O, ρ y = 1)
    (hO : ∀ y ∈ e.target, e.symm y ∈ tsupport G ∪ tsupport S → y ∈ O)
    (φ : V n → ℂ) (hφd : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (j k : Fin n) :
    ∫ y, (e.target.indicator (G ∘ e.symm) y k * wdb n j φ y -
        e.target.indicator (G ∘ e.symm) y j * wdb n k φ y) =
      -∫ y, e.target.indicator (S ∘ e.symm) y j k * φ y := by
  set ψ : V n → ℂ := fun y => (ρ y : ℂ) * φ y with hψdef
  obtain ⟨hψd, hψc, hψt⟩ := chT_mulρ ρ hρd hρc e.target hρt φ hφd
  obtain ⟨hT, hval, -⟩ := chT_test hExt hz he ψ hψd hψc hψt
  have hX := (hExt z hz e ψ he hψd hψc hψt).2.2.2
  have hms : MeasurableSet e.source := e.open_source.measurableSet
  have hmt : MeasurableSet e.target := e.open_target.measurableSet
  have hGz : ∀ x, x ∉ e.source → G x = 0 := fun x hx => by
    by_contra h
    exact hx (hGs (subset_tsupport _ (Function.mem_support.2 h)))
  have h2z : ∀ x, x ∉ e.source → S x = 0 := fun x hx => by
    by_contra h
    exact hx (hSs (subset_tsupport _ (Function.mem_support.2 h)))
  have hGO : ∀ y ∈ e.target, G (e.symm y) ≠ 0 → y ∈ O := fun y hy h =>
    hO y hy (Or.inl (subset_tsupport _ (Function.mem_support.2 h)))
  have h2O : ∀ y ∈ e.target, S (e.symm y) ≠ 0 → y ∈ O := fun y hy h =>
    hO y hy (Or.inr (subset_tsupport _ (Function.mem_support.2 h)))
  have hcf := hψd.continuous_fderiv (by simp)
  have hind : ∀ (g : V n → ℂ), Continuous g →
      AEStronglyMeasurable (e.source.indicator (fun x => g (e x))) (vol n z) :=
    fun g hg => (aestronglyMeasurable_indicator_iff hms).2
      ((hg.comp_continuousOn e.continuousOn).aestronglyMeasurable hms)
  have hwdc : ∀ j, Continuous (wdb n j ψ) := fun j =>
    ((hcf.clm_apply continuous_const).add (continuous_const.mul (hcf.clm_apply continuous_const))).div_const 2
  have hw := hSw _ hT j k
  have hL : ∫ x, (G x k * db n z j (e.source.indicator (ψ ∘ e)) x -
        G x j * db n z k (e.source.indicator (ψ ∘ e)) x) ∂vol n z =
      ∫ y, (e.target.indicator (G ∘ e.symm) y k * wdb n j φ y -
        e.target.indicator (G ∘ e.symm) y j * wdb n k φ y) := by
    calc _ = ∫ x, (G x k * e.source.indicator (fun x => wdb n j ψ (e x)) x -
            G x j * e.source.indicator (fun x => wdb n k ψ (e x)) x) ∂vol n z := by
          congr 1
          funext x
          by_cases hx : x ∈ e.source
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, (hX j x hx).2, (hX k x hx).2]
          · simp [hGz x hx]
      _ = ∫ y in e.target, (G (e.symm y) k * e.source.indicator (fun x => wdb n j ψ (e x)) (e.symm y) -
            G (e.symm y) j * e.source.indicator (fun x => wdb n k ψ (e x)) (e.symm y)) :=
          chT_int hz he _ (((chT_comp (vol n z) G hG k).mul (hind _ (hwdc j))).sub
            ((chT_comp (vol n z) G hG j).mul (hind _ (hwdc k)))) (fun x hx => by simp [hGz x hx])
      _ = _ := by
          rw [← integral_indicator hmt]
          congr 1
          funext y
          by_cases hy : y ∈ e.target
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy,
              Set.indicator_of_mem (e.map_target hy), Set.indicator_of_mem (e.map_target hy),
              e.right_inv hy, Function.comp_apply]
            by_cases hG0 : G (e.symm y) = 0
            · simp [hG0]
            · rw [(chT_wd ρ φ O hOo h1 y (hGO y hy hG0) j).2, (chT_wd ρ φ O hOo h1 y (hGO y hy hG0) k).2]
          · simp [Set.indicator_apply, hy]
  have hR : ∫ x, S x j k * e.source.indicator (ψ ∘ e) x ∂vol n z =
      ∫ y, e.target.indicator (S ∘ e.symm) y j k * φ y := by
    have hSjk : AEStronglyMeasurable (fun x => S x j k) (vol n z) :=
      (continuous_apply k).comp_aestronglyMeasurable ((continuous_apply j).comp_aestronglyMeasurable hS)
    calc _ = ∫ y in e.target, S (e.symm y) j k * e.source.indicator (ψ ∘ e) (e.symm y) :=
          chT_int hz he _ (hSjk.mul (hind ψ hψd.continuous)) (fun x hx => by simp [h2z x hx])
      _ = _ := by
          rw [← integral_indicator hmt]
          congr 1
          funext y
          by_cases hy : y ∈ e.target
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hval y hy, Function.comp_apply]
            by_cases hS0 : S (e.symm y) = 0
            · simp [hS0]
            · simp [hψdef, h1 y (h2O y hy hS0)]
          · simp [Set.indicator_apply, hy]
  rw [hL, hR] at hw
  exact hw

end Main

section Main

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}

theorem chT_back (hExt : ExtendStatement n M) (hz : IsLocalHomeomorph z) (he : IsChart n z e)
    (G : M → V n) (D : M → ℂ) (S : M → Fin n → Fin n → ℂ)
    (hG : AEStronglyMeasurable G (vol n z)) (hD : AEStronglyMeasurable D (vol n z))
    (hS : AEStronglyMeasurable S (vol n z))
    (hGs : tsupport G ⊆ e.source) (hDs : tsupport D ⊆ e.source) (hSs : tsupport S ⊆ e.source)
    (K₀ : Set (V n)) (hK₀c : IsCompact K₀) (hK₀t : K₀ ⊆ e.target) (G' : V n → V n)
    (hG'd : ContDiff ℝ ∞ G') (hG'0 : ∀ y, y ∉ K₀ → G' y = 0) (δ : ℝ≥0∞)
    (h1 : ∫⁻ y, ‖G' y - e.target.indicator (G ∘ e.symm) y‖ₑ ^ 2 < δ)
    (h2 : ∫⁻ y, ‖(∑ j, wd n j (fun u => G' u j) y) - e.target.indicator (D ∘ e.symm) y‖ₑ ^ 2 < δ)
    (h3 : ∫⁻ y, ENNReal.ofReal (sq2 n (fun j k =>
        wdb n j (fun u => G' u k) y - wdb n k (fun u => G' u j) y -
          e.target.indicator (S ∘ e.symm) y j k)) < δ) :
    ∃ g : M → V n, IsTestForm n z g ∧ (∀ x, x ∉ e.symm '' K₀ → g x = 0) ∧
      nV n z (fun x => g x - G x) (fun _ => 0) < δ ∧
      wint n z (fun x => divF n z g x - D x) (fun _ => 0) < δ ∧
      n2 n z (fun x => sbar n z g x - S x) (fun _ => 0) < δ := by
  classical
  have hms : MeasurableSet e.source := e.open_source.measurableSet
  have hmt : MeasurableSet e.target := e.open_target.measurableSet
  have hK₀cl : IsClosed K₀ := hK₀c.isClosed

  have hfz : ∀ (f : V n → ℂ) (y : V n), f =ᶠ[𝓝 y] (fun _ => (0 : ℂ)) → ∀ i,
      wd n i f y = 0 ∧ wdb n i f y = 0 := by
    intro f y hf i
    simp [wd, wdb, hf.fderiv_eq]
  have hdz : ∀ (f : M → ℂ) (x : M), x ∉ tsupport f → ∀ i, d n z i f x = 0 ∧ db n z i f x = 0 := by
    intro f x hx i
    by_cases h : ∃ e' : OpenPartialHomeomorph M (V n), IsChart n z e' ∧ x ∈ e'.source
    · have hev : (f ∘ (Classical.choose h).symm) =ᶠ[𝓝 (z x)] (fun _ => (0 : ℂ)) := by
        obtain ⟨hc, hxs⟩ := Classical.choose_spec h
        rw [hc hxs]
        have hW := (Classical.choose h).continuousOn_symm.isOpen_inter_preimage
          (Classical.choose h).open_target (isClosed_tsupport f).isOpen_compl
        have hmem : (Classical.choose h) x ∈
            (Classical.choose h).target ∩ (Classical.choose h).symm ⁻¹' (tsupport f)ᶜ := by
          refine ⟨(Classical.choose h).map_source hxs, ?_⟩
          show (Classical.choose h).symm ((Classical.choose h) x) ∉ tsupport f
          rw [(Classical.choose h).left_inv hxs]
          exact hx
        filter_upwards [hW.mem_nhds hmem] with y hy
        show f ((Classical.choose h).symm y) = 0
        by_contra hne
        exact hy.2 (subset_tsupport _ (Function.mem_support.2 hne))
      simp only [d, db, dif_pos h]
      exact hfz _ _ hev i
    · simp [d, db, dif_neg h]
  have hG'0j : ∀ j, ∀ y, y ∉ K₀ → G' y j = 0 := fun j y hy => by
    rw [hG'0 y hy]
    simp
  have hG'j : ∀ j, ContDiff ℝ ∞ (fun u => G' u j) := fun j => by
    have := ((EuclideanSpace.proj j : V n →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hG'd
    exact this
  have hcs : ∀ j, HasCompactSupport (fun u => G' u j) := fun j =>
    HasCompactSupport.intro hK₀c (fun y hy => hG'0j j y hy)
  have hts : ∀ j, tsupport (fun u => G' u j) ⊆ e.target := fun j =>
    (closure_minimal (fun y hy => by by_contra h; exact hy (hG'0j j y h)) hK₀cl).trans hK₀t
  have hE := fun j => hExt z hz e (fun u => G' u j) he (hG'j j) (hcs j) (hts j)
  have hwz : ∀ j, ∀ y, y ∉ K₀ → ∀ i, wd n i (fun u => G' u j) y = 0 ∧ wdb n i (fun u => G' u j) y = 0 :=
    fun j y hy i => hfz _ y (by
      filter_upwards [hK₀cl.isOpen_compl.mem_nhds hy] with u hu
      exact hG'0j j u hu) i
  have hcf : ∀ (f : V n → ℂ), ContDiff ℝ ∞ f → ∀ i, Continuous (wd n i f) ∧ Continuous (wdb n i f) := by
    intro f hf i
    have h := hf.continuous_fderiv (by simp)
    exact ⟨((h.clm_apply continuous_const).sub (continuous_const.mul (h.clm_apply continuous_const))).div_const 2,
      ((h.clm_apply continuous_const).add (continuous_const.mul (h.clm_apply continuous_const))).div_const 2⟩
  have hind : ∀ {E : Type} [NormedAddCommGroup E] (w : V n → E), Continuous w →
      AEStronglyMeasurable (e.source.indicator (fun x => w (e x))) (vol n z) :=
    fun w hw => (aestronglyMeasurable_indicator_iff hms).2
      ((hw.comp_continuousOn e.continuousOn).aestronglyMeasurable hms)
  have hGz : ∀ x, x ∉ e.source → G x = 0 := fun x hx => by
    by_contra h
    exact hx (hGs (subset_tsupport _ (Function.mem_support.2 h)))
  have hDz : ∀ x, x ∉ e.source → D x = 0 := fun x hx => by
    by_contra h
    exact hx (hDs (subset_tsupport _ (Function.mem_support.2 h)))
  have hSz : ∀ x, x ∉ e.source → S x = 0 := fun x hx => by
    by_contra h
    exact hx (hSs (subset_tsupport _ (Function.mem_support.2 h)))

  have htr : ∀ (F : M → ℝ≥0∞) (H : V n → ℝ≥0∞), AEMeasurable F (vol n z) →
      (∀ x, x ∉ e.source → F x = 0) → (∀ y ∈ e.target, F (e.symm y) = H y) →
      (∀ y, y ∉ e.target → H y = 0) → ∫⁻ x, F x ∂vol n z = ∫⁻ y, H y := by
    intro F H hF hs hon hoff
    rw [chT_lint hz he F hF hs, ← lintegral_indicator hmt]
    congr 1
    funext y
    by_cases hy : y ∈ e.target
    · rw [Set.indicator_of_mem hy, hon y hy]
    · rw [Set.indicator_apply, if_neg hy, hoff y hy]
  set g : M → V n := e.source.indicator (G' ∘ e) with hgdef
  have hgj : ∀ j, (fun x => g x j) = e.source.indicator ((fun u => G' u j) ∘ e) := fun j => by
    funext x
    by_cases hx : x ∈ e.source <;> simp [hgdef, Set.indicator_apply, hx]
  have hdiv : ∀ x, divF n z g x =
      e.source.indicator (fun x => ∑ i, wd n i (fun u => G' u i) (e x)) x := by
    intro x
    show ∑ i, d n z i (fun y => g y i) x = _
    by_cases hx : x ∈ e.source
    · rw [Set.indicator_of_mem hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hgj i]
      exact ((hE i).2.2.2 i x hx).1
    · rw [Set.indicator_apply, if_neg hx]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hgj i]
      exact (hdz _ x (fun h => hx ((hE i).2.2.1 h)) i).1
  have hsb : ∀ x, sbar n z g x - S x = fun j k =>
      e.source.indicator (fun x => wdb n j (fun u => G' u k) (e x) - wdb n k (fun u => G' u j) (e x)) x -
        S x j k := by
    intro x
    funext j k
    show db n z j (fun y => g y k) x - db n z k (fun y => g y j) x - S x j k = _
    rw [hgj k, hgj j]
    by_cases hx : x ∈ e.source
    · rw [Set.indicator_of_mem hx, ((hE k).2.2.2 j x hx).2, ((hE j).2.2.2 k x hx).2]
    · rw [Set.indicator_apply, if_neg hx, (hdz _ x (fun h => hx ((hE k).2.2.1 h)) j).2,
        (hdz _ x (fun h => hx ((hE j).2.2.1 h)) k).2, sub_zero]
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hgj j]
    exact ⟨fun e' he' => ((hE j).1 e' he').of_le (by first | (simp; done) | (norm_num; done) | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.2 le_top | exact le_top), (hE j).2.1⟩
  · intro x hx
    by_cases hxs : x ∈ e.source
    · rw [hgdef, Set.indicator_of_mem hxs, Function.comp_apply]
      exact hG'0 _ (fun h => hx ⟨e x, h, e.left_inv hxs⟩)
    · rw [hgdef, Set.indicator_apply, if_neg hxs]
  · have heq : nV n z (fun x => g x - G x) (fun _ => 0) =
        ∫⁻ y, ‖G' y - e.target.indicator (G ∘ e.symm) y‖ₑ ^ 2 := by
      simp only [nV, neg_zero, Real.exp_zero, mul_one]
      apply htr
      · exact (((hind G' hG'd.continuous).sub hG).norm.pow 2).aemeasurable.ennreal_ofReal
      · intro x hx
        simp [hgdef, Set.indicator_apply, hx, hGz x hx]
      · intro y hy
        rw [hgdef, Set.indicator_of_mem (e.map_target hy), Function.comp_apply, e.right_inv hy,
          Set.indicator_of_mem hy, Function.comp_apply, ENNReal.ofReal_pow (norm_nonneg _),
          ofReal_norm_eq_enorm]
      · intro y hy
        rw [hG'0 y (fun h => hy (hK₀t h)), Set.indicator_apply, if_neg hy]
        simp
    rw [heq]
    exact h1
  · have hcs' : Continuous (fun y => ∑ i, wd n i (fun u => G' u i) y) :=
      continuous_finset_sum _ fun i _ => (hcf _ (hG'j i) i).1
    have heq : wint n z (fun x => divF n z g x - D x) (fun _ => 0) =
        ∫⁻ y, ‖(∑ j, wd n j (fun u => G' u j) y) - e.target.indicator (D ∘ e.symm) y‖ₑ ^ 2 := by
      simp only [wint, neg_zero, Real.exp_zero, mul_one, hdiv]
      apply htr
      · exact (((hind _ hcs').sub hD).norm.pow 2).aemeasurable.ennreal_ofReal
      · intro x hx
        simp [Set.indicator_apply, hx, hDz x hx]
      · intro y hy
        rw [Set.indicator_of_mem (e.map_target hy), e.right_inv hy, Set.indicator_of_mem hy, Function.comp_apply,
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      · intro y hy
        have hyK : y ∉ K₀ := fun h => hy (hK₀t h)
        rw [Finset.sum_eq_zero fun i _ => (hwz i y hyK i).1, Set.indicator_apply, if_neg hy]
        simp
    rw [heq]
    exact h2
  · have hSjk : ∀ j k, AEStronglyMeasurable (fun x => S x j k) (vol n z) := fun j k =>
      (continuous_apply k).comp_aestronglyMeasurable ((continuous_apply j).comp_aestronglyMeasurable hS)
    have heq : n2 n z (fun x => sbar n z g x - S x) (fun _ => 0) =
        ∫⁻ y, ENNReal.ofReal (sq2 n (fun j k =>
          wdb n j (fun u => G' u k) y - wdb n k (fun u => G' u j) y -
            e.target.indicator (S ∘ e.symm) y j k)) := by
      simp only [n2, neg_zero, Real.exp_zero, mul_one, hsb]
      apply htr
      · refine (AEStronglyMeasurable.aemeasurable ?_).ennreal_ofReal
        simp only [sq2, div_eq_mul_inv]
        refine AEStronglyMeasurable.mul_const ?_ _
        refine Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
          Finset.aestronglyMeasurable_fun_sum _ fun k _ => ?_
        exact ((hind _ ((hcf _ (hG'j k) j).2.sub (hcf _ (hG'j j) k).2)).sub (hSjk j k)).norm.pow 2
      · intro x hx
        simp [sq2, Set.indicator_apply, hx, hSz x hx]
      · intro y hy
        simp only [sq2, Set.indicator_of_mem (e.map_target hy), Set.indicator_of_mem hy,
          e.right_inv hy, Function.comp_apply]
      · intro y hy
        have hyK : y ∉ K₀ := fun h => hy (hK₀t h)
        have h0 : ∀ i j, wdb n i (fun u => G' u j) y = 0 := fun i j => (hwz j y hyK i).2
        simp [sq2, h0, Set.indicator_apply, hy]
    rw [heq]
    exact h3

end Main

end

end ReciprocityTheory.L2DbarEstimates.F
