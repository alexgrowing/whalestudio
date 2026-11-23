import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.ConclSubseq

noncomputable section

open NumberField MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem caseB' (hTB : TwBound) (hNE : NodeEmb) (hG : Graft) (hTS : TwShift) (hTr : TrStable) {N : ℕ}
    {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)}
    {Ω Ωb : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))} {Θ Θb : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))}
    (hΩb : KTypes E Ωb) (hΘb : Levels E Θb)
    (hBTK : ∀ (r s : ℕ) (h : r + s = N) (V : Submodule ℂ (Sm E (r + s))) (V₁ : Submodule ℂ (Sm E r))
      (V₂ : Submodule ℂ (Sm E s)) (z₁ z₂ : ℂ), IsDiscrete V → IsDiscrete V₁ → IsDiscrete V₂ →
      HasType (h ▸ K) (h ▸ W) V → Emb V (MemInd2 (tw V₁ z₁) (tw V₂ z₂)) →
      (∃ K' ∈ Θb r, ∃ W' ∈ Ωb r, HasType K' W' V₁) ∧ (∃ K' ∈ Θb s, ∃ W' ∈ Ωb s, HasType K' W' V₂))
    (hIH : ∀ M < N, ∀ W' ∈ Ωb M, ∀ K' ∈ Θb M, Seq M W' K' Ω Θ)
    {R : ℝ} (hRep : RepAll E) {V : ℕ → Submodule ℂ (Sm E N)}
    (hVd : ∀ k, IsDiscrete (V k)) (hVt : ∀ k, HasType K W (V k)) (hVb : ∀ k, InfBdd R (V k))
    (hex : ∀ k, ∃ r, 0 < r ∧ r < N ∧ (ExpV r (V k)).Nonempty)
    (hsmall : ∀ ε > 0, ∀ᶠ k in atTop, ¬ Gap ε (V k)) : Concl Ω Θ V := by
  choose r c lam hr hrN hc hlam hpc hbd using
    fun k => PAscAll.exists_extremal (expFin_of dict_holds finTr_holds) expNeg_holds (V k) (hVd k) (hex k)
  have hlam0 : Tendsto lam atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun k => ha.trans (hlam k), fun a ha => ?_⟩
    filter_upwards [hsmall a ha] with k hk
    by_contra hle
    exact hk (gap_of_le (hbd k) (not_lt.1 hle))
  obtain ⟨r₀, hr₀N, σ₁, hσ₁, hσ₁r⟩ := exists_subseq_const (Set.finite_Iio N) r hrN
  have hr₀ : 0 < r₀ := hσ₁r 0 ▸ hr (σ₁ 0)
  have hr₀N' : r₀ < N := hr₀N
  obtain ⟨s, rfl⟩ : ∃ s, N = r₀ + s := ⟨N - r₀, by omega⟩
  have hs : 0 < s := by omega
  have hc' : ∀ k, c (σ₁ k) ∈ ExpV r₀ (V (σ₁ k)) := fun k => hσ₁r k ▸ hc (σ₁ k)
  have hpc' : ∀ k, pE E (r₀ + s) r₀ (c (σ₁ k)) = -lam (σ₁ k) * (r₀ * s) := fun k => by
    have h := hpc (σ₁ k)
    rw [hσ₁r k] at h
    rw [h]; push_cast; ring
  have hblk : ∀ k, ∃ (V₁ : Submodule ℂ (Sm E r₀)) (V₂ : Submodule ℂ (Sm E s)), IsDiscrete V₁ ∧ IsDiscrete V₂ ∧
      Emb (V (σ₁ k)) (MemInd2 (tw V₁ (c (σ₁ k) / (r₀ * (Module.finrank ℚ E : ℂ))))
        (tw V₂ (-c (σ₁ k) / (s * (Module.finrank ℚ E : ℂ))))) := fun k => by
    obtain ⟨T, hT⟩ := slice_of dict_holds finTr_holds E r₀ s hr₀ hs (V (σ₁ k)) (hVd _) _ (hc' k)
    have hL2 := chord_of expTw_holds sqIntCrit_holds E r₀ s hr₀ hs (V (σ₁ k)) _ T (lam (σ₁ k)) (hlam _) hT
      (hpc' k) (hbd (σ₁ k))
    exact proj_of pr_holds sliceTens_holds indMap_holds E r₀ s hr₀ hs (V (σ₁ k)) (hVd _) _ _ _ T hT hL2
  choose V₁ V₂ hV₁ hV₂ hemb using hblk
  let w₁ : ℕ → ℂ := fun k => c (σ₁ k) / (r₀ * (Module.finrank ℚ E : ℂ)) - (s : ℂ) / 2
  let w₂ : ℕ → ℂ := fun k => -c (σ₁ k) / (s * (Module.finrank ℚ E : ℂ)) + (r₀ : ℂ) / 2
  have hre : ∀ k, (w₁ k).re = -(s * lam (σ₁ k)) ∧ (w₂ k).re = r₀ * lam (σ₁ k) := fun k => re_twists hr₀ hs (hpc' k)
  obtain ⟨C₁, hC₁⟩ := hTB E r₀
  obtain ⟨C₂, hC₂⟩ := hTB E s
  have hbb := fun k => block_bound hr₀ hs (hVd (σ₁ k)) (hV₁ k) (hV₂ k) (hemb k) (hVb _) (hC₁ ·) (hC₂ ·)
  have hty := fun k => hBTK r₀ s rfl (V (σ₁ k)) (V₁ k) (V₂ k) _ _ (hVd _) (hV₁ k) (hV₂ k) (hVt _) (hemb k)
  choose K₁ hK₁ W₁ hW₁ hT₁ using fun k => (hty k).1
  choose K₂ hK₂ W₂ hW₂ hT₂ using fun k => (hty k).2
  obtain ⟨⟨⟨⟨a₁, b₁⟩, a₂⟩, b₂⟩, hmem, σ₂, hσ₂, hσ₂e⟩ :=
    exists_subseq_const ((((hΘb r₀).1.prod (hΩb r₀).1).prod (hΘb s).1).prod (hΩb s).1)
      (fun k => (((K₁ k, W₁ k), K₂ k), W₂ k)) (fun k => ⟨⟨⟨hK₁ k, hW₁ k⟩, hK₂ k⟩, hW₂ k⟩)
  simp only [Prod.mk.injEq] at hσ₂e
  obtain ⟨⟨⟨ma₁, mb₁⟩, ma₂⟩, mb₂⟩ := hmem
  obtain ⟨a, -, σ₃, hσ₃, ha⟩ := tendsto_subseq_of_bounded (x := fun j => (w₁ (σ₂ j), w₂ (σ₂ j)))
    (Metric.isBounded_closedBall (x := (0 : ℂ × ℂ)) (r := max (R + |C₁|) (R + |C₂|)))
    (fun j => by
      rw [mem_closedBall_zero_iff, Prod.norm_def]
      exact max_le_max (hbb _).1 (hbb _).2.1)
  let κ : ℕ → ℕ := fun j => σ₂ (σ₃ j)
  have hκ : StrictMono κ := hσ₂.comp hσ₃
  have ha₁ : Tendsto (fun j => w₁ (κ j)) atTop (𝓝 a.1) := (continuous_fst.tendsto a).comp ha
  have ha₂ : Tendsto (fun j => w₂ (κ j)) atTop (𝓝 a.2) := (continuous_snd.tendsto a).comp ha
  have hlamκ : Tendsto (fun j => lam (σ₁ (κ j))) atTop (𝓝 0) := hlam0.comp (hσ₁.comp hκ).tendsto_atTop
  have hre₁ : a.1.re = 0 := by
    have h1 : Tendsto (fun j => (w₁ (κ j)).re) atTop (𝓝 a.1.re) := (Complex.continuous_re.tendsto _).comp ha₁
    have h2 : Tendsto (fun j => (w₁ (κ j)).re) atTop (𝓝 0) := by
      have e : (fun j => (w₁ (κ j)).re) = fun j => -(s : ℝ) * lam (σ₁ (κ j)) := funext fun j => by
        rw [(hre (κ j)).1]; ring
      rw [e]; simpa using hlamκ.const_mul (-(s : ℝ))
    exact tendsto_nhds_unique h1 h2
  have hre₂ : a.2.re = 0 := by
    have h1 : Tendsto (fun j => (w₂ (κ j)).re) atTop (𝓝 a.2.re) := (Complex.continuous_re.tendsto _).comp ha₂
    have h2 : Tendsto (fun j => (w₂ (κ j)).re) atTop (𝓝 0) := by
      have e : (fun j => (w₂ (κ j)).re) = fun j => (r₀ : ℝ) * lam (σ₁ (κ j)) := funext fun j => (hre (κ j)).2
      rw [e]; simpa using hlamκ.const_mul (r₀ : ℝ)
    exact tendsto_nhds_unique h1 h2
  obtain ⟨φ₁, t₁, t₁₀, hφ₁, hp₁₀, hz₁₀, hp₁, hs₁, hl₁, htw₁, he₁⟩ :=
    hIH r₀ (by omega) b₁ mb₁ a₁ ma₁ (2 * R + |C₁|) hr₀ hRep (fun j => V₁ (κ j)) (fun j => hV₁ _)
      (fun j => by
        have e := hσ₂e (σ₃ j)
        rw [← e.1.1.1, ← e.1.1.2]
        exact hT₁ _)
      (fun j => (hbb _).2.2.1)
  obtain ⟨φ₂, t₂, t₂₀, hφ₂, hp₂₀, hz₂₀, hp₂, hs₂, hl₂, htw₂, he₂⟩ :=
    hIH s (by omega) b₂ mb₂ a₂ ma₂ (2 * R + |C₂|) hs hRep (fun j => V₂ (κ (φ₁ j))) (fun j => hV₂ _)
      (fun j => by
        have e := hσ₂e (σ₃ (φ₁ j))
        rw [← e.1.2, ← e.2]
        exact hT₂ _)
      (fun j => (hbb _).2.2.2)
  have hL₁ : ∀ j, (t₁ j).twists.length = t₁₀.twists.length := fun j => length_twists_of_strip (hs₁ j)
  have hL₂ : ∀ j, (t₂ j).twists.length = t₂₀.twists.length := fun j => length_twists_of_strip (hs₂ j)
  have hφ₁₂ : StrictMono fun j => φ₁ (φ₂ j) := hφ₁.comp hφ₂
  refine ⟨fun j => σ₁ (κ (φ₁ (φ₂ j))),
    fun j => .node ((t₁ (φ₂ j)).shift (w₁ (κ (φ₁ (φ₂ j))))) ((t₂ j).shift (w₂ (κ (φ₁ (φ₂ j))))),
    .node (t₁₀.shift a.1) (t₂₀.shift a.2), hσ₁.comp (hκ.comp hφ₁₂), ⟨pos_shift _ hp₁₀, pos_shift _ hp₂₀⟩, ?_,
    fun j => ⟨pos_shift _ (hp₁ _), pos_shift _ (hp₂ _)⟩, fun j => ?_,
    ⟨allLeaves_shift _ hl₁, allLeaves_shift _ hl₂⟩, fun i => ?_, fun j => ?_⟩
  · intro z hz
    simp only [Tr.twists, twists_shift, List.mem_append, List.mem_map] at hz
    rcases hz with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · simp [hz₁₀ y hy, hre₁]
    · simp [hz₂₀ y hy, hre₂]
  · simp only [Tr.strip, strip_shift, hs₁, hs₂]
  · simp only [Tr.twists, twists_shift, getD_append, getD_map_add, List.length_map, hL₁, hL₂]
    split_ifs with h1 h2
    · exact ((htw₁ i).comp hφ₂.tendsto_atTop).add (ha₁.comp hφ₁₂.tendsto_atTop)
    · exact (htw₂ (i - t₁₀.twists.length)).add (ha₂.comp hφ₁₂.tendsto_atTop)
    · exact tendsto_const_nhds
  · have hN := hNE E r₀ s (V (σ₁ (κ (φ₁ (φ₂ j))))) (V₁ (κ (φ₁ (φ₂ j)))) (V₂ (κ (φ₁ (φ₂ j)))) _ _ (hVd _) (hemb _)
    refine emb_trans hN ?_
    refine hG E r₀ s _ _ _ _ (ParabolicProjection.isStable_tw (hV₁ _).stable _)
      (hTr E r₀ _ (allLeaves_shift _ (stable_of_pos (hp₁ _)))) (ParabolicProjection.isStable_tw (hV₂ _).stable _)
      (hTr E s _ (allLeaves_shift _ (stable_of_pos (hp₂ _)))) ?_ ?_
    · exact hTS E r₀ (V₁ (κ (φ₁ (φ₂ j)))) (t₁ (φ₂ j)) _ (hV₁ _).stable (he₁ (φ₂ j))
    · exact hTS E s (V₂ (κ (φ₁ (φ₂ j)))) (t₂ j) _ (hV₂ _).stable (he₂ j)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5

end
