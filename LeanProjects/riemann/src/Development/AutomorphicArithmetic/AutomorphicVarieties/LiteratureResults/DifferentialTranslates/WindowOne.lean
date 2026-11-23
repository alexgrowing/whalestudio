import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

open Set Topology Filter

namespace UpperTheory.V.Lit.Dr

private theorem exists_compact_open_exhaustion_of_isOpen {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Y : Set V) (hY : IsOpen Y) :
    ∃ K O : ℕ → Set V, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ Y) ∧ (∀ n, IsOpen (O n)) ∧
      (∀ n, K n ⊆ O n) ∧ (∀ n, O n ⊆ K (n+1)) ∧ ∀ p ∈ Y, ∃ n, p ∈ K n := by
  refine ⟨fun n => Metric.closedBall (0:V) n \ Metric.thickening (1/((n:ℝ)+1)) Yᶜ,
    fun n => Metric.ball (0:V) ((n:ℝ)+1) \ Metric.cthickening (1/((n:ℝ)+2)) Yᶜ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (isCompact_closedBall _ _).diff Metric.isOpen_thickening
  · intro n x hx
    dsimp only at hx
    by_contra h
    exact hx.2 (Metric.self_subset_thickening (by positivity) _ h)
  · intro n
    exact Metric.isOpen_ball.sdiff Metric.isClosed_cthickening
  · intro n x hx
    dsimp only at hx ⊢
    refine ⟨?_, fun h => hx.2 (Metric.cthickening_subset_thickening' (by positivity)
      (one_div_lt_one_div_of_lt (by positivity) (by linarith)) _ h)⟩
    have h1 := hx.1
    rw [Metric.mem_closedBall] at h1
    rw [Metric.mem_ball]
    linarith
  · intro n x hx
    dsimp only at hx ⊢
    refine ⟨?_, fun h => hx.2 (Metric.thickening_subset_cthickening _ _ ?_)⟩
    · have h1 := hx.1
      rw [Metric.mem_ball] at h1
      rw [Metric.mem_closedBall]
      push_cast
      linarith
    · have e : (((n+1 : ℕ) : ℝ) + 1) = (n:ℝ) + 2 := by push_cast; ring
      rw [e] at h
      exact h
  · intro p hp
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hY p hp
    obtain ⟨n, hn⟩ := exists_nat_gt (max ‖p‖ (1/ε))
    refine ⟨n, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (le_max_left _ _).trans hn.le
    · rw [Metric.mem_thickening_iff]
      rintro ⟨y, hy, hd⟩
      apply hy
      apply hb
      rw [Metric.mem_ball, dist_comm]
      refine hd.trans ?_
      have h1 : 1/ε < n := (le_max_right _ _).trans_lt hn
      rw [div_lt_iff₀ hε] at h1
      rw [div_lt_iff₀ (by positivity)]
      nlinarith

theorem windowOne : WindowOne := by
  intro Γ V S _ _ _ _ d G hS hP
  rcases isEmpty_or_nonempty S with hE | ⟨⟨s₀⟩⟩
  · exact ⟨fun _ => ∅, fun s => isEmptyElim s, fun s => isEmptyElim s, fun s => isEmptyElim s⟩
  have hmul : ∀ (a b : Γ) (x : V), G.ρ (a * b) x = G.ρ a (G.ρ b x) := fun a b x => by
    rw [map_mul, ContinuousLinearMap.mul_apply]
  have hfin : ∀ K ⊆ G.Y, IsCompact K → {γ : Γ | ∃ p ∈ K, G.ρ γ p ∈ K}.Finite := fun K hK hKc =>
    (hP K hK hKc s₀ s₀).subset (fun γ h => ⟨Subsingleton.elim _ _, h⟩)
  have hball : ∀ p ∈ G.Y, ∃ r > 0, Metric.closedBall p r ⊆ G.Y := by
    intro p hp
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp G.isOpen p hp
    exact ⟨ε/2, half_pos hε, (Metric.closedBall_subset_ball (half_lt_self hε)).trans hb⟩
  have hsat : ∀ C ⊆ G.Y, IsCompact C → ∀ p ∈ G.Y, (¬ ∃ γ, G.ρ γ p ∈ C) →
      ∀ᶠ x in 𝓝 p, ¬ ∃ γ, G.ρ γ x ∈ C := by
    intro C hC hCc p hp hn
    obtain ⟨r, hr, hrY⟩ := hball p hp
    have hF := hfin _ (Set.union_subset hrY hC) ((isCompact_closedBall p r).union hCc)
    have h1 : ∀ᶠ x in 𝓝 p, x ∈ Metric.closedBall p r := Metric.closedBall_mem_nhds p hr
    have h2 : ∀ᶠ x in 𝓝 p, ∀ γ ∈ {γ : Γ | ∃ q ∈ Metric.closedBall p r ∪ C,
        G.ρ γ q ∈ Metric.closedBall p r ∪ C}, G.ρ γ x ∉ C := by
      rw [Filter.eventually_all_finite hF]
      intro γ _
      have ho : IsOpen ((G.ρ γ) ⁻¹' C)ᶜ := (hCc.isClosed.preimage (G.ρ γ).continuous).isOpen_compl
      exact ho.mem_nhds (fun h => hn ⟨γ, h⟩)
    filter_upwards [h1, h2] with x hx1 hx2
    rintro ⟨γ, hγ⟩
    exact hx2 γ ⟨x, Or.inl hx1, Or.inr hγ⟩ hγ
  obtain ⟨K, O, hKc, hKY, hOo, hKO, hOK, hcov⟩ := exists_compact_open_exhaustion_of_isOpen G.Y G.isOpen
  have hmono : Monotone K := monotone_nat_of_le_succ (fun n => (hKO n).trans (hOK n))
  have hOY : ∀ n, O n ⊆ G.Y := fun n => (hOK n).trans (hKY (n+1))
  have hmin : ∀ p ∈ G.Y, ∃ n γ, G.ρ γ p ∈ K n ∧ ∀ m < n, ¬ ∃ γ, G.ρ γ p ∈ K m := by
    intro p hp
    classical
    have hx : ∃ n, ∃ γ, G.ρ γ p ∈ K n := by
      obtain ⟨n, hn⟩ := hcov p hp
      exact ⟨n, 1, by rwa [map_one, ContinuousLinearMap.one_apply]⟩
    obtain ⟨γ, hγ⟩ := Nat.find_spec hx
    exact ⟨Nat.find hx, γ, hγ, fun m hm => Nat.find_min hx hm⟩
  let W0 : Set V := ⋃ n, {q | q ∈ O n ∧ ∀ m < n, ¬ ∃ γ, G.ρ γ q ∈ K m}
  refine ⟨fun _ => W0, fun s => ⟨?_, ?_⟩, fun s p hp => ?_, fun s p hp => ?_⟩
  · show IsOpen W0
    rw [isOpen_iff_mem_nhds]
    intro q hq
    obtain ⟨n, hqn⟩ := Set.mem_iUnion.mp hq
    have hq' : q ∈ O n ∧ ∀ m < n, ¬ ∃ γ, G.ρ γ q ∈ K m := hqn
    have hA : ∀ᶠ x in 𝓝 q, x ∈ O n := (hOo n).mem_nhds hq'.1
    have hB : ∀ᶠ x in 𝓝 q, ∀ m ∈ Set.Iio n, ¬ ∃ γ, G.ρ γ x ∈ K m := by
      rw [Filter.eventually_all_finite (Set.finite_Iio n)]
      intro m hm
      exact hsat (K m) (hKY m) (hKc m) q (hOY n hq'.1) (hq'.2 m hm)
    filter_upwards [hA, hB] with x hx1 hx2
    exact Set.mem_iUnion.mpr ⟨n, hx1, fun m hm => hx2 m hm⟩
  · show W0 ⊆ G.Y
    exact Set.iUnion_subset (fun n q hq => hOY n hq.1)
  · obtain ⟨n, γ, hγ, hm⟩ := hmin p hp
    refine ⟨γ⁻¹, ?_⟩
    show G.ρ γ⁻¹⁻¹ p ∈ W0
    rw [inv_inv]
    exact Set.mem_iUnion.mpr ⟨n, hKO n hγ, fun m hm' ⟨δ, hδ⟩ => hm m hm' ⟨δ * γ, by rw [hmul]; exact hδ⟩⟩
  · obtain ⟨n, γ, hγ, -⟩ := hmin p hp
    obtain ⟨r, hr, hrY⟩ := hball p hp
    have hF := hfin _ (Set.union_subset hrY (hKY (n+2))) ((isCompact_closedBall p r).union (hKc (n+2)))
    refine ⟨Metric.closedBall p r ∩ (G.ρ γ) ⁻¹' (O n),
      Filter.inter_mem (Metric.closedBall_mem_nhds p hr)
        (((hOo n).preimage (G.ρ γ).continuous).mem_nhds (hKO n hγ)), ?_⟩
    refine (hF.preimage (f := fun g : Γ => g⁻¹) (fun _ _ _ _ h => inv_injective h)).subset ?_
    rintro δ ⟨x, ⟨hx1, hx2⟩, hxW⟩
    obtain ⟨k, hk1, hk2⟩ := Set.mem_iUnion.mp hxW
    have hkn : k ≤ n + 1 := by
      by_contra hlt
      push_neg at hlt
      refine hk2 (n+1) hlt ⟨γ * δ, ?_⟩
      rw [hmul, ← hmul δ δ⁻¹ x, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
      exact hOK n hx2
    exact ⟨x, Or.inl hx1, Or.inr (hmono (by omega : k + 1 ≤ n + 2) (hOK k hk1))⟩

end UpperTheory.V.Lit.Dr
