import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SmoothSeminormAndSobolevBounds

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace PositivityTheory.CW

namespace KInvarianceAlt

theorem kinv {n : ℕ} {ε : Fin n → Bool} {k : Mx n} (hk : k ∈ Kset ε) : ∃ k' ∈ Kset ε, k' * k = 1 := by
  obtain ⟨hu, hJ⟩ := hk
  have hu' : kᴴ * k = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hu; rwa [Matrix.star_eq_conjTranspose] at this
  have hJh : (Jm ε)ᴴ = Jm ε := by
    ext i j; simp only [Jm, diagonal_conjTranspose, diagonal_apply]; split_ifs <;> simp_all
  have hJ' : kᴴ * Jm ε = Jm ε * kᴴ := by
    have h := congrArg Matrix.conjTranspose hJ
    simp only [Matrix.conjTranspose_mul, hJh] at h
    exact h.symm
  have hs' : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    have := Unitary.star_mem hu; rwa [Matrix.star_eq_conjTranspose] at this
  exact ⟨kᴴ, ⟨hs', hJ'⟩, hu'⟩

end KInvarianceAlt

theorem e1a : SmoothSeminormGrowth := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hπ i
  obtain ⟨q, N, hq, hg⟩ := hπ.growth i
  haveI : Nonempty (UJset ε) := ⟨⟨1, one_mem_UJ ε⟩⟩
  set W : Mx n → ℝ := fun g => (1 + hs g) ^ N with hWdef
  have hW : ∀ g, 0 < W g := fun g => pow_pos (by linarith [hs_nonneg g]) _
  have hWm : ∀ a b : Mx n, W (a * b) ≤ W a * W b := fun a b => by
    simp only [hWdef]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith [hs_nonneg (a * b)]) (one_add_hs_mul_le a b) N
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, ∀ x, π (a * b) x = π a (π b x) := fun a ha b hb x => by
    rw [hπ.map_mul a ha b hb]; rfl
  let f : UJset ε → Seminorm ℂ E := fun g => (Real.toNNReal (W g.1)⁻¹) • (p i).comp (π g.1 : E →ₗ[ℂ] E)
  have hf : ∀ g x, f g x = p i (π g.1 x) / W g.1 := fun g x => by
    show ((Real.toNNReal (W g.1)⁻¹ : NNReal) : ℝ) * p i (π g.1 x) = _
    rw [Real.coe_toNNReal _ (inv_nonneg.2 (hW _).le), div_eq_inv_mul]
  have hfq : ∀ g x, f g x ≤ q x := fun g x => by
    rw [hf, div_le_iff₀ (hW _), mul_comm]
    exact hg g.1 g.2 x
  have hbdd : BddAbove (Set.range f) := ⟨q, by
    rintro _ ⟨g, rfl⟩
    exact Pi.le_def.2 fun x => hfq g x⟩
  have hfb : ∀ x, BddAbove (Set.range fun g => f g x) := fun x => ⟨q x, by
    rintro _ ⟨g, rfl⟩
    exact hfq g x⟩
  set Q : Seminorm ℂ E := ⨆ g, f g with hQdef
  have hQ : ∀ x, Q x = ⨆ g, f g x := fun x => Seminorm.iSup_apply hbdd
  have hle : ∀ g x, f g x ≤ Q x := fun g x => by rw [hQ]; exact le_ciSup (hfb x) g
  have hQq : Q ≤ q := Pi.le_def.2 fun x => by rw [hQ]; exact ciSup_le fun g => hfq g x
  have h1 : ∀ g ∈ UJset ε, ∀ x, p i (π g x) ≤ W g * Q x := fun g hg x => by
    have := hle ⟨g, hg⟩ x
    rw [hf, div_le_iff₀ (hW _)] at this
    linarith
  have hKk : ∀ k ∈ Kset ε, ∀ x, Q (π k x) ≤ Q x := fun k hk x => by
    rw [hQ (π k x)]
    refine ciSup_le fun g => ?_
    have hgk : g.1 * k ∈ UJset ε := mul_mem_UJ g.2 (K_le_UJ hk)
    have := hle ⟨g.1 * k, hgk⟩ x
    rw [hf] at this ⊢
    have e : W (g.1 * k) = W g.1 := by
      simp only [hWdef, ((Formalism.REAL.hermitian_small_ball n ε).2 g.1 k hk).1]
    rw [← hmul g.1 g.2 k (K_le_UJ hk), ← e]
    exact this
  refine ⟨Q, N, Seminorm.continuous_of_le hq hQq, h1, fun h hh x => ?_, fun k hk x => ?_⟩
  · rw [hQ (π h x)]
    refine ciSup_le fun g => ?_
    rw [hf, hmul g.1 g.2 h hh x |>.symm, div_le_iff₀ (hW _)]
    calc p i (π (g.1 * h) x) ≤ W (g.1 * h) * Q x := h1 _ (mul_mem_UJ g.2 hh) x
      _ ≤ (W g.1 * W h) * Q x := mul_le_mul_of_nonneg_right (hWm _ _) (apply_nonneg _ _)
      _ = W h * Q x * W g.1 := by ring
  · refine le_antisymm (hKk k hk x) ?_
    obtain ⟨k', hk', e⟩ := KInvarianceAlt.kinv hk
    have := hKk k' hk' (π k x)
    rwa [← hmul k' (K_le_UJ hk') k (K_le_UJ hk), e, hπ.map_one] at this

end PositivityTheory.CW

end
