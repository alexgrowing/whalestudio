import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def Pm {Λ R Γ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group Γ] (r : Γ →* M4 R) (E : Subalgebra Λ R)
    (w : ℤ × ℤ) (x : R) : Prop := ∃ e ∈ E, ∃ m ∈ mono r w, x = e * m

private theorem Pm_mem {Λ R Γ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group Γ] (r : Γ →* M4 R) (E : Subalgebra Λ R)
    {x : R} (hx : x ∈ E) : Pm r E 0 x := ⟨x, hx, 1, ⟨[], by simp, by simp⟩, by simp⟩

private theorem Pm_mul {Λ R Γ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group Γ] {r : Γ →* M4 R} {E : Subalgebra Λ R}
    {w w' : ℤ × ℤ} {x y : R} (hx : Pm r E w x) (hy : Pm r E w' y) : Pm r E (w + w') (x * y) := by
  obtain ⟨e, he, m, ⟨L, hL, rfl⟩, rfl⟩ := hx
  obtain ⟨e', he', m', ⟨L', hL', rfl⟩, rfl⟩ := hy
  refine ⟨e * e', mul_mem he he', _, ⟨L ++ L', by rw [List.map_append, List.sum_append, hL, hL'], rfl⟩, ?_⟩
  rw [List.map_append, List.prod_append]
  ring

private theorem Pm_pow {Λ R Γ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group Γ] {r : Γ →* M4 R} {E : Subalgebra Λ R}
    {w : ℤ × ℤ} {x : R} (hx : Pm r E w x) (k : ℕ) : Pm r E (k • w) (x ^ k) := by
  induction k with
  | zero => rw [zero_smul, pow_zero]; exact Pm_mem r E (one_mem E)
  | succ k ih => rw [succ_nsmul, pow_succ]; exact Pm_mul ih hx

theorem UpperTheory.V.Ws.sxZMono :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R} (E : Subalgebra Λ R), D.Graded W → mono D.r 0 ⊆ E → (∀ v i s, D.ψ v i s ∈ E) → ∀ n : W.σ →₀ ℕ, Finsupp.weight W.wt n = 0 → (n.prod fun s k => W.z s ^ k) ∈ E := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ R _ _ _ D W E hG hm hψ n hn
  have hz : ∀ s, Pm D.r E (W.wt s) (W.z s) := by
    intro s
    rcases hG.var s with ⟨g, i, j, c, h1, h2, h3⟩ | ⟨v, i, t, c, h1, h2⟩
    · have hmem : D.r g i j ∈ mono D.r (wt i j) := ⟨[(g, i, j)], by simp, by simp⟩
      by_cases hij : i = j
      · have h0 : wt i j = 0 := (wt_eq_zero i j).2 hij
        rw [h2, h1, h0]
        rw [h0] at hmem
        exact Pm_mem _ _ (sub_mem (hm hmem) (E.algebraMap_mem c))
      · rw [h2, h1, h3 hij, map_zero, sub_zero]
        exact ⟨1, one_mem E, _, hmem, (one_mul _).symm⟩
    · rw [h2, h1]
      exact Pm_mem _ _ (sub_mem (hψ v i t) (E.algebraMap_mem c))
  have key : ∀ n : W.σ →₀ ℕ, Pm D.r E (Finsupp.weight W.wt n) (n.prod fun s k => W.z s ^ k) := by
    intro n
    induction n using Finsupp.induction_linear with
    | zero => rw [map_zero, Finsupp.prod_zero_index]; exact Pm_mem _ _ (one_mem E)
    | add f g hf hg =>
      rw [map_add, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      exact Pm_mul hf hg
    | single s k =>
      rw [Finsupp.prod_single_index (h := fun s k => W.z s ^ k) (pow_zero _), Finsupp.weight_single]
      exact Pm_pow (hz s) k
  obtain ⟨e, he, m, hm', h⟩ := key n
  rw [h]
  rw [hn] at hm'
  exact mul_mem he (hm hm')
