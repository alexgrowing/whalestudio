import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MopBase
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem one_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) : (1 : R) ∈ entMon r 0 :=
  ⟨[], rfl, rfl⟩

private theorem mul_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) {i j : ℤ} {a b : R}
    (ha : a ∈ entMon r i) (hb : b ∈ entMon r j) : a * b ∈ entMon r (i + j) := by
  obtain ⟨L, rfl, rfl⟩ := ha
  obtain ⟨M, rfl, rfl⟩ := hb
  exact ⟨L ++ M, by simp, by simp⟩

private theorem mat_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (g : G) (a b : Fin 3) :
    (r g).mat a b ∈ entMon r (wt1 a - wt1 b) :=
  ⟨[(g, a, b)], by simp [wt], by simp⟩

private theorem theta_left {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (c : G)
    (h1 : (r c).right = -1) (h2 : (r c).mat = 1) (g : G) :
    (theta (r g).left : Matrix (Fin 3) (Fin 3) R) = (r (c * g)).mat := by
  have h : (r c).left = 1 := Units.ext h2
  rw [map_mul, GG.mat, SemidirectProduct.mul_left, h, h1, one_mul, sgnAct_neg_one]

private theorem emb_mem {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] (r : G →* GG 3 R) (c : G)
    (h1 : (r c).right = -1) (h2 : (r c).mat = 1) (g : G) (a b : Fin 3 ⊕ Fin 3) :
    emb (r g) a b ∈ Submodule.span O (entMon r (wt6 a - wt6 b)) := by
  rw [emb_apply, theta_left r c h1 h2]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;>
    first
    | exact Submodule.zero_mem _
    | exact Submodule.subset_span (mat_mem_entMon r _ a b)

theorem UpperTheory.exists_span_entMon_approx_of_mem_wtPart :
    ∀ {O G R σ : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] [Finite σ] (η : G →* ℤˣ) (Ψ : G →* Oˣ) (r : G →* GG 3 R) (c : G),
          (r c).right = -1 → (r c).mat = 1 → ∀ (w : σ → ℤ) (Φ : MvPowerSeries σ O →ₐ[O] R) (m : Ideal R), (∀ s, Φ (MvPowerSeries.X s) ∈ m) →
          (∀ s, ∃ g a b, w s = wt6 a - wt6 b ∧ Φ (MvPowerSeries.X s) = emb (r g) a b - algebraMap O R (emb (r0 η Ψ g) a b)) →
          ∀ j, ∀ F ∈ wtPart O w j, ∀ n : ℕ, ∃ y ∈ Submodule.span O (entMon r j), Φ F - y ∈ m ^ n := by
  intro O G R σ _ _ _ _ _ η Ψ r c h1 h2 w Φ m hm hX j F hF n
  refine approx w Φ m (fun j => Submodule.span O (entMon r j))
    (Submodule.subset_span (one_mem_entMon r)) ?_ hm ?_ j F hF n
  · intro i j a ha b hb
    have h := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact mul_mem_entMon r hx hy
  · intro s
    obtain ⟨g, a, b, hw, he⟩ := hX s
    rw [hw, he]
    refine Submodule.sub_mem _ (emb_mem r c h1 h2 g a b) ?_
    by_cases h : wt6 a = wt6 b
    · rw [h, sub_self, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (one_mem_entMon r))
    · rw [unitaryEmbedding_residualRep_eq_zero_of_weight_ne η Ψ g a b h, map_zero]
      exact Submodule.zero_mem _
