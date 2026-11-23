import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearOfAdjoin
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.LaurPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.LaurDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.ScaleRD

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxNearArt :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, Φ.RUniv a D → D.Graded W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (τ : ℤ × ℤ →+ ℤ) (Q : RD Φ R'), IsNilpotent (maximalIdeal R') → Φ.Near a τ Q → ∃ f : W.A →ₐ[Λ] R', D'.map (f : W.A →+* R') = Q := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W hU hG D' hD' R' _ _ _ τ Q hnil hQ
  have hc : ∀ i j, -((∑ p : Fin 4 × Fin 4, (τ (wt p.1 p.2)).natAbs : ℕ) : ℤ) ≤ τ (wt i j) := by
    intro i j
    have h1 : (τ (wt i j)).natAbs ≤ ∑ p : Fin 4 × Fin 4, (τ (wt p.1 p.2)).natAbs :=
      Finset.single_le_sum (f := fun p : Fin 4 × Fin 4 => (τ (wt p.1 p.2)).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))
    omega
  generalize (∑ p : Fin 4 × Fin 4, (τ (wt p.1 p.2)).natAbs) = c at hc
  obtain ⟨S, _, _, _, e, he⟩ := sxLaur (Λ := Λ) hnil c
  obtain ⟨Q', hQ', hr, hψ⟩ := sxScaleRD hnil he hc hQ
  obtain ⟨F, hF, -⟩ := hU.2 S Q' hQ'
  have hFr : ∀ g i j, e (F (D.r g i j)) = HahnSeries.single (τ (wt i j)) (Q.r g i j) := by
    intro g i j
    rw [← hr, ← hF]; rfl
  have hFψ : ∀ v i s, e (F (D.ψ v i s)) = HahnSeries.single 0 (Q.ψ v i s) := by
    intro v i s
    rw [← hψ, ← hF]; rfl
  have hz : ∀ s, ∃ y, e (F (W.z s)) = HahnSeries.single (τ (W.wt s)) y := by
    intro s
    rcases hG.var s with ⟨g, i, j, x, h1, h2, h3⟩ | ⟨v, i, t, x, h1, h2⟩
    · rw [h1, h2, map_sub, map_sub, hFr, AlgHom.commutes, he.alg]
      by_cases hij : i = j
      · rw [(wt_eq_zero i j).2 hij, map_zero]
        exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
      · rw [h3 hij]
        exact ⟨Q.r g i j, by simp⟩
    · rw [h1, h2, map_sub, map_sub, hFψ, AlgHom.commutes, he.alg, map_zero]
      exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
  obtain ⟨f, hf⟩ := sxLaurDesc W he τ F (sxLaurPart W hG.max he τ F hz)
  have er : ∀ g i j, ((D'.r g i j : W.A) : R) = D.r g i j := by
    intro g i j
    rw [← hD']; rfl
  have eψ : ∀ v i s, ((D'.ψ v i s : W.A) : R) = D.ψ v i s := by
    intro v i s
    rw [← hD']; rfl
  refine ⟨f, RD.ext ?_ ?_⟩
  · ext g i j
    have hm : D'.r g i j ∈ W.gr (wt i j) := by
      show ((D'.r g i j : W.A) : R) ∈ W.part (wt i j)
      rw [er]; exact hG.ent g i j
    have h := hf _ _ hm
    rw [er, hFr] at h
    exact (HahnSeries.single_injective _ h).symm
  · funext v i
    ext s
    have hm : D'.ψ v i s ∈ W.gr 0 := by
      show ((D'.ψ v i s : W.A) : R) ∈ W.part 0
      rw [eψ]; exact hG.chr v i s
    have h := hf _ _ hm
    rw [eψ, hFψ, map_zero] at h
    exact (HahnSeries.single_injective _ h).symm
