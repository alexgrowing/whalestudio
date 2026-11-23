import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrGen

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxCoreGen :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, D.Graded W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → Algebra.adjoin (W.gr 0) (Set.range fun x : Γ × Fin 4 × Fin 4 => D'.r x.1 x.2.1 x.2.2) = ⊤ := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ R _ _ _ D W hD D' hmap
  have hr : ∀ g i j, D.r g i j = (D'.r g i j : R) := by
    subst hmap
    intro g i j
    first | rfl | simp [RD.map]
  have hψ : ∀ v i t, D.ψ v i t = (D'.ψ v i t : R) := by
    subst hmap
    intro v i t
    first | rfl | simp [RD.map]
  set S := Algebra.adjoin (W.gr 0) (Set.range fun x : Γ × Fin 4 × Fin 4 => D'.r x.1 x.2.1 x.2.2) with hS
  have hbA : ∀ b : W.gr 0, algebraMap (W.gr 0) W.A b = (b : W.A) := fun b => by first | rfl | simp
  have hgr : ∀ x : W.A, (x : R) ∈ W.part 0 → x ∈ S := by
    intro x hx
    have h := Subalgebra.algebraMap_mem S (⟨x, hx⟩ : W.gr 0)
    rwa [hbA] at h
  have hc : ∀ c : Λ, algebraMap Λ W.A c ∈ S := by
    intro c
    apply hgr
    have h0 : algebraMap Λ R c ∈ W.part 0 := by
      have := (algebraMap Λ (W.gr 0) c).2
      first
        | exact this
        | (have e : ((algebraMap Λ (W.gr 0) c : W.A) : R) = algebraMap Λ R c := by first | rfl | simp
           rw [← e]; exact this)
    first | exact h0 | simpa using h0
  have hr' : ∀ g i j, D'.r g i j ∈ S := fun g i j => Algebra.subset_adjoin ⟨(g, i, j), rfl⟩
  have hz : ∀ s, W.zA s ∈ S := by
    intro s
    rcases hD.var s with ⟨g, i, j, c, hzs, -, -⟩ | ⟨v, i, t, c, hzs, -⟩
    · have e : W.zA s = D'.r g i j - algebraMap Λ W.A c := by
        apply Subtype.ext
        show W.z s = _
        rw [hzs, hr]
        rfl
      rw [e]
      exact sub_mem (hr' g i j) (hc c)
    · have e : W.zA s = D'.ψ v i t - algebraMap Λ W.A c := by
        apply Subtype.ext
        show W.z s = _
        rw [hzs, hψ]
        rfl
      rw [e]
      refine sub_mem (hgr _ ?_) (hc c)
      rw [← hψ]
      exact hD.chr v i t
  rw [eq_top_iff]
  intro a ha0
  clear ha0
  have ha : a ∈ Algebra.adjoin Λ (↑(W.gr 0) ∪ Set.range W.zA) := by
    rw [gr_gen Λ R (ℤ × ℤ) W]
    trivial
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | ⟨s, rfl⟩
    · exact hgr x hx
    · exact hz s
  | algebraMap c => exact hc c
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy
