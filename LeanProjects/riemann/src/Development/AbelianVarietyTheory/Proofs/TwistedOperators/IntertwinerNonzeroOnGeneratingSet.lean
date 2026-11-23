import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open Matrix Formalism.REAL Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.GraphIntertwiner

theorem starProjection_comm {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Γ : Submodule ℂ E) [Γ.HasOrthogonalProjection] (s t : E →L[ℂ] E)
    (hs : ∀ u v, ⟪s u, s v⟫_ℂ = ⟪u, v⟫_ℂ) (hst : ∀ v, s (t v) = v)
    (hsΓ : ∀ v ∈ Γ, s v ∈ Γ) (htΓ : ∀ v ∈ Γ, t v ∈ Γ) (x : E) :
    Γ.starProjection (s x) = s (Γ.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal (hsΓ _ (Γ.starProjection_apply_mem x))
  rw [← map_sub, Submodule.mem_orthogonal]
  intro u hu
  rw [← hst u, hs]
  exact (Submodule.mem_orthogonal _ _).1 (Submodule.sub_starProjection_mem_orthogonal x) _ (htΓ u hu)

noncomputable def inlL (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] : H →L[ℂ] WithLp 2 (H × V) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H V).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℂ H V)

noncomputable def sumL {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (a : H →L[ℂ] H) (b : V →L[ℂ] V) :
    WithLp 2 (H × V) →L[ℂ] WithLp 2 (H × V) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H V).symm.toContinuousLinearMap.comp
    ((a.prodMap b).comp (WithLp.prodContinuousLinearEquiv 2 ℂ H V).toContinuousLinearMap)

theorem inlL_apply {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : H) :
    inlL H V x = WithLp.toLp 2 (x, 0) := rfl

theorem sumL_apply {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (a : H →L[ℂ] H) (b : V →L[ℂ] V)
    (z : WithLp 2 (H × V)) :
    sumL a b z = WithLp.toLp 2 (a z.ofLp.1, b z.ofLp.2) := rfl

theorem exists_intertwiner_of_group {n : ℕ} (G : Set (Matrix (Fin n) (Fin n) ℂ)) (h1 : 1 ∈ G)
    (hmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) (hinv : ∀ a ∈ G, ∃ b ∈ G, a * b = 1)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V))
    (hρ : IsURepOn G ρ) (hirr : IsIrredOn G ρ) (hπ : IsURepOn G π)
    (T : H →ₗ[ℂ] V) (Y₀ : Set H) (y₀ a₀ : H) (hy₀ : y₀ ∈ Y₀) (hT : T y₀ ≠ 0)
    (hco : ∀ y ∈ Y₀, ∀ g ∈ G, ⟪a₀, ρ g y⟫_ℂ = ⟪T y₀, π g (T y)⟫_ℂ) :
    ∃ B : H →L[ℂ] V, B ≠ 0 ∧ ∀ g ∈ G, ∀ x, B (ρ g x) = π g (B x) := by
  obtain ⟨⟨hρ1, hρm⟩, hρn, -⟩ := hρ
  obtain ⟨⟨hπ1, hπm⟩, hπn, -⟩ := hπ
  have hρi : ∀ g ∈ G, ∀ u v, ⟪ρ g u, ρ g v⟫_ℂ = ⟪u, v⟫_ℂ := fun g hg =>
    (LinearMap.norm_map_iff_inner_map_map (ρ g)).1 (hρn g hg)
  have hπi : ∀ g ∈ G, ∀ u v, ⟪π g u, π g v⟫_ℂ = ⟪u, v⟫_ℂ := fun g hg =>
    (LinearMap.norm_map_iff_inner_map_map (π g)).1 (hπn g hg)
  let S : Set (WithLp 2 (H × V)) :=
    {z | ∃ g ∈ G, ∃ y ∈ Y₀, z = WithLp.toLp 2 (ρ g y, π g (T y))}
  let Γ : Submodule ℂ (WithLp 2 (H × V)) := (Submodule.span ℂ S).topologicalClosure
  have hΓc : IsClosed (Γ : Set (WithLp 2 (H × V))) := Submodule.isClosed_topologicalClosure _
  have hSΓ : ∀ z ∈ S, z ∈ Γ := fun z hz =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span hz)
  have hle : ∀ K : Submodule ℂ (WithLp 2 (H × V)), IsClosed (K : Set (WithLp 2 (H × V))) →
      (∀ z ∈ S, z ∈ K) → Γ ≤ K := fun K hK hS =>
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 hS) hK
  haveI : CompleteSpace Γ := hΓc.completeSpace_coe
  have hinvt : ∀ g ∈ G, ∀ v ∈ Γ, sumL (ρ g) (π g) v ∈ Γ := by
    intro g hg
    refine hle (Γ.comap (sumL (ρ g) (π g)).toLinearMap)
      (hΓc.preimage (sumL (ρ g) (π g)).continuous) ?_
    rintro z ⟨h, hh, y, hy, rfl⟩
    refine hSΓ _ ⟨g * h, hmul g hg h hh, y, hy, ?_⟩
    rw [hρm g hg h hh, hπm g hg h hh]
    rfl
  have hcomm : ∀ g ∈ G, ∀ x, Γ.starProjection (sumL (ρ g) (π g) x)
      = sumL (ρ g) (π g) (Γ.starProjection x) := by
    intro g hg x
    obtain ⟨b, hb, hgb⟩ := hinv g hg
    refine starProjection_comm Γ _ (sumL (ρ b) (π b)) ?_ ?_ (hinvt g hg) (hinvt b hb) x
    · intro u v
      simp only [sumL_apply, WithLp.prod_inner_apply, hρi g hg, hπi g hg]
    · intro v
      have e1 : ∀ w, ρ g (ρ b w) = w := fun w => by
        have := congrArg (fun f : H →L[ℂ] H => f w) (hρm g hg b hb)
        simpa [hgb, hρ1] using this.symm
      have e2 : ∀ w, π g (π b w) = w := fun w => by
        have := congrArg (fun f : V →L[ℂ] V => f w) (hπm g hg b hb)
        simpa [hgb, hπ1] using this.symm
      simp only [sumL_apply, e1, e2]
  have hy₀Γ : WithLp.toLp 2 (y₀, T y₀) ∈ Γ := hSΓ _ ⟨1, h1, y₀, hy₀, by simp [hρ1, hπ1]⟩
  have horth : ∀ z ∈ Γ, ⟪WithLp.toLp 2 (a₀, -T y₀), z⟫_ℂ = 0 := by
    intro z hz
    have := hle (ℂ ∙ (WithLp.toLp 2 (a₀, -T y₀) : WithLp 2 (H × V)))ᗮ
      (Submodule.isClosed_orthogonal _) (by
        rintro z ⟨g, hg, y, hy, rfl⟩
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
        simp [WithLp.prod_inner_apply, hco y hy g hg]) hz
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 this
  have hinl : ∀ g, ∀ x, inlL H V (ρ g x) = sumL (ρ g) (π g) (inlL H V x) := by
    intro g x
    simp [inlL_apply, sumL_apply]
  refine ⟨(WithLp.sndL 2 ℂ H V).comp (Γ.starProjection.comp (inlL H V)), ?_, ?_⟩
  · intro hB
    have hB' : ∀ x, (Γ.starProjection (inlL H V x)).ofLp.2 = 0 := fun x =>
      congrArg (fun f : H →L[ℂ] V => f x) hB
    rcases hirr (Γ.comap (inlL H V).toLinearMap) (hΓc.preimage (inlL H V).continuous)
      (fun g hg v hv => by
        have : inlL H V (ρ g v) ∈ Γ := by rw [hinl]; exact hinvt g hg _ hv
        exact this) with hL | hL
    · have hP : Γ.starProjection (inlL H V y₀) = 0 := by
        have e : Γ.starProjection (inlL H V y₀)
            = inlL H V (Γ.starProjection (inlL H V y₀)).ofLp.1 := by
          rw [inlL_apply (Γ.starProjection (inlL H V y₀)).ofLp.1, ← hB' y₀]
        have hm : (Γ.starProjection (inlL H V y₀)).ofLp.1 ∈ Γ.comap (inlL H V).toLinearMap := by
          have := Γ.starProjection_apply_mem (inlL H V y₀)
          rw [e] at this
          exact this
        rw [hL, Submodule.mem_bot] at hm
        rw [e, hm, map_zero]
      have ho := Submodule.sub_starProjection_mem_orthogonal (K := Γ) (inlL H V y₀)
      rw [hP, sub_zero] at ho
      have h0 := (Submodule.mem_orthogonal _ _).1 ho _ hy₀Γ
      have h0' : ⟪y₀, y₀⟫_ℂ = 0 := by
        simpa only [inlL_apply, WithLp.prod_inner_apply, inner_zero_right, add_zero] using h0
      exact hT (by rw [inner_self_eq_zero.1 h0', map_zero])
    · have hm : a₀ ∈ Γ.comap (inlL H V).toLinearMap := by rw [hL]; trivial
      have h0 := horth _ hm
      have h0' : ⟪a₀, a₀⟫_ℂ = 0 := by
        have e : (inlL H V).toLinearMap a₀ = WithLp.toLp 2 (a₀, 0) := rfl
        simpa only [e, WithLp.prod_inner_apply, inner_zero_right, add_zero] using h0
      have h2 := hco y₀ hy₀ 1 h1
      rw [inner_self_eq_zero.1 h0', inner_zero_left, hπ1] at h2
      exact hT (inner_self_eq_zero.1 h2.symm)
  · intro g hg x
    show (Γ.starProjection (inlL H V (ρ g x))).ofLp.2 = π g (Γ.starProjection (inlL H V x)).ofLp.2
    rw [hinl, hcomm g hg, sumL_apply]

theorem Jm_mul_Jm {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

theorem exists_right_inv {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : g ∈ UJset ε) : ∃ b ∈ UJset ε, g * b = 1 := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have h1 : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    rw [← Jm_mul_Jm ε]
    calc (Jm ε * gᴴ * Jm ε) * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg']
  have h2 := mul_eq_one_comm.1 h1
  refine ⟨_, ?_, h2⟩
  generalize Jm ε * gᴴ * Jm ε = b at h2
  show bᴴ * Jm ε * b = Jm ε
  calc bᴴ * Jm ε * b = bᴴ * (gᴴ * Jm ε * g) * b := by rw [hg']
    _ = (g * b)ᴴ * Jm ε * (g * b) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [h2]; simp

theorem exists_intertwiner : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (UJset ε) ρ → IsIrredOn (UJset ε) ρ → IsURepOn (UJset ε) π → ∀ (T : H →ₗ[ℂ] V) (Y₀ : Set H) (y₀ a₀ : H), y₀ ∈ Y₀ → T y₀ ≠ 0 → (∀ y ∈ Y₀, ∀ g ∈ UJset ε, ⟪a₀, ρ g y⟫_ℂ = ⟪T y₀, π g (T y)⟫_ℂ) → ∃ B : H →L[ℂ] V, B ≠ 0 ∧ ∀ g ∈ UJset ε, ∀ x, B (ρ g x) = π g (B x) := by
  intro n ε H _ _ _ ρ V _ _ _ π hρ hirr hπ T Y₀ y₀ a₀ hy₀ hT hco
  refine exists_intertwiner_of_group (UJset ε) ?_ ?_ (exists_right_inv ε) H ρ V π hρ hirr hπ T Y₀ y₀ a₀
    hy₀ hT hco
  · show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  · intro a ha b hb
    have ha' : aᴴ * Jm ε * a = Jm ε := ha
    have hb' : bᴴ * Jm ε * b = Jm ε := hb
    show (a * b)ᴴ * Jm ε * (a * b) = Jm ε
    calc (a * b)ᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Jm ε := by rw [ha', hb']

end GlobalTheory.GraphIntertwiner
