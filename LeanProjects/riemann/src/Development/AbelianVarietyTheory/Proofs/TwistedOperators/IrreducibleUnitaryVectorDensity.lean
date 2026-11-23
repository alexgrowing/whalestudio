import Mathlib
open scoped InnerProductSpace

namespace GlobalTheory

namespace IrreducibleUnitaryDensity

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

noncomputable def diag (n : ℕ) (T : H →L[ℂ] H) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => T.comp (PiLp.proj 2 (fun _ : Fin n => H) j))

@[simp] lemma diag_apply (T : H →L[ℂ] H) (x : PiLp 2 (fun _ : Fin n => H)) (j : Fin n) :
    diag n T x j = T (x j) := rfl

noncomputable def incl (j : Fin n) : H →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)

lemma incl_apply (j : Fin n) (x : H) (i : Fin n) :
    (incl j x : PiLp 2 (fun _ : Fin n => H)) i = (Pi.single j x : Fin n → H) i := rfl

lemma diag_incl (T : H →L[ℂ] H) (j : Fin n) (x : H) :
    diag n T (incl j x) = incl j (T x) := by
  ext i
  simp only [diag_apply, incl_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

lemma sum_incl (x : PiLp 2 (fun _ : Fin n => H)) : ∑ j, incl j (x j) = x := by
  ext i
  simp [incl_apply, Finset.sum_apply]

lemma comm_diag (P : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H))
    (c : Fin n → Fin n → ℂ) (hc : ∀ i j x, P (incl j x) i = c i j • x) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) : P (diag n T x) = diag n T (P x) := by
  rw [← sum_incl x]
  simp only [map_sum, diag_incl]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext i
  simp [hc]

end IrreducibleUnitaryDensity

open IrreducibleUnitaryDensity in

theorem irreducibleUnitary_density (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)) (hu : ∀ g x, ‖π g x‖ = ‖x‖)
    (hs : ∀ B : H →L[ℂ] H, (∀ g, B.comp (π g) = (π g).comp B) →
      ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ H)
    (n : ℕ) (a : Fin n → H) (Λ : Fin n → (H →L[ℂ] ℂ)) (h : ∀ g, ∑ j, Λ j (π g (a j)) = 0)
    (φ u : H) : ∑ j, ⟪φ, a j⟫_ℂ * Λ j u = 0 := by
  let a' : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 a
  let S : Submodule ℂ (PiLp 2 (fun _ : Fin n => H)) :=
    Submodule.span ℂ (Set.range fun g => diag n (π g) a')
  let W := S.topologicalClosure
  have hmul : ∀ g g' x, diag n (π g) (diag n (π g') x) = diag n (π (g * g')) x := by
    intro g g' x; ext i; simp
  have hone : ∀ x, diag n (π 1) x = x := by
    intro x; ext i; simp
  have hclos : ∀ (K : Submodule ℂ (PiLp 2 (fun _ : Fin n => H))), IsClosed (K : Set (PiLp 2 (fun _ : Fin n => H))) →
      (∀ g, diag n (π g) a' ∈ K) → W ≤ K := by
    intro K hK hg
    refine Submodule.topologicalClosure_minimal S ?_ hK
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    exact hg g
  have hgen : ∀ g, diag n (π g) a' ∈ W := fun g =>
    S.le_topologicalClosure (Submodule.subset_span ⟨g, rfl⟩)
  have hinv : ∀ g, ∀ x ∈ W, diag n (π g) x ∈ W := by
    intro g x hx
    have := hclos (W.comap (diag n (π g)).toLinearMap)
      (S.isClosed_topologicalClosure.preimage (diag n (π g)).continuous)
      (fun g' => by
        change diag n (π g) (diag n (π g') a') ∈ W
        rw [hmul]; exact hgen _) hx
    exact this
  have hinner : ∀ g (x y : H), ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    (LinearIsometry.mk (π g).toLinearMap (hu g)).inner_map_map x y
  have hinner' : ∀ g x y, ⟪diag n (π g) x, diag n (π g) y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro g x y
    simp [PiLp.inner_apply, hinner]
  have hinv' : ∀ g, ∀ x ∈ Wᗮ, diag n (π g) x ∈ Wᗮ := by
    intro g x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro w hw
    have h1 : w = diag n (π g) (diag n (π g⁻¹) w) := by rw [hmul, mul_inv_cancel, hone]
    rw [h1, hinner']
    exact hx _ (hinv _ _ hw)
  haveI : CompleteSpace W := S.isClosed_topologicalClosure.completeSpace_coe
  let P := W.starProjection
  have hP : ∀ g x, P (diag n (π g) x) = diag n (π g) (P x) := by
    intro g x
    refine Submodule.eq_starProjection_of_mem_orthogonal (hinv g _ (W.starProjection_apply_mem x)) ?_
    rw [← map_sub]
    exact hinv' g _ (W.sub_starProjection_mem_orthogonal x)
  have hblock : ∀ i j : Fin n, ∃ c : ℂ, ∀ x, P (incl j x) i = c • x := by
    intro i j
    obtain ⟨c, hc⟩ := hs ((PiLp.proj 2 (fun _ : Fin n => H) i).comp (P.comp (incl j))) (by
      intro g
      ext x
      change P (incl j (π g x)) i = π g (P (incl j x) i)
      rw [← diag_incl, hP, diag_apply])
    exact ⟨c, fun x => by simpa using congrArg (fun B : H →L[ℂ] H => B x) hc⟩
  choose c hc using hblock
  let R : H →L[ℂ] H := (innerSL ℂ φ).smulRight u
  have ha : a' ∈ W := hone a' ▸ hgen 1
  have hRa : diag n R a' ∈ W := by
    have h1 : P a' = a' := Submodule.starProjection_eq_self_iff.2 ha
    rw [← h1, ← comm_diag P c hc]
    exact W.starProjection_apply_mem _
  let L : PiLp 2 (fun _ : Fin n => H) →L[ℂ] ℂ :=
    ∑ j, (Λ j).comp (PiLp.proj 2 (fun _ : Fin n => H) j)
  have hL : ∀ x, L x = ∑ j, Λ j (x j) := by
    intro x; simp [L]
  have hker : W ≤ LinearMap.ker L.toLinearMap := by
    refine hclos _ (ContinuousLinearMap.isClosed_ker L) fun g => ?_
    change L _ = 0
    rw [hL]
    exact h g
  have h0 : L (diag n R a') = 0 := hker hRa
  rw [hL] at h0
  simpa [R, a'] using h0

end GlobalTheory
