import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KerPoint

theorem support_cv_adj_cv (hKB : KerBasic) (hCv : CvTest) (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ) (hψ : Tst ψ)
    (N : Set X.G) (hNc : IsCompact N) (hN : tsupport ψ ⊆ N) :
    Function.support (cv X.μ (adj ψ) (cv X.μ φ ψ)) ⊆ N⁻¹ * (tsupport φ * N) := by
  have hadj : Tst (adj ψ) := (hKB X ψ hψ).2.2.2.1
  have hc := hCv X φ ψ hφ hψ
  have hcc := hCv X (adj ψ) (cv X.μ φ ψ) hadj hc.1
  refine hcc.2.1.trans ?_
  have hs1 : tsupport (adj ψ) ⊆ N⁻¹ := by
    refine closure_minimal ?_ hNc.inv.isClosed
    intro z hz
    have hz' : ψ z⁻¹ ≠ 0 := by
      intro h0
      apply hz
      simp [adj, h0]
    exact Set.mem_inv.2 (hN (subset_tsupport _ hz'))
  have hs2 : tsupport (cv X.μ φ ψ) ⊆ tsupport φ * N :=
    closure_minimal (hc.2.1.trans (Set.mul_subset_mul_left hN)) (hφ.2.isCompact.mul hNc).isClosed
  exact Set.mul_subset_mul hs1 hs2

theorem inner_map_sub_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (U : H →L[ℂ] H)
    (a b k₁ k₂ : H) (δ : ℝ) (ha : ‖a - k₁‖ ≤ δ) (hb : ‖b - k₂‖ ≤ δ) :
    ‖inner ℂ a (U b) - inner ℂ k₁ (U k₂)‖ ≤ ‖U‖ * δ * (‖k₂‖ + δ) + ‖k₁‖ * ‖U‖ * δ := by
  have e : inner ℂ a (U b) - inner ℂ k₁ (U k₂) = inner ℂ (a - k₁) (U b) + inner ℂ k₁ (U (b - k₂)) := by
    simp only [inner_sub_left, inner_sub_right, map_sub]
    ring
  have hbn : ‖b‖ ≤ ‖k₂‖ + δ := by
    have := norm_add_le (b - k₂) k₂
    rw [sub_add_cancel] at this
    linarith
  have hU : 0 ≤ ‖U‖ := norm_nonneg _
  have t1 : ‖(inner ℂ (a - k₁) (U b) : ℂ)‖ ≤ ‖U‖ * δ * (‖k₂‖ + δ) := by
    calc ‖(inner ℂ (a - k₁) (U b) : ℂ)‖ ≤ ‖a - k₁‖ * ‖U b‖ := norm_inner_le_norm _ _
      _ ≤ δ * (‖U‖ * (‖k₂‖ + δ)) := by
          have h2 : ‖U b‖ ≤ ‖U‖ * (‖k₂‖ + δ) :=
            (U.le_opNorm b).trans (mul_le_mul_of_nonneg_left hbn hU)
          exact mul_le_mul ha h2 (norm_nonneg _) ((norm_nonneg _).trans ha)
      _ = ‖U‖ * δ * (‖k₂‖ + δ) := by ring
  have t2 : ‖(inner ℂ k₁ (U (b - k₂)) : ℂ)‖ ≤ ‖k₁‖ * ‖U‖ * δ := by
    calc ‖(inner ℂ k₁ (U (b - k₂)) : ℂ)‖ ≤ ‖k₁‖ * ‖U (b - k₂)‖ := norm_inner_le_norm _ _
      _ ≤ ‖k₁‖ * (‖U‖ * δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (U.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb hU)
      _ = ‖k₁‖ * ‖U‖ * δ := by ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add t1 t2)

theorem eq_zero_of_le_small {D C : ℝ} (hC : 0 ≤ C) (h : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → D ≤ δ * C) : D ≤ 0 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < min 1 (ε / (C + 1)) := lt_min one_pos (div_pos hε hC1)
  have h1 := h _ hδ (min_le_left _ _)
  have h2 : min 1 (ε / (C + 1)) * C ≤ ε := by
    calc min 1 (ε / (C + 1)) * C ≤ ε / (C + 1) * (C + 1) :=
          mul_le_mul (min_le_right _ _) (by linarith) hC (div_pos hε hC1).le
      _ = ε := by field_simp
  linarith

theorem ptEq_of : KerBasic → CvTest → OpAdj → ColOp → BumpEx → ApproxU → KerClose → VecLim → PtEq := by
  intro hKB hCv hAdj hCol hBump hAU hKC hVL X ι _ Φ₁ Φ₂ Φ T₁ T₂ U h1 h2 h hT1 hT2 hT x y i j k₁ k₂ hk1 hk2
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  have hΩ : IsCompact (N⁻¹ * (tsupport (Φ i j) * N)) := hNc.inv.mul ((h i j).2.isCompact.mul hNc)
  obtain ⟨M, hM0, hM⟩ := hKC X _ x y hΩ
  have hadj1 : ∀ a b, Tst ((fun i j => adj (Φ₁ j i)) a b : X.G → ℂ) :=
    fun a b => (hKB X _ (h1 b a)).2.2.2.1
  have hTadj := hAdj X ι Φ₁ T₁ h1 hT1
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ‖ker X.Γ (Φ i j) x y - inner ℂ k₁ (U k₂)‖ ≤
      δ * (M + ‖U‖ * (‖k₂‖ + 1) + ‖k₁‖ * ‖U‖) := by
    intro δ hδ hδ1
    obtain ⟨W₁, hW₁, hL₁⟩ := hVL X ι (fun i j => adj (Φ₁ j i)) (ContinuousLinearMap.adjoint T₁) x i k₁ δ hadj1 hTadj hk1 hδ
    obtain ⟨W₂, hW₂, hL₂⟩ := hVL X ι Φ₂ T₂ y j k₂ δ h2 hT2 hk2 hδ
    obtain ⟨W₃, hW₃, hL₃⟩ := hAU X (Φ i j) δ (h i j) hδ
    obtain ⟨ψ, hψ, hsub⟩ := hBump X (N ∩ W₁ ∩ W₂ ∩ W₃)
      (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hN1 hW₁) hW₂) hW₃)
    have sN : tsupport ψ ⊆ N := fun z hz => (hsub hz).1.1.1
    have s1 : tsupport ψ ⊆ W₁ := fun z hz => (hsub hz).1.1.2
    have s2 : tsupport ψ ⊆ W₂ := fun z hz => (hsub hz).1.2
    have s3 : tsupport ψ ⊆ W₃ := fun z hz => (hsub hz).2
    have hc := hCol X ι ψ hψ.1
    obtain ⟨v, hv⟩ := hc.1 x i
    obtain ⟨u, hu⟩ := hc.1 y j
    have e1 : inner ℂ v ((T₁ * U * T₂) u) = ker X.Γ (cv X.μ (adj ψ) (cv X.μ (Φ i j) ψ)) x y :=
      (hc.2 Φ (T₁ * U * T₂) h hT y j u hu).2 x i v hv
    have e2 : inner ℂ v ((T₁ * U * T₂) u) = inner ℂ (ContinuousLinearMap.adjoint T₁ v) (U (T₂ u)) := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      rfl
    have b1 := hL₁ ψ hψ s1 v hv
    have b2 := hL₂ ψ hψ s2 u hu
    have b3 := inner_map_sub_le U _ _ k₁ k₂ δ b1 b2
    have b4 := hM (cv X.μ (adj ψ) (cv X.μ (Φ i j) ψ)) (Φ i j) δ
      (support_cv_adj_cv hKB hCv X _ ψ (h i j) hψ.1 N hNc sN)
      (by
        intro z hz
        refine ⟨1⁻¹, Set.inv_mem_inv.2 h1N, z * 1, ⟨z, subset_tsupport _ hz, 1, h1N, rfl⟩, by simp⟩)
      (fun z => (hL₃ ψ hψ s3 z).2)
    have hsplit : ker X.Γ (Φ i j) x y - inner ℂ k₁ (U k₂) =
        (inner ℂ (ContinuousLinearMap.adjoint T₁ v) (U (T₂ u)) - inner ℂ k₁ (U k₂)) -
          (ker X.Γ (cv X.μ (adj ψ) (cv X.μ (Φ i j) ψ)) x y - ker X.Γ (Φ i j) x y) := by
      rw [← e2, e1]
      ring
    have hU : 0 ≤ ‖U‖ := norm_nonneg _
    have hk : 0 ≤ ‖k₂‖ := norm_nonneg _
    have hle : ‖U‖ * δ * (‖k₂‖ + δ) ≤ ‖U‖ * δ * (‖k₂‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hU hδ.le)
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    nlinarith [b3, b4, hle]
  have hC : 0 ≤ M + ‖U‖ * (‖k₂‖ + 1) + ‖k₁‖ * ‖U‖ := by positivity
  have := eq_zero_of_le_small hC key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end GlobalTheory.CompanionTheory.KerPoint

end
