import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DSWSigLamCoe

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem decBoundJ_sigLam {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (m N : ℕ)
    (hM : ∃ C : ℝ, ∀ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∀ g ∈ UJset ε,
        Real.sqrt (S7.hs g) ^ m * ‖inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε))‖ ≤
          C * NE (smE ε (rreg ε)) N x * NE (smE ε (rreg ε)) N y) :
    DecBoundJ ε (sigLam ε Ψ v₀) m N := by
  obtain ⟨C, hC⟩ := hM
  obtain ⟨Ws, C', hWs, hNE⟩ := NE_le_nuJ (rreg_isURepOn ε) N
  have hU : IsURepOn (UJset ε) (sigLam ε Ψ v₀) := sigLam_isURepOn hgap hP hv₀
  have hWsG : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X := fun w hw => (hWs w hw).2
  have hVs : ∀ w ∈ ([] :: Ws), w.length ≤ N ∧ ∀ X ∈ w, inG ε X := by
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · simp
    · exact hWs w hw
  have hVsG : ∀ w ∈ ([] :: Ws), ∀ X ∈ w, inG ε X := fun w hw => (hVs w hw).2
  have hnn : ∀ z : Hlam ε Ψ v₀, 0 ≤ nuJ (sigLam ε Ψ v₀) ([] :: Ws) z := fun z =>
    nuJ_nonneg _ _ _
  have hnorm : ∀ z : Hlam ε Ψ v₀, ‖z‖ ≤ nuJ (sigLam ε Ψ v₀) ([] :: Ws) z := by
    intro z
    rw [nuJ_cons_nil]
    linarith [nuJ_nonneg (sigLam ε Ψ v₀) Ws z]
  have hC₁ : 0 ≤ max C' 0 := le_max_right _ _
  have hK : 0 ≤ max C 0 * max C' 0 * max C' 0 :=
    mul_nonneg (mul_nonneg (le_max_right _ _) hC₁) hC₁
  have hNE' : ∀ (x : smD ε (rreg ε)) (hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀),
      NE (smE ε (rreg ε)) N x ≤
        max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) := by
    intro x hx
    have h1 := hNE x
    have h2 : nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε) =
        nuJ (sigLam ε Ψ v₀) Ws (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) :=
      nuJ_sigLam_coe hgap hP hv₀ hWsG (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀)
    have h3 := nuJ_nonneg (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε)
    have h4 : nuJ (sigLam ε Ψ v₀) ([] :: Ws) (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) =
        ‖(⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀)‖ +
          nuJ (sigLam ε Ψ v₀) Ws (⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀) :=
      nuJ_cons_nil _ _ _
    rw [h4, ← h2]
    calc NE (smE ε (rreg ε)) N x ≤ C' * nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε) := h1
      _ ≤ max C' 0 * nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h3
      _ ≤ max C' 0 * (‖(⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ : Hlam ε Ψ v₀)‖ +
            nuJ (rreg ε) Ws ((x : smD ε (rreg ε)) : L2 ε)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) hC₁
  have hfin : ∀ (x : smD ε (rreg ε)), x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) →
      ∀ (hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀),
      ∀ (y : smD ε (rreg ε)), y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) →
      ∀ (hy : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀), ∀ g ∈ UJset ε,
        Real.sqrt (S7.hs g) ^ m *
            ‖inner ℂ (⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ : Hlam ε Ψ v₀)
              (sigLam ε Ψ v₀ g ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩)‖ ≤
          max C 0 * max C' 0 * max C' 0 *
            nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ *
            nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ := by
    intro x hxg hx y hyg hy g hg
    have he : inner ℂ (⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ : Hlam ε Ψ v₀)
        (sigLam ε Ψ v₀ g ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) =
        inner ℂ ((y : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x : smD ε (rreg ε)) : L2 ε)) := by
      rw [Submodule.coe_inner, sigLam_coe hgap hP hv₀ hg]
    rw [he]
    have hb := hC x hxg y hyg g hg
    have hx0 := NE_nonneg' (smE ε (rreg ε)) N x
    have hy0 := NE_nonneg' (smE ε (rreg ε)) N y
    have hxb := hNE' x hx
    have hyb := hNE' y hy
    calc _ ≤ C * NE (smE ε (rreg ε)) N x * NE (smE ε (rreg ε)) N y := hb
      _ ≤ max C 0 * NE (smE ε (rreg ε)) N x * NE (smE ε (rreg ε)) N y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0) hy0
      _ ≤ max C 0 * (max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) *
            (max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩) := by
          have hm := le_max_right C 0
          exact mul_le_mul (mul_le_mul_of_nonneg_left hxb hm) hyb hy0
            (mul_nonneg hm (mul_nonneg hC₁ (hnn _)))
      _ = _ := by ring
  refine ⟨max C 0 * max C' 0 * max C' 0, [] :: Ws, hVs, ?_⟩
  intro u v hu hv g hg
  have hA : 0 ≤ Real.sqrt (S7.hs g) ^ m := pow_nonneg (Real.sqrt_nonneg _) _
  have hiso : ∀ z : Hlam ε Ψ v₀, ‖sigLam ε Ψ v₀ g z‖ = ‖z‖ := fun z => hU.2.1 g hg z
  have hnear : ∀ (w : Hlam ε Ψ v₀), IsSmoothVecU ε (sigLam ε Ψ v₀) w → ∀ (e : ℝ), 0 < e →
      ∃ (x : smD ε (rreg ε)) (_ : x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
        (hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀),
        ‖w - ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩‖ ≤ e ∧
        nuJ (sigLam ε Ψ v₀) ([] :: Ws) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ ≤
          nuJ (sigLam ε Ψ v₀) ([] :: Ws) w + e := by
    intro w hw e he
    obtain ⟨x, hxg, hx, hlt⟩ := exists_near_smooth hlam hgap hP hv₀ ([] :: Ws) hVsG w hw he
    refine ⟨x, hxg, hx, (hnorm _).trans hlt.le, ?_⟩
    have hxs := sigLam_smooth_of_genSub (ε := ε) (Ψ := Ψ) (v₀ := v₀) hx
    have htri := nuJ_le_add_of (sigLam ε Ψ v₀) ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ w
      (w - ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) ([] :: Ws) (by
        intro W hW
        rw [dSW_sub hU (hVsG W hW) hw hxs]
        set a := dSW (sigLam ε Ψ v₀) W w
        set b := dSW (sigLam ε Ψ v₀) W ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩
        calc ‖b‖ = ‖a - (a - b)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖a‖ + ‖a - b‖ := norm_sub_le _ _)
    linarith
  have hbound : ∀ e : ℝ, 0 < e →
      Real.sqrt (S7.hs g) ^ m * ‖inner ℂ v (sigLam ε Ψ v₀ g u)‖ ≤
        Real.sqrt (S7.hs g) ^ m * (e * ‖u‖ + (‖v‖ + e) * e) +
          max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
            (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e) := by
    intro e he
    obtain ⟨x, hxg, hx, hux, hnx⟩ := hnear u hu e he
    obtain ⟨y, hyg, hy, hvy, hny⟩ := hnear v hv e he
    set x' : Hlam ε Ψ v₀ := ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩ with hx'
    set y' : Hlam ε Ψ v₀ := ⟨((y : smD ε (rreg ε)) : L2 ε), hy⟩ with hy'
    have hsplit : inner ℂ v (sigLam ε Ψ v₀ g u) =
        inner ℂ (v - y') (sigLam ε Ψ v₀ g u) +
          (inner ℂ y' (sigLam ε Ψ v₀ g (u - x')) + inner ℂ y' (sigLam ε Ψ v₀ g x')) := by
      rw [map_sub, inner_sub_left, inner_sub_right]
      ring
    have h1 : ‖inner ℂ (v - y') (sigLam ε Ψ v₀ g u)‖ ≤ e * ‖u‖ := by
      calc _ ≤ ‖v - y'‖ * ‖sigLam ε Ψ v₀ g u‖ := norm_inner_le_norm _ _
        _ = ‖v - y'‖ * ‖u‖ := by rw [hiso]
        _ ≤ e * ‖u‖ := mul_le_mul_of_nonneg_right hvy (norm_nonneg _)
    have hy'n : ‖y'‖ ≤ ‖v‖ + e := by
      calc ‖y'‖ = ‖v - (v - y')‖ := by rw [sub_sub_cancel]
        _ ≤ ‖v‖ + ‖v - y'‖ := norm_sub_le _ _
        _ ≤ ‖v‖ + e := by linarith
    have h2 : ‖inner ℂ y' (sigLam ε Ψ v₀ g (u - x'))‖ ≤ (‖v‖ + e) * e := by
      calc _ ≤ ‖y'‖ * ‖sigLam ε Ψ v₀ g (u - x')‖ := norm_inner_le_norm _ _
        _ = ‖y'‖ * ‖u - x'‖ := by rw [hiso]
        _ ≤ (‖v‖ + e) * e := mul_le_mul hy'n hux (norm_nonneg _) (by linarith [norm_nonneg v])
    have h3 := hfin x hxg hx y hyg hy g hg
    have h3' : Real.sqrt (S7.hs g) ^ m * ‖inner ℂ y' (sigLam ε Ψ v₀ g x')‖ ≤
        max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
          (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e) := by
      refine h3.trans ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_left hnx hK) hny (hnn _)
        (mul_nonneg hK (by linarith [hnn u]))
    rw [hsplit]
    calc _ ≤ Real.sqrt (S7.hs g) ^ m * (‖inner ℂ (v - y') (sigLam ε Ψ v₀ g u)‖ +
            (‖inner ℂ y' (sigLam ε Ψ v₀ g (u - x'))‖ + ‖inner ℂ y' (sigLam ε Ψ v₀ g x')‖)) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))) hA
      _ = Real.sqrt (S7.hs g) ^ m * (‖inner ℂ (v - y') (sigLam ε Ψ v₀ g u)‖ +
            ‖inner ℂ y' (sigLam ε Ψ v₀ g (u - x'))‖) +
            Real.sqrt (S7.hs g) ^ m * ‖inner ℂ y' (sigLam ε Ψ v₀ g x')‖ := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hA) h3'
  have hlim : Filter.Tendsto (fun e : ℝ => Real.sqrt (S7.hs g) ^ m * (e * ‖u‖ + (‖v‖ + e) * e) +
        max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
          (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (max C 0 * max C' 0 * max C' 0 * nuJ (sigLam ε Ψ v₀) ([] :: Ws) u *
        nuJ (sigLam ε Ψ v₀) ([] :: Ws) v)) := by
    have hc : Continuous (fun e : ℝ => Real.sqrt (S7.hs g) ^ m * (e * ‖u‖ + (‖v‖ + e) * e) +
        max C 0 * max C' 0 * max C' 0 * (nuJ (sigLam ε Ψ v₀) ([] :: Ws) u + e) *
          (nuJ (sigLam ε Ψ v₀) ([] :: Ws) v + e)) := by
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun e he => hbound e he)

end ReciprocityTheory.ChartRestriction.DS.DecInf
