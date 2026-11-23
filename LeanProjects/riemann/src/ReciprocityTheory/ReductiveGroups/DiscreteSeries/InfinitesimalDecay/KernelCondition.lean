import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.SigLamSmoothOfGenSub
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.KFiniteVectorsInGeneratedSubmodule

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem exists_kfin_near {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))) (hWs : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X)
    (u : Hlam ε Ψ v₀) (hu : IsSmoothVecU ε (sigLam ε Ψ v₀) u) {e : ℝ} (he : 0 < e) :
    ∃ x : Hlam ε Ψ v₀, Formalism.MainNotions.S.IsKFin ε (sigLam ε Ψ v₀) x ∧ nuJ (sigLam ε Ψ v₀) Ws (u - x) < e := by
  have := S7.compactSpace_KG ε
  have : MeasureTheory.IsFiniteMeasure (S7.muK ε) := by unfold S7.muK; infer_instance
  have : (S7.muK ε).IsOpenPosMeasure := by unfold S7.muK; infer_instance
  have hσ : IsURepOn (UJset ε) (sigLam ε Ψ v₀) := sigLam_isURepOn hgap hP hv₀
  have hWg : ∀ i : Fin Ws.length, ∀ X ∈ Ws.get i, inG ε X := fun i => hWs _ (List.get_mem Ws i)
  obtain ⟨α, hα, hαF⟩ := approx_id (S7.muK ε) (finAlg_sep_KG ε)
    (fun (i : Fin Ws.length) (k : S7.KG ε) => dSW (sigLam ε Ψ v₀) (Ws.get i) (sigLam ε Ψ v₀ (S7.toMK k) u))
    (fun i => continuous_dSW_orbit hσ (hWg i) hu) (δ := e / (Ws.length + 1)) (by positivity)
  obtain ⟨x, hxdef⟩ : ∃ x : Hlam ε Ψ v₀, x = ∫ k, α k • sigLam ε Ψ v₀ (S7.toMK k) u ∂(S7.muK ε) := ⟨_, rfl⟩
  have hK : Formalism.MainNotions.S.IsKFin ε (sigLam ε Ψ v₀) x := by rw [hxdef]; exact kfin_integral hσ u hα
  obtain ⟨y, -, hyx⟩ := kfin_mem_genSub hlam hgap hP hv₀ x hK
  have hxs : IsSmoothVecU ε (sigLam ε Ψ v₀) x := by
    have hyH : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀ := by rw [hyx]; exact x.2
    have h := sigLam_smooth_of_genSub (Ψ := Ψ) (v₀ := v₀) hyH
    rwa [show (⟨(y : L2 ε), hyH⟩ : Hlam ε Ψ v₀) = x from Subtype.ext hyx] at h
  refine ⟨x, hK, ?_⟩
  have hterm : ∀ w ∈ Ws, ‖dSW (sigLam ε Ψ v₀) w (u - x)‖ ≤ e / (Ws.length + 1) := by
    intro w hw
    obtain ⟨i, rfl⟩ := List.get_of_mem hw
    have hxs' : IsSmoothVecU ε (sigLam ε Ψ v₀) (∫ k, α k • sigLam ε Ψ v₀ (S7.toMK k) u ∂(S7.muK ε)) := by
      rw [← hxdef]; exact hxs
    rw [dSW_sub hσ (hWg i) hu hxs, hxdef]
    erw [dSW_integral hσ (fun z hz => sigLam_sep z hz) (hWg i) hu α hxs']
    rw [norm_sub_rev]
    have h1 : sigLam ε Ψ v₀ (S7.toMK (1 : S7.KG ε)) u = u := by
      rw [show S7.toMK (1 : S7.KG ε) = 1 from rfl, hσ.1.1]
      rfl
    have h2 := hαF i
    beta_reduce at h2
    rw [h1] at h2
    exact h2.le
  unfold nuJ
  calc (Ws.map fun w => ‖dSW (sigLam ε Ψ v₀) w (u - x)‖).sum
      ≤ (Ws.map fun w => ‖dSW (sigLam ε Ψ v₀) w (u - x)‖).length • (e / (Ws.length + 1)) :=
        List.sum_le_card_nsmul _ _ fun r hr => by
          obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
          exact hterm w hw
    _ = (Ws.length : ℝ) * (e / (Ws.length + 1)) := by rw [List.length_map, nsmul_eq_mul]
    _ < e := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end ReciprocityTheory.ChartRestriction.DS.DecInf
