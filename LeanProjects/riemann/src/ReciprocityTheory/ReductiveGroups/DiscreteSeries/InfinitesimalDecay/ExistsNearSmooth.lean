import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.KernelCondition
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.KFiniteVectorsInGeneratedSubmodule

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem exists_near_smooth {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))) (hWs : ∀ w ∈ Ws, ∀ X ∈ w, inG ε X)
    (u : Hlam ε Ψ v₀) (hu : IsSmoothVecU ε (sigLam ε Ψ v₀) u) {e : ℝ} (he : 0 < e) :
    ∃ x ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      ∃ hx : ((x : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀,
        nuJ (sigLam ε Ψ v₀) Ws (u - ⟨((x : smD ε (rreg ε)) : L2 ε), hx⟩) < e := by
  obtain ⟨x, hxK, hxe⟩ := exists_kfin_near hlam hgap hP hv₀ Ws hWs u hu he
  obtain ⟨y, hy, hyx⟩ := kfin_mem_genSub hlam hgap hP hv₀ x hxK
  have hyH : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀ := by rw [hyx]; exact x.2
  refine ⟨y, hy, hyH, ?_⟩
  have hxy : (⟨((y : smD ε (rreg ε)) : L2 ε), hyH⟩ : Hlam ε Ψ v₀) = x := Subtype.ext hyx
  rw [hxy]
  exact hxe

end ReciprocityTheory.ChartRestriction.DS.DecInf
