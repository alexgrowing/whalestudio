import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ}

theorem kfin_mem_genSub {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hlam : S7.IsHCParam lam) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (x : Hlam ε Ψ v₀) (hx : Formalism.MainNotions.S.IsKFin ε (sigLam ε Ψ v₀) x) :
    ∃ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ((y : smD ε (rreg ε)) : L2 ε) = (x : L2 ε) := by
  obtain ⟨S, hSf, hxS, hSK⟩ := hx
  have h := sigLam_kfin hgap hP hv₀ S hSf hSK hxS
  simp only [kfinLam, Submodule.mem_comap, Submodule.mem_map] at h
  obtain ⟨y, hy, hyx⟩ := h
  exact ⟨y, hy, hyx⟩

end ReciprocityTheory.ChartRestriction.DS.DecInf
