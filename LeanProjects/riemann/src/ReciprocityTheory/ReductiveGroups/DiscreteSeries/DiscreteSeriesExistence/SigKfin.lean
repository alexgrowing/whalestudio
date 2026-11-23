import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothRestrict

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem sigLam_kfin_smooth (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (x : Hlam ε Ψ v₀) (hx : x ∈ kfinLam ε Ψ v₀) :
    IsSmoothVecU ε (sigLam ε Ψ v₀) x := by

  obtain ⟨w, -, hw⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hx)
  have hsm : IsSmoothVecU ε (rreg ε) ((x : Hlam ε Ψ v₀) : L2 ε) := by
    have hw' : (w : L2 ε) = (x : L2 ε) := hw
    rw [← hw']
    exact (mem_smD_iff ε (rreg ε) _).mp w.2

  exact (isSmoothVecU_restrict (rreg_isURepOn ε) (Hlam ε Ψ v₀)
    (rreg_mem_Hlam hgap hP hv₀) x).mpr hsm

end ReciprocityTheory.ChartRestriction.DS
