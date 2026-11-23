import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

theorem isDS_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : Formalism.MainNotions.S.IsDS ε lam (sigLam ε Ψ v₀) := by
  refine ⟨inferInstance, Hlam_nontrivial hgap hP hv₀, sigLam_isURepOn hgap hP hv₀, sigLam_irred hgap hP hv₀,
    sqInt_sigLam hgap hP hv₀, ⟨_, (sigLam_lowK hgap hP hv₀).1⟩, ?_⟩
  intro μ S hS
  exact (sigLam_kType_bounds hgap hP hv₀ S hS).1

end ReciprocityTheory.ChartRestriction.DS
