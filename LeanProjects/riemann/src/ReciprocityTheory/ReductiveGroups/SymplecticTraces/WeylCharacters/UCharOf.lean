import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Statement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.BranchModel
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS.S7

theorem uChar_of (hS : SqCharStatement) : UCharStatement := by
  intro N Λ _ T k t hk
  obtain ⟨σ, hσk, hU, hK⟩ := ReciprocityTheory.ChartRestriction.DS.HW.KType.exists_rep T
  obtain ⟨lam, hlam, e, he⟩ :=
    ReciprocityTheory.ChartRestriction.DS.HW.model_equiv N (fun a => (Λ a : ℝ)) T.V σ ⊤ hU hK
  have hw : lam.w = Λ := by
    funext a
    exact_mod_cast (hlam a).symm
  let g : GL (Fin N) ℂ := ReciprocityTheory.ChartRestriction.DS.HW.torepUnit _ k.2
  have hg : (g : Matrix (Fin N) (Fin N) ℂ) = Matrix.diagonal t := hk
  obtain ⟨f, hf, htr⟩ := hS N lam g t hg
  let e' : T.V ≃ₗ[ℂ] Formalism.BasicNotions.nablaSq ℂ N lam := Submodule.topEquiv.symm.trans e
  have hconj : f = e'.conj ((T.op k : T.V →L[ℂ] T.V) : T.V →ₗ[ℂ] T.V) := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    have hz := he g k.2 (e.symm y)
    rw [LinearEquiv.apply_symm_apply] at hz
    rw [hf y, ← hz, ← hσk k]
    rfl
  have hk' : kChar T k = LinearMap.trace ℂ _ f := by
    rw [hconj, LinearMap.trace_conj']
    rfl
  rw [hk', htr, hw]

end ReciprocityTheory.ChartRestriction.TR.Weyl
