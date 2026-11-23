import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Arbitrary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.IsDSSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.SigLamMemLpOfNe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaFA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.SigLamKTypeBounds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataClosGenEqTop
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.LayerBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.KhwEqZeroSharp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidUniversal
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidOrth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RorthFunctionalEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.MultOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsLowK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsKfin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsAdm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.SigLamEquivData

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section One

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

variable {lam : Fin n → ℝ}

theorem lowKMultOne_of_cas (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hcas : CasOnSmooth ε lam σ)
    (S S' : Submodule ℂ H) (hS : Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S)
    (hS' : Formalism.MainNotions.S.IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S') : S = S' := by
  obtain ⟨V, hV, hV0, hVK, hc⟩ := ReciprocityTheory.ChartRestriction.DS.arb_datum hDS hcas
  obtain ⟨-, -, hσ, hirr, -⟩ := hDS
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have htop := data_closGen_eq_top hgap hσ hD hV hc hVK hirr hV0
  rw [data_lowK_eq hgap hσ hD hV hc hVK S (htop ▸ le_top) hS,
    data_lowK_eq hgap hσ hD hV hc hVK S' (htop ▸ le_top) hS']

private theorem exists_linearIsometryEquiv_of_eq_top {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (C : Submodule ℂ H) (hC : C = ⊤) : ∃ W : C ≃ₗᵢ[ℂ] H, ∀ y : C, W y = y :=
  ⟨LinearIsometryEquiv.ofSurjective C.subtypeₗᵢ
    (fun y => ⟨⟨y, by rw [hC]; exact Submodule.mem_top⟩, rfl⟩), fun _ => rfl⟩

theorem equiv_sigLam_of_cas (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hgap : StdGap ε lam) (hcas : CasOnSmooth ε lam σ)
    {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) :
    ∃ U : Hlam ε Ψ v₀ ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ x : Hlam ε Ψ v₀, U (sigLam ε Ψ v₀ g x) = σ g (U x) := by
  obtain ⟨V, hV, hV0, hVK, hc⟩ := ReciprocityTheory.ChartRestriction.DS.arb_datum hDS hcas
  obtain ⟨-, -, hσ, hirr, -⟩ := hDS
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have htop := data_closGen_eq_top hgap hσ hD hV hc hVK hirr hV0
  obtain ⟨U, hU⟩ := sigLam_equiv_data hgap hP hv₀ hσ hD hV hc hVK hV0
  obtain ⟨W, hW⟩ := exists_linearIsometryEquiv_of_eq_top _ htop
  refine ⟨U.trans W, fun g hg x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply, hW]
  exact hU g hg x

end One

private theorem exists_coe_linearIsometryEquiv_of_eq_top {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (C : Submodule ℂ H) (hC : C = ⊤) : ∃ W : C ≃ₗᵢ[ℂ] H, ∀ y : C, W y = y :=
  ⟨LinearIsometryEquiv.ofSurjective C.subtypeₗᵢ
    (fun y => ⟨⟨y, by rw [hC]; exact Submodule.mem_top⟩, rfl⟩), fun _ => rfl⟩

theorem dsUnique_of_cas {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hDS : Formalism.MainNotions.S.IsDS ε lam σ) (hcas : CasOnSmooth ε lam σ)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (hDS' : Formalism.MainNotions.S.IsDS ε lam σ')
    (hcas' : CasOnSmooth ε lam σ') :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ x : H, U (σ g x) = σ' g (U x) := by
  obtain ⟨V, hV, hV0, hVK, hc⟩ := ReciprocityTheory.ChartRestriction.DS.arb_datum hDS hcas
  obtain ⟨V', hV', hV0', hVK', hc'⟩ := ReciprocityTheory.ChartRestriction.DS.arb_datum hDS' hcas'
  obtain ⟨-, -, hσ, hirr, -⟩ := hDS
  obtain ⟨-, -, hσ', hirr', -⟩ := hDS'
  have hD := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ
  have hD' := ReciprocityTheory.ChartRestriction.DS.isDerivedOn_smE hσ'
  obtain ⟨W, hW⟩ := exists_coe_linearIsometryEquiv_of_eq_top _ (data_closGen_eq_top hgap hσ hD hV hc hVK hirr hV0)
  obtain ⟨W', hW'⟩ := exists_coe_linearIsometryEquiv_of_eq_top _ (data_closGen_eq_top hgap hσ' hD' hV' hc' hVK' hirr' hV0')
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap hσ hD hV hc hVK hV0 hσ' hD' hV' hc' hVK' hV0'
  have hWs : ∀ z : H, ((W.symm z : closGen (ReciprocityTheory.ChartRestriction.DS.smE ε σ) V) : H) = z := fun z => by
    rw [← hW]; exact W.apply_symm_apply z
  refine ⟨(W.symm.trans U).trans W', fun g hg x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply, hW']
  exact hU g hg _ _ (by rw [hWs, hWs])

end ReciprocityTheory.ChartRestriction.DS.G2
