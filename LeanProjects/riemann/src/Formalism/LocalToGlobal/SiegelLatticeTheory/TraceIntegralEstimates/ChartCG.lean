import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartC

noncomputable section

open scoped Matrix Classical
open MeasureTheory Finset NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.L2.SG.LocWSOf

namespace Formalism.L2.S.Pv.Chart

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isClosed_inN {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} := by
  have hS : ∀ (S : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ),
      IsClosed {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ x ∈ S} := fun S x =>
    S.closed_of_finiteDimensional.preimage ((continuous_id.sub continuous_const).matrix_mulVec continuous_const)
  unfold InN InS
  simp only [Set.setOf_and, Set.setOf_forall]
  exact ((isClosed_iInter fun a => hS _ _).inter (hS _ _)).inter
    (isClosed_iInter fun y => isClosed_iInter fun _ => hS _ _)

variable {D : D7}

theorem isClosed_stV (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    IsClosed (Formalism.L2.SG.NGPin.StV X u u' γ v) := by
  have hu : Continuous fun y : Formalism.REAL.UJ (X.B.I.ε v) => uMat y :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous fun y : Formalism.REAL.UJ (X.B.I.ε v) => uMat ((γ v)⁻¹ * y * γ v) :=
    hu.comp ((continuous_const.mul continuous_id).mul continuous_const)
  exact ((isClosed_inN _ _ _).preimage hu).inter ((isClosed_inN _ _ _).preimage hc)

theorem chartC_holds : Formalism.L2.SG.NGCut.StabilizerCovolume.ChartC := by
  intro D X Y u u' t hrel hG w hw γw s s' hrep hs hs' hpt
  have : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  have hτ : ∀ v : InfinitePlace X.B.I.F, ∃ τ, vOf X τ = v := fun v => ⟨X.pl v, X.pl.symm_apply_apply v⟩
  have hpl : ∀ z ∈ StInf X u u' γw, ∀ v, z v ∈ Formalism.L2.SG.NGPin.StV X u u' γw v := by
    intro z hz v
    rw [Formalism.L2.SG.NGPin.stInf_eq_pi] at hz
    exact hz v (Set.mem_univ _)
  refine ⟨BX, fun p => BX_measurable p, fun p x x' y y' h => BX_lower p x x' y y' h, fun p x => BX_zero p x,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Formalism.L2.SG.NGPin.stCoord_eq]
    refine measurable_pi_lambda _ fun v => ?_
    obtain ⟨τ, rfl⟩ := hτ v
    exact (stCoordV_meas C u' w γw τ).comp (measurable_pi_apply _)
  · rw [Formalism.L2.SG.NGPin.stInf_eq_pi]
    exact MeasurableSet.univ_pi fun v => (isClosed_stV X u u' γw v).measurableSet
  · intro z₁ h₁ z₂ h₂ heq
    rw [Formalism.L2.SG.NGPin.stCoord_eq] at heq
    funext v
    obtain ⟨τ, rfl⟩ := hτ v
    exact stCoordV_inj C u u' w γw τ hrep (hpl z₁ h₁ _) (hpl z₂ h₂ _) (congrFun heq (vOf X τ))
  · intro x
    have hex : ∀ v, ∃ y ∈ Formalism.L2.SG.NGPin.StV X u u' γw v,
        Formalism.L2.SG.NGPin.stCoordV X u' w γw v y = x v := by
      intro v
      obtain ⟨τ, rfl⟩ := hτ v
      exact stCoordV_surj C u u' w γw τ hrep (x (vOf X τ))
    choose y hy hyx using hex
    refine ⟨y, ?_, ?_⟩
    · rw [Formalism.L2.SG.NGPin.stInf_eq_pi]; exact fun v _ => hy v
    · rw [Formalism.L2.SG.NGPin.stCoord_eq]; funext v; exact hyx v
  · intro z₁ h₁ z₂ h₂
    refine ⟨?_, ?_⟩
    · have hN := Formalism.L2.SG.Pf.psiInfChar_holds D X u
      have hN' := Formalism.L2.SG.Pf.psiInfChar_holds D X u'
      refine ⟨(hN.2.1 _ h₁.1 _ h₂.1).1, ?_⟩
      have e : γw⁻¹ * (z₁ * z₂) * γw = (γw⁻¹ * z₁ * γw) * (γw⁻¹ * z₂ * γw) := by group
      rw [e]
      exact (hN'.2.1 _ h₁.2 _ h₂.2).1
    · rw [Formalism.L2.SG.NGPin.stCoord_eq]
      funext v p
      exact stCoordV_mul X v (hpl z₁ h₁ v) (hpl z₂ h₂ v) p
  · intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    refine ⟨?_, ?_⟩
    · have := Formalism.L2.SG.Pf.FormTranspose.sinf_conj X u (Formalism.L2.SG.Pf.Sinf.sinf_inv' X u hs) hr1
      simpa only [inv_inv] using this
    · have hγ : γw = s⁻¹ * t.pt.1 * s' := by rw [hpt]; group
      have := Formalism.L2.SG.Pf.FormTranspose.sinf_conj X u' (Formalism.L2.SG.Pf.Sinf.sinf_inv' X u' hs') hr2
      rw [hγ]
      convert this using 1
      group

end Formalism.L2.S.Pv.Chart

end
