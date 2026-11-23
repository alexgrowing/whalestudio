import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.OntoJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TruncEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.model :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (D : Datum H V W), ∃ M : Sc H V W, M.T₀ = D.T₀ ∧ (∀ u, M.J u = D.J u) ∧ (∀ v, M.J' v = D.J' v) ∧
      ∀ T Λ, D.T₀ ≤ T → (IsTrunc D.J D.J' T Λ ↔ Λ = M.abelian₂ T T) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ D
  let D' : Datum H W V :=
    { J := D.J', J' := D.J, T₀ := D.T₀, B := D.B, β := D.β', β' := D.β
      span := fun h a b => D.span h b a
      shift := fun t u u' v v' a b => by
        rw [← inner_conj_symm, ← D.shift t v v' u u' b a, inner_conj_symm]
      causal := fun s u v a b => by
        rw [← inner_conj_symm, D.causal (2 * D.T₀ - s) v u b (by simpa using a), map_zero]
      β_ker := D.β'_ker, β'_ker := D.β_ker, β_unit := D.β'_unit, β'_unit := D.β_unit, B_sa := D.B_sa
      B_J := D.B_J', B_J' := D.B_J
      compact := fun T Λ hT h => D.compact T Λ hT ⟨h.1, h.2.1, fun x => (h.2.2 x).trans
        ⟨fun ⟨u, v, a, b, c⟩ => ⟨v, u, b, a, c.trans (add_comm _ _)⟩, fun ⟨u, v, a, b, c⟩ => ⟨v, u, b, a, c.trans (add_comm _ _)⟩⟩⟩ }
  let J := LinearIsometryEquiv.ofSurjective D.J (ontoJ D)
  let J' := LinearIsometryEquiv.ofSurjective D.J' (ontoJ D')
  have hJ : ∀ u, J u = D.J u := fun _ => rfl
  have hJ' : ∀ u, J' u = D.J' u := fun _ => rfl
  let F : Flow H :=
    { U := fun t => (J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L sh V t ∘L (J.symm.toContinuousLinearEquiv : H →L[ℂ] L V)
      zero := fun h => by
        show J ((shF V).U 0 (J.symm h)) = h
        rw [(shF V).zero, J.apply_symm_apply]
      add := fun s t h => by
        show J ((shF V).U (s + t) (J.symm h)) = J ((shF V).U s (J.symm (J ((shF V).U t (J.symm h)))))
        rw [(shF V).add, J.symm_apply_apply]
      norm := fun t h => by
        show ‖J ((shF V).U t (J.symm h))‖ = _
        rw [J.norm_map, (shF V).norm, J.symm.norm_map]
      cont := fun h => J.continuous.comp ((shF V).cont _) }
  have hU : ∀ t u, F.U t (J u) = J (sh V t u) := fun t u => by
    show J (sh V t (J.symm (J u))) = _
    rw [J.symm_apply_apply]
  have sup : ∀ {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [CompleteSpace X] (s : ℝ) (u : L X),
      ∀ᵐ x : ℝ, x ≤ s → cut X (Ioi s) u x = 0 := fun s u =>
    (cutSpec (Ioi s) measurableSet_Ioi u).mono fun x h hx => by rw [h, indicator_of_notMem (by simpa using hx)]
  have caus : ∀ (s : ℝ) (u : L V) (v : L W), ⟪J (cut V (Ioi s) u), J' (cut W (Ioi (2 * D.T₀ - s)) v)⟫_ℂ = 0 :=
    fun s u v => D.causal s _ _ (sup s u) (sup _ v)
  refine ⟨⟨J, J', F, D.T₀, hU, fun t v => ?_, caus⟩, rfl, hJ, hJ', fun T Λ hT => ?_⟩
  · refine ext_inner_left ℂ fun h => ?_
    obtain ⟨u, rfl⟩ := J.surjective h
    have e : J u = F.U t (J (sh V (-t) u)) := by rw [← hU, ← F.add, add_neg_cancel, F.zero]
    conv_lhs => rw [e]
    refine ((⟨(F.U t : H →ₗ[ℂ] H), F.norm t⟩ : H →ₗᵢ[ℂ] H).inner_map_map _ _).trans ?_
    exact D.shift (-t) u _ v _ (sh_ae V _ u) (sh_ae W _ v)
  · rw [truncEq D.J D.J' T Λ fun u v => D.causal T _ _ (sup T u) ((sup T v).mono fun x h hx => h (by linarith))]
    have a1 : ContinuousLinearMap.adjoint D.J.toContinuousLinearMap = (J.symm.toContinuousLinearEquiv : H →L[ℂ] L V) :=
      ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => (J.inner_map_map _ _).symm.trans (by
        show ⟪J (J.symm x), J y⟫_ℂ = _
        rw [J.apply_symm_apply]; rfl)).symm
    have a2 : ContinuousLinearMap.adjoint D.J'.toContinuousLinearMap = (J'.symm.toContinuousLinearEquiv : H →L[ℂ] L W) :=
      ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => (J'.inner_map_map _ _).symm.trans (by
        show ⟪J' (J'.symm x), J' y⟫_ℂ = _
        rw [J'.apply_symm_apply]; rfl)).symm
    rw [a1, a2]
    rfl
