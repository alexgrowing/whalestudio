import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.ContinuousDSWOrbit
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.FinAlgSepKG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaFA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem intK {E : Type*} [NormedAddCommGroup E] {f : S7.KG ε → E} (hf : Continuous f) :
    Integrable f (S7.muK ε) := by
  have := S7.compactSpace_KG ε
  have : IsFiniteMeasureOnCompacts (S7.muK ε) := by unfold S7.muK; infer_instance
  exact integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)

theorem orbitK_continuous (hσ : IsURepOn (UJset ε) σ) (u : H) :
    Continuous fun k : S7.KG ε => σ (S7.toMK k) u :=
  (hσ.2.2 u).comp_continuous S7.IdA.continuous_toMK fun k => smd_inUJ_of_Kset k.2

theorem toMK_mul_apply (hσ : IsURepOn (UJset ε) σ) (k₀ k : S7.KG ε) (u : H) :
    σ (S7.toMK (k₀ * k)) u = σ (S7.toMK k₀) (σ (S7.toMK k) u) := by
  rw [show S7.toMK (k₀ * k) = S7.toMK k₀ * S7.toMK k from rfl,
    hσ.1.2 _ (smd_inUJ_of_Kset k₀.2) _ (smd_inUJ_of_Kset k.2)]
  rfl

theorem kfin_integral (hσ : IsURepOn (UJset ε) σ) (u : H) {α : C(S7.KG ε, ℂ)} (hα : Mult1.Down.KF.Fin2 α) :
    Formalism.MainNotions.S.IsKFin ε σ (∫ k, α k • σ (S7.toMK k) u ∂(S7.muK ε)) := by
  classical
  have := S7.compactSpace_KG ε
  set x := ∫ k, α k • σ (S7.toMK k) u ∂(S7.muK ε)
  obtain ⟨ι, _, a, β, hab⟩ := hα
  have hint : ∀ γ : C(S7.KG ε, ℂ), Integrable (fun k => γ k • σ (S7.toMK k) u) (S7.muK ε) := fun γ =>
    intK (γ.continuous.smul (orbitK_continuous hσ u))
  set T : Submodule ℂ H := Submodule.span ℂ (Set.range fun i => ∫ κ, β i κ • σ (S7.toMK κ) u ∂(S7.muK ε))
  have hT : FiniteDimensional ℂ T := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have key : ∀ k₀ : S7.KG ε, σ (S7.toMK k₀) x ∈ T := by
    intro k₀
    have e1 : σ (S7.toMK k₀) x = ∫ k, α k • σ (S7.toMK (k₀ * k)) u ∂(S7.muK ε) := by
      rw [← (σ (S7.toMK k₀)).integral_comp_comm (hint α)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [map_smul, toMK_mul_apply hσ]
    set f : S7.KG ε → H := fun κ => α (k₀⁻¹ * κ) • σ (S7.toMK κ) u
    have e2 : ∫ k, α k • σ (S7.toMK (k₀ * k)) u ∂(S7.muK ε) = ∫ κ, f κ ∂(S7.muK ε) := by
      rw [← integral_mul_left_eq_self f k₀]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [f, inv_mul_cancel_left]
    have e3 : ∫ κ, f κ ∂(S7.muK ε) =
        ∑ i, a i k₀⁻¹ • ∫ κ, β i κ • σ (S7.toMK κ) u ∂(S7.muK ε) := by
      have : f = fun κ => ∑ i, a i k₀⁻¹ • (β i κ • σ (S7.toMK κ) u) := by
        funext κ
        simp only [f, hab, Finset.sum_smul, smul_smul]
      rw [this]
      show ∫ κ, ∑ i, a i k₀⁻¹ • (β i κ • σ (S7.toMK κ) u) ∂(S7.muK ε) = _
      rw [integral_finsetSum Finset.univ (f := fun i κ => a i k₀⁻¹ • (β i κ • σ (S7.toMK κ) u))
        (fun i _ => (hint (β i)).smul (a i k₀⁻¹))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_smul]
    rw [e1, e2, e3]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  set S : Submodule ℂ H := Submodule.span ℂ (Set.range fun k : S7.KG ε => σ (S7.toMK k) x)
  have hST : S ≤ T := Submodule.span_le.2 fun v ⟨k, hk⟩ => hk ▸ key k
  refine ⟨S, Submodule.finiteDimensional_of_le hST, ?_, ?_⟩
  · have : σ (S7.toMK (1 : S7.KG ε)) x = x := by
      rw [show S7.toMK (1 : S7.KG ε) = 1 from rfl, hσ.1.1]
      rfl
    exact this ▸ Submodule.subset_span ⟨1, rfl⟩
  · intro g hg v hv
    obtain ⟨k', rfl⟩ := ffa_Kset (ε := ε) hg
    have hle : S ≤ S.comap (σ (S7.toMK k')) := Submodule.span_le.2 fun w ⟨k, hk⟩ => by
      rw [← hk]
      show σ (S7.toMK k') (σ (S7.toMK k) x) ∈ S
      rw [← toMK_mul_apply hσ]
      exact Submodule.subset_span ⟨k' * k, rfl⟩
    exact hle hv

theorem dSW_integral (hσ : IsURepOn (UJset ε) σ)
    (hsep : ∀ z : H, (∀ y, IsSmoothVecU ε σ y → inner ℂ y z = 0) → z = 0)
    {w : List (Matrix (Fin n) (Fin n) ℂ)} (hw : ∀ X ∈ w, inG ε X) {u : H} (hu : IsSmoothVecU ε σ u)
    (α : C(S7.KG ε, ℂ)) (hx : IsSmoothVecU ε σ (∫ k, α k • σ (S7.toMK k) u ∂(S7.muK ε))) :
    dSW σ w (∫ k, α k • σ (S7.toMK k) u ∂(S7.muK ε)) =
      ∫ k, α k • dSW σ w (σ (S7.toMK k) u) ∂(S7.muK ε) := by
  have := S7.compactSpace_KG ε
  have hint1 : Integrable (fun k => α k • σ (S7.toMK k) u) (S7.muK ε) :=
    intK (α.continuous.smul (orbitK_continuous hσ u))
  have hint2 : Integrable (fun k => α k • dSW σ w (σ (S7.toMK k) u)) (S7.muK ε) :=
    intK (α.continuous.smul (continuous_dSW_orbit hσ hw hu))
  refine sub_eq_zero.1 (hsep _ fun y hy => ?_)
  have hwr : ∀ X ∈ w.reverse, inG ε X := fun X hX => hw X (List.mem_reverse.1 hX)
  rw [inner_sub_right, sub_eq_zero, inner_dSW hσ hw hy hx, ← integral_inner hint1, ← integral_inner hint2,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right]
  rw [inner_dSW hσ hw hy (IsSmoothVecU.kStable hσ k.2 hu)]
  ring

section abelian₂

variable {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
  {v₀ : T.V}

theorem sigLam_smooth_of_genSub {y : smD ε (rreg ε)}
    (hyH : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀) :
    IsSmoothVecU ε (sigLam ε Ψ v₀) (⟨(y : L2 ε), hyH⟩ : Hlam ε Ψ v₀) := by
  have h := (mem_smD_iff ε (rreg ε) (y : L2 ε)).1 y.2
  exact smoothOnGV_clm (Hlam ε Ψ v₀).orthogonalProjectionOnto h

theorem sigLam_sep (z : Hlam ε Ψ v₀)
    (hz : ∀ y, IsSmoothVecU ε (sigLam ε Ψ v₀) y → inner ℂ y z = 0) : z = 0 := by
  have hcl : IsClosed {v : L2 ε | inner ℂ v (z : L2 ε) = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hsub : (((genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)).map (smD ε (rreg ε)).subtype : Submodule ℂ (L2 ε)) :
      Set (L2 ε)) ⊆ {v : L2 ε | inner ℂ v (z : L2 ε) = 0} := by
    rintro v ⟨y, hy, rfl⟩
    have hyH : ((y : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ v₀ :=
      Submodule.le_topologicalClosure _ ⟨y, hy, rfl⟩
    have := hz _ (sigLam_smooth_of_genSub hyH)
    rwa [Submodule.coe_inner] at this
  have hzc : (z : L2 ε) ∈ closure (((genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)).map (smD ε (rreg ε)).subtype :
      Submodule ℂ (L2 ε)) : Set (L2 ε)) := by
    have := z.2
    unfold Hlam closGen at this
    rwa [← Submodule.topologicalClosure_coe]
  have h0 : inner ℂ (z : L2 ε) (z : L2 ε) = (0 : ℂ) := hcl.closure_subset_iff.2 hsub hzc
  exact Subtype.ext (inner_self_eq_zero.1 h0)

end abelian₂

end ReciprocityTheory.ChartRestriction.DS.DecInf
