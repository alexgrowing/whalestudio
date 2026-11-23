import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.HomFin

open NumberField MeasureTheory
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

private theorem UpperTheory.V.KernelIndexFullLattice.pvFin_abs {G E M : Type} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [AddCommGroup M] [Module ℂ M]
    (C : Subgroup G) [IsTopologicalGroup C] [CompactSpace C] [T2Space C] (ρ : BanachRep G E)
    (σ : Representation ℂ C M) (hσ : CompactRep.IsKFinite σ) (j : M →ₗ[ℂ] E) (hj : Function.Injective j)
    (hjσ : ∀ (k : C) m, j (σ k m) = ρ k (j m)) (F : Submodule ℂ M)
    (hF : ∀ (c : Submodule (MonoidAlgebra ℂ C) σ.asModule)
      (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ C) σ.asModule),
      FiniteDimensional ℂ (LinearMap.range (CompactRep.kProj hσ hc ∘ₗ F.subtype)))
    (v : E) (hv : FiniteDimensional ℂ (ρ.kSpan C v)) :
    ∃ N : Submodule ℂ E, FiniteDimensional ℂ N ∧ ∀ P : E →L[ℂ] E,
      (∀ (k : C) x, P (ρ k x) = ρ k (P x)) → (∀ x ∈ ρ.kSpan C v, ∃ m ∈ F, j m = P x) → P v ∈ N := by
  let S : Subrepresentation (ρ.restrict C).toRepresentation :=
    ⟨ρ.kSpan C v, fun k _ hw => ρ.map_mem_kSpan_of_mem C hw k⟩
  have hc : Representation.HasContinuousCoeff (W := ρ.kSpan C v) S.toRepresentation := by
    intro φ w
    refine φ.continuous_of_finiteDimensional.comp ?_
    exact Continuous.subtype_mk ((ρ.continuous_orbit (w : E)).comp continuous_subtype_val) _
  obtain ⟨N, hN, hN'⟩ := UpperTheory.V.KernelIndexFullLattice.homFin_holds C M (ρ.kSpan C v) σ hσ S.toRepresentation hc F hF
  refine ⟨N.map j, inferInstance, fun P hP hPF => ?_⟩
  have hr : ∀ x : ρ.kSpan C v, ((P : E →ₗ[ℂ] E) ∘ₗ (ρ.kSpan C v).subtype) x ∈ LinearMap.range j := by
    intro x
    obtain ⟨m, -, hm⟩ := hPF x x.2
    exact ⟨m, hm⟩
  let f : ρ.kSpan C v →ₗ[ℂ] M := (LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range j) _ hr
  have hf : ∀ x, j (f x) = P x := fun x =>
    congrArg Subtype.val ((LinearEquiv.ofInjective j hj).apply_symm_apply ⟨_, hr x⟩)
  refine ⟨f ⟨v, ρ.mem_kSpan_self C v⟩, hN' f (fun k x => hj ?_) (fun x => ?_) _, hf _⟩
  · rw [hjσ, hf, hf, ← hP]
    rfl
  · obtain ⟨m, hm, e⟩ := hPF x x.2
    rwa [hj ((hf x).trans e.symm)]

theorem UpperTheory.V.KernelIndexFullLattice.pvFin_holds :
    UpperTheory.V.KernelIndexFullLattice.PvFin := by
  intro K _ _ n μ₁ _ π U hUc hUo v hv hfin
  let j : π.carrier →ₗ[ℂ] CuspL2 μ₁ := cuspVecL μ₁ ∘ₗ π.carrier.subtype
  have hj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun m hm => Subtype.ext ?_
    exact eq_zero_of_cuspVecL_eq_zero (μ := μ₁) (π.le_central m.2) hm
  obtain ⟨N, hN, hN'⟩ := UpperTheory.V.KernelIndexFullLattice.pvFin_abs (archCompact K n) (archRepT μ₁) π.toModule.gk.σ
    π.toModule.gk.isKFinite j hj (fun k m => cuspToL2_sigma μ₁ k (π.le_central m.2))
    (fixedVectors π.toModule.τ U) (π.isAdmissible.2 U hUc hUo) v hfin
  refine ⟨N, hN, fun P hPk hPu hP => hN' P hPk fun x hx => ?_⟩
  have hxU : ∀ u ∈ U, cuspRepT μ₁ (retractOne (finEmb K n u)) x = x := by
    intro u hu
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      have hcomm : retractOne (finEmb K n u) * archP K n k = archP K n k * retractOne (finEmb K n u) := by
        rw [← retract_infEmb, ← retractOne_mul, ← retractOne_mul, infEmb_mul_finEmb_comm]
      have h1 := (cuspRepT μ₁).map_mul_apply (retractOne (finEmb K n u)) (archP K n k) v
      have h2 := (cuspRepT μ₁).map_mul_apply (archP K n k) (retractOne (finEmb K n u)) v
      rw [hv u hu, ← hcomm, h1] at h2
      exact h2
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  obtain ⟨φ, hφ, e⟩ := hP x
  refine ⟨⟨φ, hφ⟩, fun u hu => hj ?_, e⟩
  have h := cuspToL2_finRepCusp μ₁ u (π.le_central hφ)
  rw [e, ← hPu u hu, hxU u hu, ← e] at h
  exact h
