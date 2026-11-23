import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigOrdInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.AdmLocal
open IsLocalRing UpperTheory.V.Hi UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

open TensorProduct in
private theorem UpperTheory.pi_scalar_right_tmul {O Ω ι : Type} [CommRing O] [Field Ω] [Algebra O Ω]
    [Fintype ι] [DecidableEq ι] (a : Ω) (v : ι → O) :
    TensorProduct.piScalarRight O Ω Ω ι (a ⊗ₜ v) = a • fun i => algebraMap O Ω (v i) := by
  ext i
  simp [Algebra.smul_def, mul_comm]

private theorem UpperTheory.map_max_gen_eigenspace_of_intertwine {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (E : V ≃ₗ[K] W) (f : Module.End K V) (g : Module.End K W)
    (h : ∀ x, g (E x) = E (f x)) (μ : K) :
    (f.maxGenEigenspace μ).map E.toLinearMap = g.maxGenEigenspace μ := by
  have hp : ∀ (k : ℕ) x, ((g - μ • 1) ^ k) (E x) = E (((f - μ • 1) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]
      simp [h]
  ext y
  obtain ⟨x, rfl⟩ := E.surjective y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Module.End.mem_maxGenEigenspace,
    Module.End.mem_maxGenEigenspace]
  simp only [hp, EmbeddingLike.map_eq_zero_iff]

theorem UpperTheory.span_ordinaryPart_eq_sup_unit_generalized_eigenspaces :
    ∀ (O Ω ι : Type) [CommRing O] [IsCNL O] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω] [Fintype ι] (T₀ : Module.End O (ι → O)) (T : Module.End Ω (ι → Ω)), (∀ v, T (fun i => algebraMap O Ω (v i)) = fun i => algebraMap O Ω (T₀ v i)) → ⨆ μ : {μ : Ω // IsIntUnit O μ}, T.maxGenEigenspace μ.1 = Submodule.span Ω ((fun (v : ι → O) i => algebraMap O Ω (v i)) '' (ordPart T₀ : Set (ι → O))) := by
  intro O Ω ι _ hO _ _ _ _ T₀ T hT
  classical
  haveI : IsAdicComplete (maximalIdeal O) O := hO.complete
  have hadm := (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordAdm_maximalIdeal_and_finite_quotients (R := O) (M := ι → O)).1
  have hex := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExists hadm T₀
  have key := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt (K := Ω) hex.1
  set E := TensorProduct.piScalarRight O Ω Ω ι with hE
  have hEt : ∀ (a : Ω) (v : ι → O),
      E (a ⊗ₜ v) = a • fun i => algebraMap O Ω (v i) := UpperTheory.pi_scalar_right_tmul
  have hc : ∀ x, T (E x) = E (T₀.baseChange Ω x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => rw [LinearMap.baseChange_tmul, hEt, hEt, map_smul, hT]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h1 := congrArg (Submodule.map E.toLinearMap) key
  simp only [Submodule.map_iSup, UpperTheory.map_max_gen_eigenspace_of_intertwine E _ T hc] at h1
  rw [iSup_subtype]
  refine Eq.trans ?_ (h1.symm.trans ?_)
  · rfl
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      rw [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hEt]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
      rw [← hex.2.1]
      exact ⟨v, rfl⟩
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    rw [← hex.2.1] at hv
    obtain ⟨w, rfl⟩ := hv
    refine ⟨_, ⟨(1 : Ω) ⊗ₜ w, rfl⟩, ?_⟩
    rw [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hEt, one_smul]
