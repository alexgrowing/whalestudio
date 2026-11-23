import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.TypePoly

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def slc {K : Type} [Field K] [NumberField K] {n : ℕ} (g : AdelicGLn.AdelicGL K n) :
    archSmooth K n →ₗ[ℂ] (archCompact K n → ℂ) where
  toFun φ k := φ.1 (g * infEmb K n k.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem slc_op {K : Type} [Field K] [NumberField K] {n : ℕ} (X : (isExpLieAlgebra K n).lieSubalgebra)
    (hX : ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X) ∈ archCompact K n) :
    (∃ D : Module.End ℂ (archCompact K n → ℂ), ∀ g φ,
      D (slc g φ) = slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ)) ∧
    ∀ (V : Submodule ℂ (archCompact K n → ℂ)), FiniteDimensional ℂ V → (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) →
      ∀ g φ, slc g φ ∈ V → slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ) ∈ V := by
  let γ : ℝ → archCompact K n := fun t =>
    ⟨(isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X), hX t⟩
  have F : ∀ (g : AdelicGLn.AdelicGL K n) (φ : archSmooth K n) (k : archCompact K n),
      HasDerivAt (fun t => slc g φ (k * γ t)) (slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ) k) 0 := by
    intro g φ k
    have d := (isExpLieAlgebra K n).hasDerivAt_rightDeriv
      ((show IsArchSmooth φ.1 from φ.2) (g * infEmb K n k.1)) ((isExpLieAlgebra K n).ofLie X) 1
    show HasDerivAt _ ((uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 (g * infEmb K n k.1)) 0
    rw [uAction_ι_apply]
    have e : (fun t => slc g φ (k * γ t)) = fun t => archSlice φ.1 (g * infEmb K n k.1)
        (1 * (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X)) := by
      funext t
      simp only [slc, LinearMap.coe_mk, AddHom.coe_mk, archSlice_apply, one_mul, Subgroup.coe_mul, map_mul,
        mul_assoc]
      rfl
    rw [e]
    exact d
  let P : Submodule ℂ (archCompact K n → ℂ) :=
    { carrier := {f | ∀ k, DifferentiableAt ℝ (fun t => f (k * γ t)) 0}
      add_mem' := fun ha hb k => (ha k).add (hb k)
      zero_mem' := fun _ => differentiableAt_const _
      smul_mem' := fun c _ hf k => (hf k).const_smul c }
  let D₀ : P →ₗ[ℂ] (archCompact K n → ℂ) :=
    { toFun := fun f k => deriv (fun t => f.1 (k * γ t)) 0
      map_add' := fun f h => by
        funext k
        show deriv (fun t => f.1 (k * γ t) + h.1 (k * γ t)) 0 = _
        exact deriv_add (f.2 k) (h.2 k)
      map_smul' := fun c f => by
        funext k
        show deriv (fun t => c • f.1 (k * γ t)) 0 = _
        exact deriv_const_smul c (f.2 k) }
  obtain ⟨D, hD⟩ := LinearMap.exists_extend D₀
  refine ⟨⟨D, fun g φ => ?_⟩, fun V hV hVs g φ hφ => ?_⟩
  · have hm : slc g φ ∈ P := fun k => (F g φ k).differentiableAt
    have h1 := congrArg (fun L => L ⟨slc g φ, hm⟩) hD
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    funext k
    exact (F g φ k).deriv
  · haveI := hV
    exact mem_of_hasDerivAt V (c := fun t k => slc g φ (k * γ t)) (fun t => hVs _ hφ (γ t)) (fun k => F g φ k)

theorem UpperTheory.algMod_bot_compact_casimir_of_types :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Types S → ∀ (ι : Type) [Fintype ι] (X : ι → (isExpLieAlgebra K n).lieSubalgebra) (c : ι → ℝ), (∀ i, c i = 0 ∨ ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (X i)) ∈ archCompact K n) → AlgMod S ⊥ (uAction (∑ i, c i • (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i)))) := by
  intro K _ _ n S hS ι _ X c hc
  obtain ⟨V, hV, hVs, hSV⟩ := hS
  have hi : ∀ i, ∃ Di : Module.End ℂ (archCompact K n → ℂ), ∀ g φ,
      c i • Di (Di (slc g φ)) = slc g (c i • uAction (UniversalEnvelopingAlgebra.ι ℝ (X i))
        (uAction (UniversalEnvelopingAlgebra.ι ℝ (X i)) φ)) := by
    intro i
    rcases hc i with h0 | hX
    · exact ⟨0, fun g φ => by simp [h0]⟩
    · obtain ⟨D, hD⟩ := (slc_op (X i) hX).1
      exact ⟨D, fun g φ => by rw [hD, hD, LinearMap.map_smul_of_tower]⟩
  choose Di hDi using hi
  have e1 : ∀ φ : archSmooth K n, uAction (∑ i, c i • (UniversalEnvelopingAlgebra.ι ℝ (X i) *
      UniversalEnvelopingAlgebra.ι ℝ (X i))) φ = ∑ i, c i • uAction (UniversalEnvelopingAlgebra.ι ℝ (X i))
        (uAction (UniversalEnvelopingAlgebra.ι ℝ (X i)) φ) := by
    intro φ
    simp only [map_sum, map_smul, map_mul, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  have hinter : ∀ g φ, (∑ i, c i • (Di i * Di i)) (slc g φ) = slc g (uAction (∑ i, c i •
      (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i))) φ) := by
    intro g φ
    rw [e1, map_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    exact Finset.sum_congr rfl fun i _ => hDi i g φ
  have hstab : ∀ φ ∈ (⨅ g, V.comap (slc g)), uAction (∑ i, c i •
      (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i))) φ ∈ (⨅ g, V.comap (slc g)) := by
    intro φ hφ
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hφ ⊢
    intro g
    rw [e1, map_sum]
    refine V.sum_mem fun i _ => ?_
    rw [LinearMap.map_smul_of_tower]
    rcases hc i with h0 | hX
    · rw [h0, zero_smul]
      exact V.zero_mem
    · exact V.smul_of_tower_mem _ ((slc_op (X i) hX).2 V hV hVs g _ ((slc_op (X i) hX).2 V hV hVs g φ (hφ g)))
  have hinV : ∀ g, ∀ φ ∈ (⨅ g, V.comap (slc g)), slc g φ ∈ V := by
    intro g φ hφ
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hφ
    exact hφ g
  obtain ⟨q, hq, -, hq0⟩ := UpperTheory.V.Af.CuspFin.polySlices (archSmooth K n) (archCompact K n → ℂ)
    (AdelicGLn.AdelicGL K n) _ _ (fun g => slc g) hinter V hV _ hstab hinV
  refine ⟨q, hq, fun φ hφ => ?_⟩
  rw [Submodule.mem_bot]
  have hN : φ ∈ (⨅ g, V.comap (slc g)) := by
    simp only [Submodule.mem_iInf, Submodule.mem_comap]
    exact fun g => hSV φ hφ g
  apply Subtype.ext
  funext g
  have h1 := congrFun (hq0 g φ hN) 1
  simpa [slc] using h1
