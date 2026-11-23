import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleDiscreteSpaces

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
namespace GlobalTheory.CompanionTheory.FinDiscRepr

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

lemma integrable_of_cont (ν : Measure K) [ν.IsHaarMeasure] {f : K → ℂ} (hf : Continuous f) :
    Integrable f ν :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma exists_weak_integral (ν : Measure K) [ν.IsHaarMeasure]
    {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (a : K → E)
    (ha : ∀ ℓ : E →ₗ[ℂ] ℂ, Continuous fun k => ℓ (a k)) :
    ∃ v : E, ∀ ℓ : E →ₗ[ℂ] ℂ, ℓ v = ∫ k, ℓ (a k) ∂ν := by
  let Φ : Module.Dual ℂ (Module.Dual ℂ E) :=
    { toFun := fun ℓ => ∫ k, ℓ (a k) ∂ν
      map_add' := fun ℓ ℓ' => by
        simpa using integral_add (integrable_of_cont ν (ha ℓ)) (integrable_of_cont ν (ha ℓ'))
      map_smul' := fun c ℓ => by
        simpa using integral_const_mul c (fun k => ℓ (a k)) }
  refine ⟨(Module.evalEquiv ℂ E).symm Φ, fun ℓ => ?_⟩
  have h := (Module.evalEquiv ℂ E).apply_symm_apply Φ
  have h2 := congrArg (fun F : Module.Dual ℂ (Module.Dual ℂ E) => F ℓ) h
  simpa [Module.evalEquiv_apply, Φ] using h2

lemma exists_weak_integral_sub (ν : Measure K) [ν.IsHaarMeasure]
    {M : Type} [AddCommGroup M] [Module ℂ M] (A : Submodule ℂ M) [FiniteDimensional ℂ A]
    (a : K → M) (haA : ∀ k, a k ∈ A) (h : K → ℂ) (hh : Continuous h)
    (ha : ∀ ℓ : M →ₗ[ℂ] ℂ, Continuous fun k => ℓ (a k)) :
    ∃ v ∈ A, ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ v = ∫ k, h k * ℓ (a k) ∂ν := by
  obtain ⟨v, hv⟩ := exists_weak_integral ν (E := A) (fun k => h k • (⟨a k, haA k⟩ : A)) (by
    intro ℓ
    obtain ⟨ℓ', hℓ'⟩ := LinearMap.exists_extend ℓ
    have : ∀ k, ℓ (h k • (⟨a k, haA k⟩ : A)) = h k * ℓ' (a k) := by
      intro k
      rw [map_smul, smul_eq_mul, ← hℓ']
      rfl
    simp only [this]
    exact hh.mul (ha ℓ'))
  refine ⟨v, v.2, fun ℓ => ?_⟩
  have := hv (ℓ.domRestrict A)
  simpa using this

lemma exists_repr_point (ν : Measure K) [ν.IsHaarMeasure]
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : K → V)
    (hb : ∀ ℓ : V →ₗ[ℂ] ℂ, Continuous fun k => ℓ (b k)) :
    ∃ τ : V →ₗ[ℂ] ℂ, ∀ σ : V →ₗ[ℂ] ℂ,
      σ (b 1) = ∫ k, (starRingEnd ℂ) (τ (b k)) * σ (b k) ∂ν := by
  classical
  have hex : ∀ τ : V →ₗ[ℂ] ℂ, ∃ T : V, ∀ σ : V →ₗ[ℂ] ℂ,
      σ T = ∫ k, (starRingEnd ℂ) (τ (b k)) * σ (b k) ∂ν := fun τ =>
    exists_weak_integral ν (fun k => (starRingEnd ℂ) (τ (b k)) • b k) (by
      intro ℓ
      simp only [map_smul, smul_eq_mul]
      exact (Complex.continuous_conj.comp (hb τ)).mul (hb ℓ)) |>.imp fun T hT σ => by
        simpa using hT σ
  let S : Submodule ℂ V :=
    { carrier := {T | ∃ τ : V →ₗ[ℂ] ℂ, ∀ σ : V →ₗ[ℂ] ℂ,
        σ T = ∫ k, (starRingEnd ℂ) (τ (b k)) * σ (b k) ∂ν}
      add_mem' := by
        rintro T T' ⟨τ, hτ⟩ ⟨τ', hτ'⟩
        refine ⟨τ + τ', fun σ => ?_⟩
        rw [map_add, hτ, hτ', ← integral_add]
        · simp [add_mul]
        · exact integrable_of_cont ν ((Complex.continuous_conj.comp (hb τ)).mul (hb σ))
        · exact integrable_of_cont ν ((Complex.continuous_conj.comp (hb τ')).mul (hb σ))
      zero_mem' := ⟨0, fun σ => by simp⟩
      smul_mem' := by
        rintro c T ⟨τ, hτ⟩
        refine ⟨(starRingEnd ℂ) c • τ, fun σ => ?_⟩
        rw [map_smul, hτ, smul_eq_mul, ← integral_const_mul]
        simp [mul_assoc] }
  by_cases hu : b 1 ∈ S
  · obtain ⟨τ, hτ⟩ := hu
    exact ⟨τ, hτ⟩
  · exfalso
    obtain ⟨l, hl1, hl2⟩ := Submodule.exists_le_ker_of_notMem hu
    obtain ⟨T, hT⟩ := hex l
    have hTS : T ∈ S := ⟨l, hT⟩
    have hz : l T = 0 := hl2 hTS
    have hnn : ∀ k, (starRingEnd ℂ) (l (b k)) * l (b k) = ((‖l (b k)‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hi : ∫ k, ‖l (b k)‖ ^ 2 ∂ν = 0 := by
      have := hT l
      rw [hz] at this
      simp only [hnn] at this
      rw [integral_complex_ofReal] at this
      exact_mod_cast this.symm
    have hc : Continuous fun k => ‖l (b k)‖ ^ 2 := ((hb l).norm).pow 2
    have hint : Integrable (fun k => ‖l (b k)‖ ^ 2) ν :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hae := (integral_eq_zero_iff_of_nonneg (fun k => by positivity) hint).1 hi
    have hall : (fun k => ‖l (b k)‖ ^ 2) = fun _ => (0 : ℝ) :=
      (Continuous.ae_eq_iff_eq ν hc continuous_const).1 hae
    have := congrFun hall 1
    simp at this
    exact hl1 this

end GlobalTheory.CompanionTheory.FinDiscRepr

namespace GlobalTheory.CompanionTheory.FinDiscRepr

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

lemma end_coeff_continuous {M : Type} [AddCommGroup M] [Module ℂ M]
    (A : Submodule ℂ M) [FiniteDimensional ℂ A] (r : K → A →ₗ[ℂ] A)
    (hr : ∀ ℓ : M →ₗ[ℂ] ℂ, ∀ a : A, Continuous fun k => ℓ (r k a : M))
    (η : (A →ₗ[ℂ] A) →ₗ[ℂ] ℂ) : Continuous fun k => η (r k) := by
  classical
  let b := Module.finBasis ℂ A
  let c : ((Fin (Module.finrank ℂ A)) → A) →ₗ[ℂ] ℂ := η ∘ₗ (b.constr ℂ).toLinearMap
  have key : ∀ k, η (r k) = ∑ i, (c ∘ₗ LinearMap.single ℂ (fun _ : Fin (Module.finrank ℂ A) => (A : Type)) i) (r k (b i)) := by
    intro k
    have h1 : r k = b.constr ℂ (fun i => r k (b i)) := (b.constr_self ℂ (r k)).symm
    have h2 : (fun i => r k (b i)) = ∑ i, Pi.single i (r k (b i)) :=
      (Finset.univ_sum_single _).symm
    calc η (r k) = c (fun i => r k (b i)) := by
          simp only [c, LinearMap.comp_apply, LinearEquiv.coe_coe]
          rw [← h1]
      _ = _ := by
          rw [h2, map_sum]
          simp [LinearMap.single_apply]
  simp only [key]
  refine continuous_finset_sum _ fun i _ => ?_
  obtain ⟨ℓ', hℓ'⟩ := LinearMap.exists_extend (c ∘ₗ LinearMap.single ℂ (fun _ : Fin (Module.finrank ℂ A) => (A : Type)) i)
  have : ∀ k, (c ∘ₗ LinearMap.single ℂ (fun _ : Fin (Module.finrank ℂ A) => (A : Type)) i) (r k (b i)) = ℓ' (r k (b i) : M) := by
    intro k
    rw [← hℓ']
    rfl
  simp only [this]
  exact hr ℓ' (b i)

theorem representing_vector : ∀ {K M H X : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure] [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Representation ℂ K M) (ι : M →ₗ[ℂ] H) (U U' : Submodule ℂ M) (ev : X → M →ₗ[ℂ] ℂ),
  (∀ k, ∀ x ∈ U', ∀ y ∈ U, ⟪ι (ρ k x), ι (ρ k y)⟫_ℂ = ⟪ι x, ι y⟫_ℂ) →
  (∀ k, ∀ x ∈ U', ∀ y ∈ U', ⟪ι (ρ k x), ι (ρ k y)⟫_ℂ = ⟪ι x, ι y⟫_ℂ) →
  (∀ x ∈ U, ∃ A : Submodule ℂ M, FiniteDimensional ℂ A ∧ x ∈ A ∧ A ≤ U ∧ (∀ k, ∀ a ∈ A, ρ k a ∈ A) ∧ ∀ ℓ : M →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (ρ k a)) →
  (∀ x ∈ U', ∃ A : Submodule ℂ M, FiniteDimensional ℂ A ∧ x ∈ A ∧ A ≤ U' ∧ (∀ k, ∀ a ∈ A, ρ k a ∈ A) ∧ ∀ ℓ : M →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (ρ k a)) →
  (∀ W : Submodule ℂ (K → ℂ), FiniteDimensional ℂ W → FiniteDimensional ℂ (Submodule.span ℂ {x | x ∈ U' ∧ ∀ t, (fun k => ev t (ρ k x)) ∈ W})) →
  ∀ x ∈ U, ∃ y ∈ U', ∀ z ∈ U', ⟪ι z, ι x⟫_ℂ = ⟪ι z, ι y⟫_ℂ := by
  intro K M H X _ _ _ _ _ _ ν _ _ _ _ _ ρ ι U U' ev h1 h2 hU hU' hadm x hx
  obtain ⟨A, hAfd, hxA, hAU, hAst, hAc⟩ := hU x hx
  haveI := hAfd
  let ρA : K → A →ₗ[ℂ] A := fun k => (ρ k).restrict (hAst k)
  have hρA : ∀ k (a : A), ((ρA k a : A) : M) = ρ k a := fun k a => rfl
  have hρAmul : ∀ k k', ρA (k * k') = ρA k ∘ₗ ρA k' := by
    intro k k'
    ext a
    simp [hρA, map_mul, Module.End.mul_apply]
  have hρA1 : ρA 1 = LinearMap.id := by
    ext a
    simp [hρA]
  have hcont : ∀ η : (A →ₗ[ℂ] A) →ₗ[ℂ] ℂ, Continuous fun k => η (ρA k) :=
    end_coeff_continuous A ρA (fun ℓ a => by
      simpa [hρA] using hAc ℓ a a.2)
  have hinv : ∀ η : (A →ₗ[ℂ] A) →ₗ[ℂ] ℂ, Continuous fun k => η (ρA k⁻¹) :=
    fun η => (hcont η).comp continuous_inv
  obtain ⟨τ, hτ⟩ := exists_repr_point ν (fun k => ρA k⁻¹) hinv
  have hτ' : ∀ σ : (A →ₗ[ℂ] A) →ₗ[ℂ] ℂ, σ LinearMap.id =
      ∫ k, (starRingEnd ℂ) (τ (ρA k⁻¹)) * σ (ρA k⁻¹) ∂ν := by
    intro σ
    have := hτ σ
    simpa [hρA1] using this
  let g : K → ℂ := fun k => τ (ρA k⁻¹)
  have hg : Continuous g := hinv τ
  have hcg : Continuous fun k => (starRingEnd ℂ) (g k) := Complex.continuous_conj.comp hg

  have K1 : ∀ ℓ : M →ₗ[ℂ] ℂ, ∀ w ∈ A,
      ℓ w = ∫ k, (starRingEnd ℂ) (g k) * ℓ (ρ k⁻¹ w) ∂ν := by
    intro ℓ w hw
    let σ : (A →ₗ[ℂ] A) →ₗ[ℂ] ℂ :=
      { toFun := fun φ => ℓ (φ ⟨w, hw⟩ : M)
        map_add' := fun φ ψ => by simp
        map_smul' := fun c φ => by simp }
    exact hτ' σ

  have hst' : ∀ k, ∀ z ∈ U', ρ k z ∈ U' := by
    intro k z hz
    obtain ⟨B, _, hzB, hBU, hBst, _⟩ := hU' z hz
    exact hBU (hBst k z hzB)

  let Φ : ((A →ₗ[ℂ] A) →ₗ[ℂ] ℂ) →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun η k => η (ρA k)
      map_add' := fun η η' => rfl
      map_smul' := fun c η => rfl }
  let Wf : Submodule ℂ (K → ℂ) := LinearMap.range Φ
  haveI hWf : FiniteDimensional ℂ Wf := inferInstance
  let S : Set M := {x | x ∈ U' ∧ ∀ t, (fun k => ev t (ρ k x)) ∈ Wf}
  let D : Submodule ℂ M := Submodule.span ℂ S
  haveI hDfd : FiniteDimensional ℂ D := hadm Wf hWf
  have hDU : D ≤ U' := Submodule.span_le.2 fun _ h => h.1

  have Z : ∀ z ∈ U', ∃ z₁ ∈ S, ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ z₁ = ∫ k, g k * ℓ (ρ k z) ∂ν := by
    intro z hz
    obtain ⟨B, hBfd, hzB, hBU, hBst, hBc⟩ := hU' z hz
    haveI := hBfd
    obtain ⟨z₁, hz₁B, hz₁⟩ := exists_weak_integral_sub ν B (fun k => ρ k z)
      (fun k => hBst k z hzB) g hg (fun ℓ => hBc ℓ z hzB)
    refine ⟨z₁, ⟨hBU hz₁B, fun t => ?_⟩, hz₁⟩
    let f : K → ℂ := fun k => ev t (ρ k z)
    have hf : Continuous f := hBc (ev t) z hzB
    have hcomp : ∀ φ : A →ₗ[ℂ] A, Continuous fun k => τ (ρA k⁻¹ ∘ₗ φ) := by
      intro φ
      let σ : (A →ₗ[ℂ] A) →ₗ[ℂ] ℂ :=
        { toFun := fun ψ => τ (ψ ∘ₗ φ)
          map_add' := fun ψ ψ' => by rw [LinearMap.add_comp, map_add]
          map_smul' := fun c ψ => by rw [LinearMap.smul_comp, map_smul]; rfl }
      exact hinv σ
    let η : (A →ₗ[ℂ] A) →ₗ[ℂ] ℂ :=
      { toFun := fun φ => ∫ k, τ (ρA k⁻¹ ∘ₗ φ) * f k ∂ν
        map_add' := fun φ ψ => by
          have i1 : Integrable (fun k => τ (ρA k⁻¹ ∘ₗ φ) * f k) ν :=
            integrable_of_cont ν ((hcomp φ).mul hf)
          have i2 : Integrable (fun k => τ (ρA k⁻¹ ∘ₗ ψ) * f k) ν :=
            integrable_of_cont ν ((hcomp ψ).mul hf)
          rw [← integral_add i1 i2]
          simp [LinearMap.comp_add, add_mul]
        map_smul' := fun c φ => by
          rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
          simp [LinearMap.comp_smul, mul_assoc] }
    refine ⟨η, funext fun k₀ => ?_⟩
    show ∫ k, τ (ρA k⁻¹ ∘ₗ ρA k₀) * f k ∂ν = ev t (ρ k₀ z₁)
    have e1 : ev t (ρ k₀ z₁) = ∫ k, g k * f (k₀ * k) ∂ν := by
      have := hz₁ ((ev t) ∘ₗ (ρ k₀))
      simpa [f, map_mul, Module.End.mul_apply] using this
    rw [e1, ← integral_mul_left_eq_self (fun k => τ (ρA k⁻¹ ∘ₗ ρA k₀) * f k) k₀]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show τ (ρA (k₀ * k)⁻¹ ∘ₗ ρA k₀) * f (k₀ * k) = g k * f (k₀ * k)
    have : ρA (k₀ * k)⁻¹ ∘ₗ ρA k₀ = ρA k⁻¹ := by
      rw [← hρAmul]
      simp
    rw [this]

  have I1 : ∀ (z z₁ : M), (∀ ℓ : M →ₗ[ℂ] ℂ, ℓ z₁ = ∫ k, g k * ℓ (ρ k z) ∂ν) → ∀ w : M,
      ⟪ι z₁, ι w⟫_ℂ = ∫ k, (starRingEnd ℂ) (g k) * ⟪ι (ρ k z), ι w⟫_ℂ ∂ν := by
    intro z z₁ hz₁ w
    have := hz₁ ((innerₛₗ ℂ (ι w)) ∘ₗ ι)
    simp only [LinearMap.comp_apply, innerₛₗ_apply_apply] at this
    rw [← inner_conj_symm, this, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp [inner_conj_symm]

  let P : Submodule ℂ H := D.map ι
  haveI : FiniteDimensional ℂ P := inferInstance
  haveI : CompleteSpace P := FiniteDimensional.complete ℂ P
  obtain ⟨t₀, ht₀D, ht₀⟩ : ∃ t₀ ∈ D, ι t₀ = P.starProjection (ι x) := by
    have : P.starProjection (ι x) ∈ P := by
      rw [Submodule.starProjection_apply]
      exact (P.orthogonalProjection (ι x)).2
    obtain ⟨t, ht, e⟩ := Submodule.mem_map.1 this
    exact ⟨t, ht, e⟩
  have hproj : ∀ d ∈ D, ⟪ι d, ι x⟫_ℂ = ⟪ι d, ι t₀⟫_ℂ := by
    intro d hd
    have hP : ι d ∈ P := Submodule.mem_map_of_mem hd
    have := Submodule.inner_right_of_mem_orthogonal hP (P.sub_starProjection_mem_orthogonal (ι x))
    rw [ht₀]
    rw [← sub_eq_zero, ← inner_sub_right]
    exact this
  have ht₀U : t₀ ∈ U' := hDU ht₀D
  obtain ⟨B, hBfd, htB, hBU, hBst, hBc⟩ := hU' t₀ ht₀U
  haveI := hBfd
  obtain ⟨y, hyB, hy⟩ := exists_weak_integral_sub ν B (fun k => ρ k⁻¹ t₀)
    (fun k => hBst k⁻¹ t₀ htB) (fun k => (starRingEnd ℂ) (g k)) hcg
    (fun ℓ => (hBc ℓ t₀ htB).comp continuous_inv)
  refine ⟨y, hBU hyB, fun z hz => ?_⟩
  obtain ⟨z₁, hz₁S, hz₁⟩ := Z z hz
  have hcancel : ∀ k, ρ k⁻¹ (ρ k z) = z := by
    intro k
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have a1 : ⟪ι z₁, ι x⟫_ℂ = ⟪ι z, ι x⟫_ℂ := by
    rw [I1 z z₁ hz₁ x]
    have := K1 ((innerₛₗ ℂ (ι z)) ∘ₗ ι) x hxA
    simp only [LinearMap.comp_apply, innerₛₗ_apply_apply] at this
    rw [this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have e := h1 k⁻¹ (ρ k z) (hst' k z hz) x hx
    rw [hcancel] at e
    simp only [e]
  have a2 : ⟪ι z₁, ι t₀⟫_ℂ = ⟪ι z, ι y⟫_ℂ := by
    rw [I1 z z₁ hz₁ t₀]
    have := hy ((innerₛₗ ℂ (ι z)) ∘ₗ ι)
    simp only [LinearMap.comp_apply, innerₛₗ_apply_apply] at this
    rw [this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have e := h2 k⁻¹ (ρ k z) (hst' k z hz) t₀ ht₀U
    rw [hcancel] at e
    simp only [e]
  have hz₁D : z₁ ∈ D := Submodule.subset_span hz₁S
  rw [← a1, hproj z₁ hz₁D, a2]

end GlobalTheory.CompanionTheory.FinDiscRepr
