import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJStandardLEuler
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel

open MeasureTheory Filter Set Topology IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing RestrictedProduct SchwartzMap Classical ENNReal NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal

set_option linter.unusedSectionVars false

section Continuity

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem exists_norm_le_of_cusp (hn : 0 < n) {φ : AdelicGLn.AdelicGL K n → ℂ}
    (hφ : φ ∈ AutomorphicForm.cuspForms K n)
    (hA : ∀ (t : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n), φ (Reduction.centralSection K n t * x) = φ x) :
    ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms hφ
  refine ⟨C, fun y ↦ ?_⟩
  set p := (GJGlobal.splitEquiv (K := K) hn).symm y
  have hy : y = (p.1 : AdelicGLn.AdelicGL K n) * Reduction.centralSection K n p.2 := by
    rw [← GJGlobal.splitEquiv_apply hn p, MeasurableEquiv.apply_symm_apply]
  rw [hy, ← Reduction.centralSection_mul_comm, hA]
  exact hC _ p.1.2

theorem continuous_globalMatrixCoeff (hn : 0 < n) (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure]
    {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ} (h₁ : φ₁ ∈ AutomorphicForm.cuspForms K n)
    (h₂ : φ₂ ∈ AutomorphicForm.cuspForms K n)
    (hA : ∀ (t : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n), φ₁ (Reduction.centralSection K n t * x) = φ₁ x) :
    Continuous (GJGlobal.matrixCoeff μ φ₁ φ₂) := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_le_of_cusp hn h₁ hA
  obtain ⟨C₂, hC₂⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms h₂
  have h1c : Continuous φ₁ := h₁.1.continuous
  have h2c : Continuous φ₂ := h₂.1.continuous
  have hfin : μ (RightCosetSpace.fundamentalDomain (Reduction.rationalGLOne K n)) < ⊤ :=
    GJGlobal.measure_fundamentalDomain_rationalGLOne_lt_top μ
  have : IsFiniteMeasure (μ.restrict (RightCosetSpace.fundamentalDomain (Reduction.rationalGLOne K n))) :=
    isFiniteMeasure_restrict.2 hfin.ne
  refine continuous_of_dominated (bound := fun _ ↦ C₁ * C₂) (fun g ↦ ?_) (fun g ↦ ?_)
    (integrable_const _) (Eventually.of_forall fun x ↦ ?_)
  · exact ((h1c.comp (continuous_subtype_val.mul continuous_const)).mul
      (continuous_star.comp (h2c.comp continuous_subtype_val))).aestronglyMeasurable
  · refine Eventually.of_forall fun x ↦ ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC₁ _) (hC₂ _ x.2) (norm_nonneg _) ((norm_nonneg _).trans (hC₁ 1))
  · exact (h1c.comp (continuous_const.mul continuous_id)).mul continuous_const

end Continuity

theorem hasProd_compl_of_hasProd {ι : Type*} {f : ι → ℂ} {a : ℂ} (h : HasProd f a) (S : Finset ι)
    (hS : ∀ i ∈ S, f i ≠ 0) :
    HasProd (fun i : {i // i ∉ S} ↦ f i) (a / ∏ i ∈ S, f i) := by
  set g : ι → ℂ := (S : Set ι).mulIndicator fun i ↦ (f i)⁻¹ with hg
  have hgp : HasProd g (∏ i ∈ S, (f i)⁻¹) := by
    have : HasProd g (∏ i ∈ S, g i) := hasProd_prod_of_ne_finset_one fun i hi ↦ by
      rw [hg, Set.mulIndicator_of_notMem (by simpa using hi)]
    rwa [Finset.prod_congr rfl fun i hi ↦ by rw [hg, Set.mulIndicator_of_mem (by simpa using hi)]] at this
  have hfg := h.mul hgp
  have heq : (fun i ↦ f i * g i) = ({i | i ∉ S} : Set ι).mulIndicator f := by
    funext i
    by_cases hi : i ∈ S
    · rw [hg, Set.mulIndicator_of_mem (by simpa using hi),
        Set.mulIndicator_of_notMem (by simpa using hi), mul_inv_cancel₀ (hS i hi)]
    · rw [hg, Set.mulIndicator_of_notMem (by simpa using hi),
        Set.mulIndicator_of_mem (by simpa using hi), mul_one]
  rw [heq, Finset.prod_inv_distrib, ← div_eq_mul_inv] at hfg
  exact (hasProd_subtype_iff_mulIndicator (s := {i | i ∉ S})).2 hfg

section Partial

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem differentiable_detPow {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (g : GL (Fin n) F) (w : ℂ) :
    Differentiable ℂ fun s : ℂ ↦ detPow g (s + w) := by
  have hq : (LocalField.residueCard F : ℂ) ≠ 0 := Nat.cast_ne_zero.2 LocalField.residueCard_ne_zero
  simp_rw [detPow_eq_qs_zpow, qs]
  exact ((differentiable_id.add_const w).neg.const_cpow (Or.inl hq)).zpow
    (Or.inl fun s h ↦ hq ((Complex.cpow_eq_zero_iff _ _).1 h).1)

end Partial

section Main

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem detPow_ne_zero' {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (g : GL (Fin n) F) (s : ℂ) : detPow g s ≠ 0 := by
  have hq : (LocalField.residueCard F : ℂ) ≠ 0 := Nat.cast_ne_zero.2 LocalField.residueCard_ne_zero
  rw [detPow_eq_qs_zpow, qs]
  exact zpow_ne_zero _ fun h ↦ hq ((Complex.cpow_eq_zero_iff _ _).1 h).1

theorem archComp_prodEquiv_symm (x : AdelicGLn.InfiniteAdelicGL K n) (y : AdelicGLn.FiniteAdelicGL K n) :
    archComp K n ((AdelicGLn.prodEquiv K n).symm (x, y)) = x := by
  show ((AdelicGLn.prodEquiv K n) ((AdelicGLn.prodEquiv K n).symm (x, y))).1 = x
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem localComp_prodEquiv_symm (v : HeightOneSpectrum (𝓞 K)) (x : AdelicGLn.InfiniteAdelicGL K n)
    (y : AdelicGLn.FiniteAdelicGL K n) :
    localComp n v ((AdelicGLn.prodEquiv K n).symm (x, y)) = AdelicGLn.finiteRestrictedEquiv K n y v := by
  show AdelicGLn.finiteRestrictedEquiv K n
    ((AdelicGLn.prodEquiv K n) ((AdelicGLn.prodEquiv K n).symm (x, y))).2 v = _
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem partialL_converges_meromorphic (hn : 2 ≤ n) (μ : Measure (Reduction.normOneGL K n))
    [μ.IsHaarMeasure] {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ} (h₁ : φ₁ ∈ AutomorphicForm.cuspForms K n)
    (h₂ : φ₂ ∈ AutomorphicForm.cuspForms K n)
    (hA : ∀ (t : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
      φ₁ (Reduction.centralSection K n t * x) = φ₁ x)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {V : HeightOneSpectrum (𝓞 K) → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (ξ : ∀ v, V v)
    (ℓ : ∀ v, Module.Dual ℂ (V v)) (hξ : ∀ v, ξ v ∈ smoothVectors (π v))
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    (hirr : ∀ v ∉ S, (π v).IsIrreducible) (hadm : ∀ v ∉ S, IsAdmissible (π v))
    (z : HeightOneSpectrum (𝓞 K) → Fin n → ℂˣ)
    (hz : ∀ v ∉ S, Spherical.IsSatakeParameter (F := v.adicCompletion K) (π v) (localHaar n v) (z v))
    (fi : AdelicGLn.InfiniteAdelicGL K n → ℂ)
    (hf : ∀ g, GJGlobal.matrixCoeff μ φ₁ φ₂ g = fi (archComp K n g) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)
        (localComp n v g))
    (hf0 : ∃ g, GJGlobal.matrixCoeff μ φ₁ φ₂ g ≠ 0) :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re →
        (∀ v ∉ S, ∀ i, ‖(z v i : ℂ) * qs (v.adicCompletion K) s‖ < 1) ∧
        (∀ v ∉ S, LFunction (F := v.adicCompletion K) (π v) s = ∏ i, (1 - (z v i : ℂ) * qs (v.adicCompletion K) s)⁻¹) ∧
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦
          LFunction (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) (π v) s) (partialL S π s)) ∧
      ∃ Λ D : ℂ → ℂ, Differentiable ℂ Λ ∧ Differentiable ℂ D ∧ (∃ s, D s ≠ 0) ∧
        ∀ s : ℂ, σ < s.re → Λ s = D s * partialL S π s := by
  have hn0 : 0 < n := by omega
  have : NeZero n := ⟨by omega⟩
  set f := GJGlobal.matrixCoeff μ φ₁ φ₂ with hfdef
  have hfc : Continuous f := continuous_globalMatrixCoeff hn0 μ h₁ h₂ hA
  obtain ⟨g₀, hg₀⟩ := hf0
  set c₀ := ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀) with hc₀
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀)).Finite := by
    refine ((finite_setOf_not_mem g₀).union S.finite_toSet).subset fun v hv ↦ ?_
    by_contra hc
    simp only [mem_union, Finset.mem_coe, not_or] at hc
    have hK : localComp n v g₀ ∈ integralGL (v.adicCompletion K) n := by
      by_contra h
      exact hc.1 h
    apply hv
    show ℓ v (π v (localComp n v g₀) (ξ v)) = 1
    rw [(hsph v hc.2).1 _ hK, (hsph v hc.2).2]
  rw [hf g₀] at hg₀
  have hfi0 : fi (archComp K n g₀) ≠ 0 := left_ne_zero_of_mul hg₀
  have hc₀0 : c₀ ≠ 0 := right_ne_zero_of_mul hg₀
  have hloc0 : ∀ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀) ≠ 0 :=
    fun v h ↦ hc₀0 (finprod_eq_zero _ v h hsupp)

  have hfic : Continuous fi := by
    have key : ∀ x, fi x = f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) / c₀ := by
      intro x
      have : f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) = fi x * c₀ := by
        rw [hf, archComp_prodEquiv_symm]
        simp_rw [localComp_prodEquiv_symm]
        rfl
      rw [this, mul_div_cancel_right₀ _ hc₀0]
    have hc : Continuous fun x ↦ f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) / c₀ :=
      (hfc.comp ((AdelicGLn.prodEquiv K n).symm.continuous.comp
        (continuous_id.prodMk continuous_const))).div_const c₀
    exact hc.congr fun x ↦ (key x).symm

  set μi : Measure (AdelicGLn.InfiniteAdelicGL K n) := Measure.haar
  obtain ⟨φ, -, hφne, hZd, s₁, hs₁⟩ := exists_archBump μi hfic hfi0
  have hbump : ∀ v ∈ S, ∃ Φ : Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ, IsSchwartzBruhat Φ ∧
      ∃ a : ℂ, a ≠ 0 ∧ ∀ s : ℂ,
        Integrable (fun g : GL (Fin n) (v.adicCompletion K) ↦ Φ (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) *
          Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g * detPow g (s + ((n : ℂ) - 1) / 2)) (localHaar n v) ∧
        ∫⁻ g : GL (Fin n) (v.adicCompletion K), ‖Φ (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) *
          Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g * detPow g (s + ((n : ℂ) - 1) / 2)‖ₑ ∂localHaar n v ≠ 0 ∧
        zetaIntegral (localHaar n v) Φ (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s =
          a * detPow (localComp n v g₀) (s + ((n : ℂ) - 1) / 2) :=
    fun v _ ↦ exists_localBump (localHaar n v) (π v) (hξ v) (ℓ v) (hloc0 v)
  choose Φb hΦbSB a ha hΦb using hbump
  set Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ :=
    fun v ↦ if h : v ∈ S then Φb v h else integralIndicator (v.adicCompletion K) n with hΦdef
  have hΦS : ∀ v (hv : v ∈ S), Φ v = Φb v hv := fun v hv ↦ by simp only [hΦdef, dif_pos hv]
  have hSB : ∀ v ∈ S, IsSchwartzBruhat (Φ v) := fun v hv ↦ by rw [hΦS v hv]; exact hΦbSB v hv
  have hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n :=
    fun v hv ↦ by simp only [hΦdef, dif_neg hv]
  have hΦmem := matrixTensor_mem φ S Φ hSB hS0
  set aa : HeightOneSpectrum (𝓞 K) → ℂ := fun v ↦ if h : v ∈ S then a v h else 1 with haa
  have haaS : ∀ v (hv : v ∈ S), aa v = a v hv := fun v hv ↦ by simp only [haa, dif_pos hv]

  set ν : Measure (AdelicGLn.AdelicGL K n) := Measure.haar
  obtain ⟨σ₀, Λ, -, hΛ, -, hZ, -, -⟩ :=
    GJGlobal.globalZeta_entire_functionalEquation hn μ ν h₁ h₂ hA hΦmem
  set c : ℂ := (((prodConst ν μi : ℝ) * finConst K n : ℝ) : ℂ) with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef]
    exact_mod_cast (mul_pos (NNReal.coe_pos.2 (prodConst_pos ν μi)) finConst_pos).ne'
  set D : ℂ → ℂ := fun s ↦ c * archZeta μi φ fi s *
    ∏ v ∈ S, (aa v * detPow (localComp n v g₀) (s + ((n : ℂ) - 1) / 2)) with hDdef
  have hmain : ∀ s : ℂ, σ₀ < s.re →
      (∀ v ∉ S, ∀ i, ‖(z v i : ℂ) * qs (v.adicCompletion K) s‖ < 1) ∧
      (∀ v ∉ S, LFunction (F := v.adicCompletion K) (π v) s = ∏ i, (1 - (z v i : ℂ) * qs (v.adicCompletion K) s)⁻¹) ∧
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦
          LFunction (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) (π v) s) (partialL S π s) ∧
      Λ s = D s * partialL S π s := by
    intro s hs
    obtain ⟨hint, hΛs⟩ := hZ s hs
    obtain ⟨hE, hE2⟩ := globalZeta_eq_euler ν μi φ hSB hS0 hξ hsph hfic hf hint
    have hAne : ¬ (archIntegrand φ fi s =ᵐ[μi] 0) := by
      intro h0
      apply hφne s
      have h0' : (fun x ↦ ‖archIntegrand φ fi s x‖ₑ) =ᵐ[μi] 0 :=
        h0.mono fun x hx ↦ by simp [hx]
      rw [lintegral_congr_ae h0']
      simp
    obtain ⟨hBint, hP⟩ := hE2 hAne
    have hlocint : ∀ v, Integrable (localIntegrand Φ π ξ ℓ s v) (localHaar n v) :=
      integrable_factor_finite (localIntegrand Φ π ξ ℓ s)
        (fun v ↦ (continuous_localIntegrand' hSB hS0 hξ s v).measurable)
        (by
          filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv k hk
          exact localIntegrand_eq_one hS0 hsph s hv hk)
        (fun y ↦ rfl) hBint (fun v hv ↦ by
          by_cases hvS : v ∈ S
          · have := (hΦb v hvS s).2.1
            simp only [localIntegrand, hΦS v hvS]
            exact this
          · exact absurd (fun k hk ↦ localIntegrand_eq_one hS0 hsph s hvS hk) hv)

    have hun : ∀ v ∉ S, (∀ i, ‖(z v i : ℂ) * qs (v.adicCompletion K) s‖ < 1) ∧
        zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s =
          ∏ i, (1 - (z v i : ℂ) * qs (v.adicCompletion K) s)⁻¹ := by
      intro v hv
      have hint_v : Integrable (fun g : GL (Fin n) (v.adicCompletion K) ↦
          integralIndicator (v.adicCompletion K) n (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) *
            Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g * detPow g (s + ((n : ℂ) - 1) / 2)) (localHaar n v) := by
        refine (hlocint v).congr (Eventually.of_forall fun g ↦ ?_)
        simp only [localIntegrand, hS0 v hv]
      obtain ⟨hw, heq⟩ := zetaIntegral_sphericalCoeff_of_integrable (localHaar n v) (hz v hv)
        (hsph v hv).1 (hsph v hv).2 hint_v
      refine ⟨hw, ?_⟩
      rw [hS0 v hv, heq, measureReal_def, localHaar_integralGL]
      simp
    have hL : ∀ v ∉ S, LFunction (F := v.adicCompletion K) (π v) s = ∏ i, (1 - (z v i : ℂ) * qs (v.adicCompletion K) s)⁻¹ := by
      intro v hv
      have := hirr v hv
      have hK : fixedVectors (π v) (integralGL (v.adicCompletion K) n) ≠ ⊥ := by
        intro h
        have hmem := (hsph v hv).1
        rw [h, Submodule.mem_bot] at hmem
        have := (hsph v hv).2
        rw [hmem, map_zero] at this
        exact zero_ne_one this
      exact LFunction_eq_prod_of_isSatakeParameter (hadm v hv) hK (localHaar n v) (hz v hv) s

    have hram : ∀ v ∈ S, zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s =
        aa v * detPow (localComp n v g₀) (s + ((n : ℂ) - 1) / 2) := by
      intro v hv
      rw [hΦS v hv, haaS v hv]
      exact (hΦb v hv s).2.2
    have hram0 : ∀ v ∈ S, zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s ≠ 0 := by
      intro v hv
      rw [hram v hv, haaS v hv]
      exact mul_ne_zero (ha v hv) (detPow_ne_zero' _ _)
    have hcompl := hasProd_compl_of_hasProd hP S hram0
    have hcompl' : HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦
          LFunction (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) (π v) s)
        ((∏' v, zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s) /
          ∏ v ∈ S, zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s) := by
      refine hcompl.congr_fun fun v ↦ ?_
      rw [(hun v v.2).2, hL v v.2]
    have hpL : partialL S π s = (∏' v, zetaIntegral (localHaar n v) (Φ v)
        (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s) /
          ∏ v ∈ S, zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s :=
      hcompl'.tprod_eq
    refine ⟨fun v hv ↦ (hun v hv).1, hL, hpL ▸ hcompl', ?_⟩
    have hS0' : ∏ v ∈ S, zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s ≠ 0 :=
      Finset.prod_ne_zero_iff.2 hram0
    rw [← hΛs, hE, hpL, hDdef]
    simp only
    rw [← Finset.prod_congr rfl hram]
    field_simp
    rw [hcdef]
    ring
  refine ⟨σ₀, fun s hs ↦ ⟨(hmain s hs).1, (hmain s hs).2.1, (hmain s hs).2.2.1⟩, Λ, D, hΛ, ?_, ⟨s₁, ?_⟩,
    fun s hs ↦ (hmain s hs).2.2.2⟩
  · have hprod : Differentiable ℂ fun s : ℂ ↦
        ∏ v ∈ S, (aa v * detPow (localComp n v g₀) (s + ((n : ℂ) - 1) / 2)) := by
      have := Differentiable.finsetProd (u := S)
        (f := fun v (s : ℂ) ↦ aa v * detPow (localComp n v g₀) (s + ((n : ℂ) - 1) / 2))
        fun v _ ↦ (differentiable_const _).mul (differentiable_detPow _ _)
      have heq : (fun s : ℂ ↦ ∏ v ∈ S, (aa v * detPow (localComp n v g₀) (s + ((n : ℂ) - 1) / 2))) =
          ∏ v ∈ S, fun s : ℂ ↦ aa v * detPow (localComp n v g₀) (s + ((n : ℂ) - 1) / 2) := by
        funext s
        rw [Finset.prod_apply]
      rw [heq]
      exact this
    exact (hZd.const_mul c).mul hprod
  · refine mul_ne_zero (mul_ne_zero hc hs₁) (Finset.prod_ne_zero_iff.2 fun v hv ↦ ?_)
    rw [haaS v hv]
    exact mul_ne_zero (ha v hv) (detPow_ne_zero' _ _)

theorem partialL_meromorphicOn (hn : 2 ≤ n) (μ : Measure (Reduction.normOneGL K n))
    [μ.IsHaarMeasure] {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ} (h₁ : φ₁ ∈ AutomorphicForm.cuspForms K n)
    (h₂ : φ₂ ∈ AutomorphicForm.cuspForms K n)
    (hA : ∀ (t : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
      φ₁ (Reduction.centralSection K n t * x) = φ₁ x)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {V : HeightOneSpectrum (𝓞 K) → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (ξ : ∀ v, V v)
    (ℓ : ∀ v, Module.Dual ℂ (V v)) (hξ : ∀ v, ξ v ∈ smoothVectors (π v))
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    (hirr : ∀ v ∉ S, (π v).IsIrreducible) (hadm : ∀ v ∉ S, IsAdmissible (π v))
    (z : HeightOneSpectrum (𝓞 K) → Fin n → ℂˣ)
    (hz : ∀ v ∉ S, Spherical.IsSatakeParameter (F := v.adicCompletion K) (π v) (localHaar n v) (z v))
    (fi : AdelicGLn.InfiniteAdelicGL K n → ℂ)
    (hf : ∀ g, GJGlobal.matrixCoeff μ φ₁ φ₂ g = fi (archComp K n g) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)
        (localComp n v g))
    (hf0 : ∃ g, GJGlobal.matrixCoeff μ φ₁ φ₂ g ≠ 0) :
    ∃ σ : ℝ, ∃ L D : ℂ → ℂ, MeromorphicOn L univ ∧ Differentiable ℂ D ∧ (∃ s, D s ≠ 0) ∧
      ∀ s : ℂ, σ < s.re → D s ≠ 0 → L s = partialL S π s := by
  obtain ⟨σ, -, Λ, D, hΛ, hD, hD0, hΛD⟩ := partialL_converges_meromorphic hn μ h₁ h₂ hA S π ξ ℓ hξ hsph
    hirr hadm z hz fi hf hf0
  refine ⟨σ, fun s ↦ Λ s / D s, D, ?_, hD, hD0, fun s hs hs0 ↦ ?_⟩
  · exact ((hΛ.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn).div
      ((hD.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn)
  · show Λ s / D s = _
    rw [hΛD s hs, mul_div_cancel_left₀ _ hs0]

end Main

end GJStandardL

end

end GroundTheory.Automorphic
