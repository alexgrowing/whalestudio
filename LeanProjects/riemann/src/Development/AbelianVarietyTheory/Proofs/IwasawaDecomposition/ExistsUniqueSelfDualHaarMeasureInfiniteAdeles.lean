import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacterStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversionHaarSymmForm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsUniqueNormed
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralCompContinuousLinearEquiv

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.SdInf

theorem selfDual_map {V W : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [MeasurableSpace W] [BorelSpace W] (e : V ≃+ W) (he : Continuous e) (he' : Continuous e.symm)
    {μ : Measure V} {χ : V → V → ℂ} {χ' : W → W → ℂ} (h : ∀ x y, χ' (e x) (e y) = χ x y)
    (hμ : SelfDual μ χ) : SelfDual (μ.map e) χ' := by
  haveI := hμ.1
  let T : V ≃ₜ W := { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  have hm : MeasurableEmbedding e := T.measurableEmbedding
  refine ⟨e.isAddHaarMeasure_map μ he he', fun Φ hΦ hsup hI z => ?_⟩
  obtain ⟨z, rfl⟩ := e.surjective z
  rw [hm.integrable_map_iff] at hI
  simp only [hm.integral_map, Function.comp_def, h] at hI ⊢
  rw [← map_neg]
  exact hμ.2 (fun x => Φ (e x)) (hΦ.comp he) (hsup.comp_homeomorph T) hI z

theorem existsUnique_of_equiv {V W : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (e : V ≃+ W) (he : Continuous e) (he' : Continuous e.symm) (l : V → V → ℝ)
    (ha : ∀ x x' y, l (x + x') y = l x y + l x' y) (hs : ∀ x y, l x y = l y x)
    (hc : ∀ y, Continuous fun x => l x y) (hn : ∀ x, (∀ y, l x y = 0) → x = 0) :
    ∃! μ : Measure V,
      SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((l x y : ℝ) : ℂ))) :=
  _root_.UpperTheory.Reformulated.B.Yzb9.existsUnique_of_equiv e he he' l ha hs hc hn

theorem exists_log_char {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (f : W → ℂ)
    (hf : Continuous f) (h1 : ∀ x, ‖f x‖ = 1) (hadd : ∀ x y, f (x + y) = f x * f y) :
    ∃ L : W → ℝ, Continuous L ∧ (∀ x y, L (x + y) = L x + L y) ∧
      ∀ x, f x = Complex.exp (2 * Real.pi * Complex.I * ((L x : ℝ) : ℂ)) := by
  let g : W → Circle := fun x => ⟨f x, by simp [Submonoid.unitSphere, h1]⟩
  have hg : Continuous g := hf.subtype_mk _
  have hgadd : ∀ x y, g (x + y) = g x * g y := fun x y => Subtype.ext (hadd x y)
  have h0 : g 0 = 1 := by
    have := hgadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  obtain ⟨G, ⟨hG0, hG⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts ⟨g, hg⟩ 0 0
    (by simp [h0])
  have hG' : ∀ x, Circle.exp (G x) = g x := fun x => congrFun hG x
  have hGadd : ∀ x y, G (x + y) = G x + G y := by
    intro x y
    have hc : Continuous fun y : W => G (x + y) - G x - G y := by fun_prop
    have := Circle.isCoveringMap_exp.const_of_comp hc (fun y y' => by
      simp only [Circle.exp_sub, hG', hgadd]
      simp) y 0
    simp only [add_zero, hG0, sub_self] at this
    linarith
  refine ⟨fun x => G x / (2 * Real.pi), by fun_prop, fun x y => by simp only [hGadd, add_div], fun x => ?_⟩
  have : f x = ((Circle.exp (G x) : Circle) : ℂ) := by rw [hG']
  rw [this, Circle.coe_exp]
  congr 1
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R]

theorem trace_tmul (c : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (c ⊗ₜ[F] e) = c * algebraMap F R (Algebra.trace F E e) := by
  have h1 : (c ⊗ₜ[F] e : R ⊗[F] E) = c • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, smul_eq_mul]
  congr 1
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  ext x
  simp

theorem trace_nondeg [Algebra.IsSeparable F E] (z : R ⊗[F] E)
    (h : ∀ w, Algebra.trace R (R ⊗[F] E) (z * w) = 0) : z = 0 := by
  classical
  let b := Module.finBasis F E
  let b' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b
  have key : ∀ (k) (z : R ⊗[F] E), (Algebra.TensorProduct.basis R b').repr z k =
      Algebra.trace R (R ⊗[F] E) (z * (1 : R) ⊗ₜ[F] b k) := by
    intro k z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_mul]
    | tmul a e =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, trace_tmul, Algebra.TensorProduct.basis_repr_tmul]
      simp [b', LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  refine (Algebra.TensorProduct.basis R b').ext_elem fun k => ?_
  rw [key, h]; simp

variable (σ : E →ₐ[F] E)

omit [FiniteDimensional F E] in
theorem sigR_sigR (hσ : ∀ x, σ (σ x) = x) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = _
    rw [hσ]

theorem trace_sigR (z : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ z) = Algebra.trace R (R ⊗[F] E) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e =>
    show Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] σ e) = _
    rw [trace_tmul, trace_tmul]
    congr 2
    exact Algebra.trace_eq_of_algEquiv
      (AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)) e

variable {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

omit [FiniteDimensional F E] in
theorem BR_add (X X' Y : Fin 1 → Fin M → R ⊗[F] E) :
    BR R σ J (X + X') Y = BR R σ J X Y + BR R σ J X' Y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

omit [FiniteDimensional F E] in
theorem BR_smul (t : R) (X Y : Fin 1 → Fin M → R ⊗[F] E) :
    BR R σ J X (t • Y) = BR R σ J X Y * t := by
  simp only [BR, hR, Formalism.UG.hform, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul,
    smul_eq_mul, mul_comm t, Finset.sum_mul]

theorem BR_symm (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (X Y : Fin 1 → Fin M → R ⊗[F] E) :
    BR R σ J X Y = BR R σ J Y X := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← trace_sigR R σ]
  congr 1
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_sigR R σ hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : sigR R σ (JR R J j i) = JR R J i j := by
    show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
    rw [hJ.1]
  rw [this]; ring

theorem BR_nondeg [Algebra.IsSeparable F E] (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J)
    (X : Fin 1 → Fin M → R ⊗[F] E) (h : ∀ Y, BR R σ J X Y = 0) : X = 0 := by
  have h1 : Matrix.vecMul (fun i => sigR R σ (X 0 i)) (JR R J) = 0 := by
    funext j
    refine trace_nondeg R _ fun w => ?_
    have := h fun _ => Pi.single j w
    simpa [BR, hR, Formalism.UG.hform, Pi.single_apply, Matrix.vecMul, dotProduct, Finset.sum_mul] using this
  have hu : IsUnit (JR R J : Matrix (Fin M) (Fin M) (R ⊗[F] E)).det := by
    have : (JR R J : Matrix (Fin M) (Fin M) (R ⊗[F] E)).det = inclR R J.det :=
      ((inclR R).map_det J).symm
    rw [this]
    exact (Ne.isUnit hJ.2).map _
  have h2 := congrArg (fun v => Matrix.vecMul v (JR R J)⁻¹) h1
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one,
    Matrix.zero_vecMul] at h2
  funext a i
  rw [Subsingleton.elim a 0, ← sigR_sigR R σ hσ (X 0 i), congrFun h2 i]
  simp

theorem BR_continuous [TopologicalSpace R] [IsTopologicalRing R] (Y : Fin 1 → Fin M → R ⊗[F] E) :
    Continuous fun X => BR R σ J X Y := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) := IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ
  unfold BR hR Formalism.UG.hform
  fun_prop

end Alg

theorem exists_equiv_Ainf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ a : Ainf F ≃+ (InfinitePlace F → ℝ), Continuous a ∧ Continuous a.symm := by
  refine ⟨AddEquiv.piCongrRight fun v =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).toAddEquiv, ?_, ?_⟩
  · exact continuous_pi fun v =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).continuous.comp
        (continuous_apply v)
  · exact continuous_pi fun v =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.continuous.comp
        (continuous_apply v)

theorem existsUnique_selfDual_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → (∃! ν, SdR (Ainf F) (psiInf F ψ) ν) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃! μ, SdW F E σ M J (Ainf F) (psiInf F ψ) 1 μ := by
  intro F E _ _ _ _ _ σ hCM ψ hψ
  obtain ⟨hF, -, -, hσ'⟩ := hCM
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply φ.injective
    rw [hσ', hσ', star_star]
  have hnd := (GlobalTheory.T.localComponents_nontrivial_adelic_character F ψ hψ).2.2
  obtain ⟨a, ha, ha'⟩ := exists_equiv_Ainf F
  have hpc : Continuous (psiInf F ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨L₀, hL₀c, hL₀a, hL₀⟩ := exists_log_char (fun u => psiInf F ψ (a.symm u)) (hpc.comp ha')
    (fun u => hψ.2.1 _) (fun u v => by
      simp only [psiInf, map_add, ← AddChar.map_add_eq_mul]
      congr 1
      exact Prod.ext rfl (add_zero _).symm)
  let L : Ainf F → ℝ := fun x => L₀ (a x)
  have hLc : Continuous L := hL₀c.comp ha
  have hLa : ∀ x y, L (x + y) = L x + L y := fun x y => by simp only [L, map_add, hL₀a]
  have hL : ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * ((L x : ℝ) : ℂ)) :=
    fun x => by simpa using hL₀ (a x)
  have hLn : ∀ x, (∀ y, L (x * y) = 0) → x = 0 := fun x h => hnd x fun y => by simp [hL, h]
  refine ⟨?_, fun M J hJ => ?_⟩
  · have := existsUnique_of_equiv a ha ha' (fun s t => L (s * t)) (fun x x' y => by rw [add_mul, hLa])
      (fun x y => by rw [mul_comm]) (fun y => hLc.comp (continuous_id.mul continuous_const)) hLn
    simpa only [SdR, hL] using this
  · simp only [SdW, hL]
    let c := (Algebra.TensorProduct.basis (Ainf F) (Module.finBasis F E)).equivFun
    have hc : Continuous c := IsModuleTopology.continuous_of_linearMap c.toLinearMap
    have hc' : Continuous c.symm := IsModuleTopology.continuous_of_linearMap c.symm.toLinearMap
    let e : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃+
        (Fin 1 → Fin M → Fin (Module.finrank F E) → InfinitePlace F → ℝ) :=
      AddEquiv.piCongrRight fun _ => AddEquiv.piCongrRight fun _ =>
        c.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => a)
    refine existsUnique_of_equiv e ?_ ?_ (fun X Y => L (BR (Ainf F) σ J X Y))
      (fun X X' Y => by rw [BR_add, hLa]) (fun X Y => by rw [BR_symm _ σ J hσ hJ])
      (fun Y => hLc.comp (BR_continuous _ σ J Y))
      (fun X h => BR_nondeg _ σ J hσ hJ X fun Y => hLn _ fun t => by rw [← BR_smul]; exact h _)
    · show Continuous fun (X : Fin 1 → Fin M → Ainf F ⊗[F] E) i j k => a (c (X i j) k)
      fun_prop
    · show Continuous fun (X : Fin 1 → Fin M → Fin (Module.finrank F E) → InfinitePlace F → ℝ) i j =>
        c.symm fun k => a.symm (X i j k)
      fun_prop

end GlobalTheory.GaugeEx.SdInf
