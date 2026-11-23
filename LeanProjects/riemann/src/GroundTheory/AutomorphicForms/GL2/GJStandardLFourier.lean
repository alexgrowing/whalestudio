import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJStandardLTensor
import GroundTheory.AutomorphicForms.RestrictedAddHaarProduct
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.GlobalFields.TateThesis.HeckeLFunction
import GroundTheory.LocalFields.LocalZetaEpsilon

open MeasureTheory Filter Set Topology IsDedekindDomain NumberField NumberField.mixedEmbedding Matrix
open scoped NumberField.AdeleRing RestrictedProduct SchwartzMap Classical ENNReal NNReal ValuativeRel nonZeroDivisors

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal GJMatrix GroundTheory.Global GroundTheory.LocalField

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem integralIndicator_comp_symm {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (z : Fin n × Fin n → F) :
    (integralIndicator F n ∘ (matrixCoordHomeomorph (Fin n) F).symm) z =
      localTensor (fun _ : Fin n × Fin n ↦ (valBall F 0 : Set F).indicator fun _ ↦ (1 : ℂ)) z := by
  simp only [Function.comp_apply, localTensor]
  by_cases h : ∀ p, z p ∈ (𝒪[F] : Set F)
  · rw [integralIndicator, Set.indicator_of_mem]
    · refine (Finset.prod_eq_one fun p _ ↦ ?_).symm
      rw [Set.indicator_of_mem (by rw [coe_valBall_zero]; exact h p)]
    · rw [mem_integralMatrixSet]
      intro i j
      exact h (i, j)
  · push Not at h
    obtain ⟨p, hp⟩ := h
    rw [integralIndicator, Set.indicator_of_notMem]
    · refine (Finset.prod_eq_zero (Finset.mem_univ p) ?_).symm
      rw [Set.indicator_of_notMem (by rw [coe_valBall_zero]; exact hp)]
    · rw [mem_integralMatrixSet]
      intro hall
      exact hp (hall p.1 p.2)

theorem localMatrixFourier_integralIndicator_of_conductor {F : Type*} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (h0 : addCharConductor ψ = 0) :
    localMatrixFourier ψ (integralIndicator F n) = integralIndicator F n := by
  funext y
  rw [localMatrixFourier_eq]
  have hfun : integralIndicator F n ∘ (matrixCoordHomeomorph (Fin n) F).symm =
      localTensor (fun _ : Fin n × Fin n ↦ (valBall F 0 : Set F).indicator fun _ ↦ (1 : ℂ)) :=
    funext (integralIndicator_comp_symm (n := n))
  rw [hfun, localFourierPi_localTensor]
  have hloc : localFourier (selfDualMeasure ψ) ψ ((valBall F 0 : Set F).indicator fun _ ↦ (1 : ℂ)) =
      (valBall F 0 : Set F).indicator fun _ ↦ (1 : ℂ) := by
    funext x
    rw [localFourier_indicator_valBall (selfDualMeasure ψ) hψ hψ1 0 x, h0, sub_zero,
      selfDualMeasure_real_valBall_zero, h0]
    simp
  simp only [hloc]
  have := integralIndicator_comp_symm (F := F) (n := n) (matrixCoordT y)
  rw [← this]
  show integralIndicator F n (Matrix.of fun i j ↦ y j i) = integralIndicator F n y
  unfold integralIndicator
  by_cases hy : ∀ i j, y i j ∈ 𝒪[F]
  · rw [Set.indicator_of_mem (show (Matrix.of fun i j ↦ y j i) ∈ integralMatrixSet F n from
        mem_integralMatrixSet.2 fun i j ↦ hy j i),
      Set.indicator_of_mem (show y ∈ integralMatrixSet F n from mem_integralMatrixSet.2 hy)]
    rfl
  · rw [Set.indicator_of_notMem (show (Matrix.of fun i j ↦ y j i) ∉ integralMatrixSet F n from
        fun h ↦ hy fun i j ↦ mem_integralMatrixSet.1 h j i),
      Set.indicator_of_notMem (show y ∉ integralMatrixSet F n from
        fun h ↦ hy (mem_integralMatrixSet.1 h))]

variable (K) in

def ramifiedPlaces : Finset (HeightOneSpectrum (𝓞 K)) :=
  (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (K := K)
    ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))).toFinset

theorem differentExp_eq_zero {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ ramifiedPlaces K) :
    differentExp v = 0 := by
  by_contra h
  exact hv ((Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (K := K)
    ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))).mem_toFinset.2 h)

theorem addCharConductor_eq_zero {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ ramifiedPlaces K) :
    addCharConductor (localAdelicChar K v) = 0 := by
  rw [addCharConductor_localAdelicChar, differentExp_eq_zero hv, neg_zero]

theorem localMatrixFourier_integralIndicator {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ ramifiedPlaces K) :
    localMatrixFourier (localAdelicChar K v) (integralIndicator (v.adicCompletion K) n) =
      integralIndicator (v.adicCompletion K) n :=
  localMatrixFourier_integralIndicator_of_conductor (continuous_localAdelicChar v)
    (localAdelicChar_ne_one v) (addCharConductor_eq_zero hv)

instance fact_isOpen_integralMatrices : Fact (∀ v : HeightOneSpectrum (𝓞 K),
    IsOpen (integralMatrices (v.adicCompletion K) n : Set (Matrix (Fin n) (Fin n) (v.adicCompletion K)))) :=
  ⟨RestrictedProduct.isOpen_coe_of_forall (Fin n) (AdelicGLn.mem_integralMatrices_adicCompletion K n)
    (fun _ ↦ Valued.isOpen_valuationSubring _)⟩

instance measurableSpace_finMatRes : MeasurableSpace (Πʳ v : HeightOneSpectrum (𝓞 K),
    [Matrix (Fin n) (Fin n) (v.adicCompletion K),
      (integralMatrices (v.adicCompletion K) n : Set (Matrix (Fin n) (Fin n) (v.adicCompletion K)))]) :=
  _root_.borel _

instance borelSpace_finMatRes : BorelSpace (Πʳ v : HeightOneSpectrum (𝓞 K),
    [Matrix (Fin n) (Fin n) (v.adicCompletion K),
      (integralMatrices (v.adicCompletion K) n : Set (Matrix (Fin n) (Fin n) (v.adicCompletion K)))]) :=
  ⟨rfl⟩

variable (K n) in

def finMatHomeomorph : (Fin n × Fin n → FiniteAdeleRing (𝓞 K) K) ≃ₜ
    Πʳ v : HeightOneSpectrum (𝓞 K), [Matrix (Fin n) (Fin n) (v.adicCompletion K),
      (integralMatrices (v.adicCompletion K) n : Set (Matrix (Fin n) (Fin n) (v.adicCompletion K)))] :=
  (matrixCoordHomeomorph (Fin n) (FiniteAdeleRing (𝓞 K) K)).symm.trans
    (RestrictedProduct.matrixHomeomorph (Fin n) (AdelicGLn.mem_integralMatrices_adicCompletion K n)
      (fun _ ↦ Valued.isOpen_valuationSubring _))

variable (K n) in

def finMatEquiv : (Fin n × Fin n → FiniteAdeleRing (𝓞 K) K) ≃ₜ+
    Πʳ v : HeightOneSpectrum (𝓞 K), [Matrix (Fin n) (Fin n) (v.adicCompletion K),
      (integralMatrices (v.adicCompletion K) n : Set (Matrix (Fin n) (Fin n) (v.adicCompletion K)))] :=
  { (finMatHomeomorph K n).toEquiv with
    map_add' := fun x y ↦ RestrictedProduct.ext _ _ fun v ↦ by
      ext i j
      rfl
    continuous_toFun := (finMatHomeomorph K n).continuous
    continuous_invFun := (finMatHomeomorph K n).symm.continuous }

variable (K n) in

def finMatHaar : Measure (Πʳ v : HeightOneSpectrum (𝓞 K), [Matrix (Fin n) (Fin n) (v.adicCompletion K),
      (integralMatrices (v.adicCompletion K) n : Set (Matrix (Fin n) (Fin n) (v.adicCompletion K)))]) :=
  (finiteMeasurePi K (ι := Fin n × Fin n)).map (finMatEquiv K n)

instance isAddHaarMeasure_finMatHaar : (finMatHaar K n).IsAddHaarMeasure := by
  unfold finMatHaar
  infer_instance

theorem coe_integralMatrices_eq_pi {F : Type*} [Field F] [ValuativeRel F] :
    (integralMatrices F n : Set (Matrix (Fin n) (Fin n) F)) =
      (Set.univ.pi fun _ : Fin n ↦ Set.univ.pi fun _ : Fin n ↦ (𝒪[F] : Set F) :
        Set (Fin n → Fin n → F)) :=
  Set.ext fun _ ↦ ⟨fun h i _ j _ ↦ (mem_integralMatrices F n).1 h i j,
    fun h ↦ (mem_integralMatrices F n).2 fun i j ↦ h i (Set.mem_univ i) j (Set.mem_univ j)⟩

variable (K n) in

def matVol (v : HeightOneSpectrum (𝓞 K)) : ℝ≥0∞ :=
  matrixMeasure (selfDualMeasure (localAdelicChar K v))
    (integralMatrices (v.adicCompletion K) n : Set (Matrix (Fin n) (Fin n) (v.adicCompletion K)))

theorem matVol_eq (v : HeightOneSpectrum (𝓞 K)) :
    matVol K n v = ∏ _i : Fin n, ∏ _j : Fin n,
      selfDualMeasure (localAdelicChar K v) (𝒪[v.adicCompletion K] : Set (v.adicCompletion K)) := by
  rw [matVol, coe_integralMatrices_eq_pi, matrixMeasure]
  erw [Measure.pi_pi]
  simp_rw [Measure.pi_pi]

theorem matVol_ne_zero (v : HeightOneSpectrum (𝓞 K)) : matVol K n v ≠ 0 := by
  rw [matVol_eq, selfDualMeasure_integers]
  refine Finset.prod_ne_zero_iff.2 fun _ _ ↦ Finset.prod_ne_zero_iff.2 fun _ _ ↦ ?_
  exact ENNReal.coe_ne_zero.2 (selfDualMeasure_coeff_ne_zero _)

theorem matVol_ne_top (v : HeightOneSpectrum (𝓞 K)) : matVol K n v ≠ ⊤ := by
  rw [matVol_eq, selfDualMeasure_integers]
  exact ENNReal.prod_ne_top fun _ _ ↦ ENNReal.prod_ne_top fun _ _ ↦ ENNReal.coe_ne_top

theorem matVol_of_notMem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ ramifiedPlaces K) : matVol K n v = 1 := by
  rw [matVol_eq, selfDualMeasure_integers, addCharConductor_eq_zero hv]
  simp

variable (K n) in

def locMeas (v : HeightOneSpectrum (𝓞 K)) : Measure (Matrix (Fin n) (Fin n) (v.adicCompletion K)) :=
  (matVol K n v)⁻¹ • matrixMeasure (selfDualMeasure (localAdelicChar K v))

instance isAddHaarMeasure_matrixMeasure_selfDual (v : HeightOneSpectrum (𝓞 K)) :
    (matrixMeasure (selfDualMeasure (localAdelicChar K v)) :
      Measure (Matrix (Fin n) (Fin n) (v.adicCompletion K))).IsAddHaarMeasure := by
  unfold matrixMeasure
  have h : ∀ _ : Fin n, (Measure.pi fun _ : Fin n ↦
      selfDualMeasure (localAdelicChar K v)).IsAddHaarMeasure := fun _ ↦ inferInstance
  exact Measure.pi.isAddHaarMeasure
    (fun _ : Fin n ↦ Measure.pi fun _ : Fin n ↦ selfDualMeasure (localAdelicChar K v))

instance isAddHaarMeasure_locMeas (v : HeightOneSpectrum (𝓞 K)) : (locMeas K n v).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 (matVol_ne_top v))
    (ENNReal.inv_ne_top.2 (matVol_ne_zero v))

theorem locMeas_integralMatrices (v : HeightOneSpectrum (𝓞 K)) :
    locMeas K n v (integralMatrices (v.adicCompletion K) n :
      Set (Matrix (Fin n) (Fin n) (v.adicCompletion K))) = 1 := by
  rw [locMeas, Measure.smul_apply, smul_eq_mul, ← matVol, ENNReal.inv_mul_cancel (matVol_ne_zero v)
    (matVol_ne_top v)]

theorem integral_locMeas (v : HeightOneSpectrum (𝓞 K)) (f : Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ) :
    ∫ x, f x ∂locMeas K n v =
      ((matVol K n v).toReal : ℂ)⁻¹ * ∫ x, f x ∂matrixMeasure (selfDualMeasure (localAdelicChar K v)) := by
  rw [locMeas, integral_smul_measure, ENNReal.toReal_inv, Complex.real_smul, Complex.ofReal_inv]

theorem finiteAdelicChar_eq_finprod (a : FiniteAdeleRing (𝓞 K) K) :
    (finiteAdelicChar K a : ℂ) = ∏ᶠ v, (localAdelicChar K v (a v) : ℂ) := by
  rw [finiteAdelicChar_apply, adelicChar_eq_prod, finiteAdeleInr_fst, finiteAdeleInr_snd]
  have h0 : ∏ w : InfinitePlace K, infiniteAdelicChar K w ((0 : InfiniteAdeleRing K) w) = 1 :=
    Finset.prod_eq_one fun w _ ↦ by
      rw [show (0 : InfiniteAdeleRing K) w = 0 from rfl, AddChar.map_zero_eq_one]
  rw [h0, one_mul]
  exact MonoidHom.map_finprod_of_preimage_one Circle.coeHom (fun x hx ↦ Subtype.ext hx) _

def entriesAtT (v : HeightOneSpectrum (𝓞 K)) (z : Fin n × Fin n → FiniteAdeleRing (𝓞 K) K) :
    Matrix (Fin n) (Fin n) (v.adicCompletion K) :=
  Matrix.of fun i j ↦ z (j, i) v

theorem sum_mul_apply_eq_trace (x z : Fin n × Fin n → FiniteAdeleRing (𝓞 K) K)
    (v : HeightOneSpectrum (𝓞 K)) :
    (∑ p, x p * z p) v = Matrix.trace (entriesAt v x * entriesAtT v z) := by
  have h : (∑ p, x p * z p) v = ∑ p, x p v * z p v :=
    map_sum (RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v) _ _
  rw [h, Matrix.trace, Fintype.sum_prod_type]
  rfl

variable (K n) in

def finConstF : ℝ :=
  (finMatHaar K n).real {X | ∀ v, X v ∈
      (integralMatrices (v.adicCompletion K) n : Set (Matrix (Fin n) (Fin n) (v.adicCompletion K)))} *
    ∏ v ∈ ramifiedPlaces K, ((matVol K n v).toReal)⁻¹

theorem isCompact_integralMatrices (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (integralMatrices (v.adicCompletion K) n :
      Set (Matrix (Fin n) (Fin n) (v.adicCompletion K))) := by
  rw [coe_integralMatrices_eq_pi, ← coe_valBall_zero]
  exact isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_valBall 0

theorem finConstF_ne_zero : finConstF K n ≠ 0 := by
  refine mul_ne_zero (RestrictedAddHaar.measureReal_setOf_forall_mem_pos
    (G := fun v : HeightOneSpectrum (𝓞 K) ↦ Matrix (Fin n) (Fin n) (v.adicCompletion K))
    (fun v ↦ (integralMatrices (v.adicCompletion K) n).toAddSubgroup)
    (fact_isOpen_integralMatrices (K := K) (n := n)).out isCompact_integralMatrices _).ne'
    (Finset.prod_ne_zero_iff.2 fun v _ ↦ inv_ne_zero (ENNReal.toReal_pos (matVol_ne_zero v)
      (matVol_ne_top v)).ne')

theorem finiteFourierPi_tensorFin (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (hS : ∀ v ∈ S, IsSchwartzBruhat (Φ v))
    (h0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n)
    (z : Fin n × Fin n → FiniteAdeleRing (𝓞 K) K) :
    finiteFourierPi K (tensorFin Φ) z = (finConstF K n : ℂ) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), localMatrixFourier (localAdelicChar K v) (Φ v) (entriesAtT v z) := by
  set C : ∀ v : HeightOneSpectrum (𝓞 K), AddSubgroup (Matrix (Fin n) (Fin n) (v.adicCompletion K)) :=
    fun v ↦ (integralMatrices (v.adicCompletion K) n).toAddSubgroup with hCdef
  set F : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ :=
    fun v M ↦ Φ v M * (localAdelicChar K v (Matrix.trace (M * entriesAtT v z)) : ℂ) with hFdef
  set H : (Πʳ v : HeightOneSpectrum (𝓞 K), [Matrix (Fin n) (Fin n) (v.adicCompletion K),
      (integralMatrices (v.adicCompletion K) n : Set (Matrix (Fin n) (Fin n) (v.adicCompletion K)))]) → ℂ :=
    fun X ↦ ∏ᶠ v : HeightOneSpectrum (𝓞 K), F v (X v) with hHdef

  have hΦ1 : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ M ∈ integralMatrices (v.adicCompletion K) n, Φ v M = 1 := by
    intro v hv M hM
    rw [h0 v hv, integralIndicator, Set.indicator_of_mem (mem_integralMatrixSet.2 ((mem_integralMatrices _ n).1 hM))]
    rfl
  have hψ1 : ∀ v : HeightOneSpectrum (𝓞 K), ∀ M ∈ integralMatrices (v.adicCompletion K) n,
      entriesAtT v z ∈ integralMatrices (v.adicCompletion K) n →
        (localAdelicChar K v (Matrix.trace (M * entriesAtT v z)) : ℂ) = 1 := by
    intro v M hM hW
    have hMW : M * entriesAtT v z ∈ integralMatrices (v.adicCompletion K) n := mul_mem hM hW
    have htr : Matrix.trace (M * entriesAtT v z) ∈ v.adicCompletionIntegers K := by
      rw [Matrix.trace]
      refine sum_mem fun i _ ↦ ?_
      have := (mem_integralMatrices _ n).1 hMW i i
      exact (mem_valuationInteger_iff v _).1 this
    rw [localAdelicChar_eq_one_of_mem (mem_localInvDifferent_of_mem htr)]
    rfl
  have hWint : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ (finite_setOf_not_integral z).toFinset →
      entriesAtT v z ∈ integralMatrices (v.adicCompletion K) n := by
    intro v hv
    rw [mem_integralMatrices]
    intro i j
    by_contra h
    apply hv
    rw [Set.Finite.mem_toFinset]
    exact ⟨(j, i), fun h' ↦ h ((mem_valuationInteger_iff v _).2 h')⟩
  have hXfin : ∀ X : (Πʳ v : HeightOneSpectrum (𝓞 K), [Matrix (Fin n) (Fin n) (v.adicCompletion K),
      (integralMatrices (v.adicCompletion K) n : Set (Matrix (Fin n) (Fin n) (v.adicCompletion K)))]),
      {v : HeightOneSpectrum (𝓞 K) | X v ∉ integralMatrices (v.adicCompletion K) n}.Finite :=
    fun X ↦ Filter.eventually_cofinite.1 X.2
  set R := ramifiedPlaces K with hRdef
  set Bz := (finite_setOf_not_integral z).toFinset with hBzdef
  set T := S ∪ R ∪ Bz with hTdef
  have hbox : ∀ X ∈ RestrictedAddHaar.box C T, H X = ∏ v ∈ T, F v (X v) := by
    intro X hX
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ ?_
    by_contra hvT
    apply hv
    have hvS : v ∉ S := fun h ↦ hvT (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hvB : v ∉ Bz := fun h ↦ hvT (Finset.mem_union_right _ h)
    have hXv : X v ∈ integralMatrices (v.adicCompletion K) n := hX v hvT
    show Φ v (X v) * _ = 1
    rw [hΦ1 v hvS _ hXv, hψ1 v _ hXv (hWint v hvB), one_mul]
  have hzero : ∀ X, X ∉ RestrictedAddHaar.box C S → H X = 0 := by
    intro X hX
    simp only [RestrictedAddHaar.mem_box, not_forall] at hX
    obtain ⟨v, hvS, hXv⟩ := hX
    refine finprod_eq_zero _ v ?_ ?_
    · show Φ v (X v) * _ = 0
      rw [h0 v hvS, integralIndicator, Set.indicator_of_notMem, zero_mul]
      exact fun h ↦ hXv ((mem_integralMatrices _ n).2 (mem_integralMatrixSet.1 h))
    · refine (((hXfin X).union S.finite_toSet).union Bz.finite_toSet).subset fun w hw ↦ ?_
      by_contra hc
      simp only [mem_union, mem_ofPred_eq, Finset.mem_coe, not_or, not_not] at hc
      apply hw
      show Φ w (X w) * _ = 1
      rw [hΦ1 w hc.1.2 _ hc.1.1, hψ1 w _ hc.1.1 (hWint w hc.2), one_mul]

  have hfin1 : ∀ x : Fin n × Fin n → FiniteAdeleRing (𝓞 K) K,
      (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦ Φ v (entriesAt v x)).Finite := by
    intro x
    refine ((finite_setOf_not_integral x).union S.finite_toSet).subset fun w hw ↦ ?_
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, Finset.mem_coe, not_or, not_exists, not_not] at hc
    apply hw
    show Φ w (entriesAt w x) = 1
    rw [h0 w hc.2]
    exact integralIndicator_entriesAt fun ij ↦ hc.1 ij
  have hfin2 : ∀ a : FiniteAdeleRing (𝓞 K) K,
      (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦ (localAdelicChar K v (a v) : ℂ)).Finite := by
    intro a
    refine (Filter.eventually_cofinite.1 a.2).subset fun w hw ↦ ?_
    by_contra hc
    apply hw
    have h1 : localAdelicChar K w (a w) = 1 :=
      localAdelicChar_eq_one_of_mem (mem_localInvDifferent_of_mem (not_not.1 hc))
    show ((localAdelicChar K w (a w) : Circle) : ℂ) = 1
    rw [h1]
    rfl
  have h1 : finiteFourierPi K (tensorFin Φ) z = ∫ X, H X ∂finMatHaar K n := by
    rw [finiteFourierPi, finMatHaar, show (finiteMeasurePi K (ι := Fin n × Fin n)).map (finMatEquiv K n) =
      (finiteMeasurePi K (ι := Fin n × Fin n)).map (finMatHomeomorph K n).toMeasurableEquiv from rfl,
      integral_map_equiv]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    show (∏ᶠ v, Φ v (entriesAt v x)) * (finiteAdelicChar K (∑ p, x p * z p) : ℂ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), F v (finMatHomeomorph K n x v)
    rw [finiteAdelicChar_eq_finprod, ← finprod_mul_distrib (hfin1 x) (hfin2 _)]
    refine finprod_congr fun v ↦ ?_
    rw [sum_mul_apply_eq_trace]
    rfl
  have hST : S ⊆ T := fun v h ↦ Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have h2 : ∫ X, H X ∂finMatHaar K n =
      ∫ X in (RestrictedAddHaar.box C T : Set (Πʳ v : HeightOneSpectrum (𝓞 K),
        [Matrix (Fin n) (Fin n) (v.adicCompletion K),
          (integralMatrices (v.adicCompletion K) n : Set (Matrix (Fin n) (Fin n) (v.adicCompletion K)))])),
        H X ∂finMatHaar K n :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun X hX ↦
      hzero X fun h ↦ hX (RestrictedAddHaar.box_mono C hST h)).symm
  have hFc : ∀ v, Measurable (F v) := by
    intro v
    have hΦc : Continuous (Φ v) := by
      by_cases hv : v ∈ S
      · exact (hS v hv).1.continuous
      · rw [h0 v hv]
        exact isSchwartzBruhat_integralIndicator.1.continuous
    exact (hΦc.mul (continuous_subtype_val.comp ((continuous_localAdelicChar v).comp
      ((continuous_id.matrix_mul continuous_const).matrix_trace)))).measurable
  have hν1 : ∀ v : HeightOneSpectrum (𝓞 K), locMeas K n v
      ((C v : AddSubgroup (Matrix (Fin n) (Fin n) (v.adicCompletion K))) :
        Set (Matrix (Fin n) (Fin n) (v.adicCompletion K))) = 1 :=
    fun v ↦ locMeas_integralMatrices v
  have h3 := RestrictedAddHaar.setIntegral_box
    (G := fun v : HeightOneSpectrum (𝓞 K) ↦ Matrix (Fin n) (Fin n) (v.adicCompletion K)) C
    (fact_isOpen_integralMatrices (K := K) (n := n)).out isCompact_integralMatrices (finMatHaar K n)
    (fun v ↦ locMeas K n v) hν1 F hFc T H hbox
  rw [h1, h2]
  refine h3.trans ?_
  have hint : ∀ v, ∫ M, F v M ∂locMeas K n v = ((matVol K n v).toReal : ℂ)⁻¹ *
      localMatrixFourier (localAdelicChar K v) (Φ v) (entriesAtT v z) := fun v ↦ by
    rw [integral_locMeas]
    rfl
  simp_rw [hint, Finset.prod_mul_distrib]
  have hRT : R ⊆ T := fun v h ↦ Finset.mem_union_left _ (Finset.mem_union_right _ h)
  have hκ : ∏ v ∈ T, ((matVol K n v).toReal : ℂ)⁻¹ = ∏ v ∈ R, ((matVol K n v).toReal : ℂ)⁻¹ :=
    (Finset.prod_subset hRT fun v _ hvR ↦ by rw [matVol_of_notMem hvR]; simp).symm
  have hL : ∏ v ∈ T, localMatrixFourier (localAdelicChar K v) (Φ v) (entriesAtT v z) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), localMatrixFourier (localAdelicChar K v) (Φ v) (entriesAtT v z) := by
    refine (finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ ?_).symm
    by_contra hvT
    apply hv
    have hvS : v ∉ S := fun h ↦ hvT (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hvR : v ∉ R := fun h ↦ hvT (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hvB : v ∉ Bz := fun h ↦ hvT (Finset.mem_union_right _ h)
    show localMatrixFourier (localAdelicChar K v) (Φ v) (entriesAtT v z) = 1
    rw [h0 v hvS, localMatrixFourier_integralIndicator hvR, integralIndicator,
      Set.indicator_of_mem (mem_integralMatrixSet.2 ((mem_integralMatrices _ n).1 (hWint v hvB)))]
    rfl
  rw [hκ, hL, finConstF]
  push_cast
  change (?a : ℂ) * ((?p : ℂ) * (?l : ℂ)) = ?a * ?p * ?l
  ring

variable (K n) in

def swapCLE : (Fin n × Fin n → mixedSpace K) ≃L[ℝ] (Fin n × Fin n → mixedSpace K) :=
  (LinearEquiv.funCongrLeft ℝ (mixedSpace K) (Equiv.prodComm (Fin n) (Fin n))).toContinuousLinearEquiv

def archMatrixFourier (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ)) : 𝓢(Fin n × Fin n → mixedSpace K, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (swapCLE K n) (mixedFourierPiSchwartz K φ)

theorem entriesAtT_finPartPi_matrixCoordT (v : HeightOneSpectrum (𝓞 K))
    (y : Matrix (Fin n) (Fin n) 𝔸[K]) :
    entriesAtT v (finPartPi (matrixCoordT y)) = localMat v y := by
  ext i j
  rfl

theorem exists_adelicMatrixFourier_matrixTensor : ∃ C : ℂ, C ≠ 0 ∧
    ∀ (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ)) (S : Finset (HeightOneSpectrum (𝓞 K)))
      (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ),
      (∀ v ∈ S, IsSchwartzBruhat (Φ v)) → (∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n) →
        adelicMatrixFourier K (matrixTensor φ Φ) =
          C • matrixTensor (archMatrixFourier φ) (fun v ↦ localMatrixFourier (localAdelicChar K v) (Φ v)) := by
  refine ⟨(finConstF K n : ℂ), Complex.ofReal_ne_zero.2 finConstF_ne_zero, fun φ S Φ hS h0 ↦ ?_⟩
  funext y
  have hcoord : coordFun (matrixTensor φ Φ) = schwartzBruhatTensorPi φ (tensorFin Φ) := by
    funext z
    rfl
  rw [adelicMatrixFourier_eq, hcoord, adelicFourierPi_schwartzBruhatTensorPi, Pi.smul_apply, smul_eq_mul]
  show (mixedFourierPiSchwartz K φ) (infPartPi (matrixCoordT y)) *
      finiteFourierPi K (tensorFin Φ) (finPartPi (matrixCoordT y)) = _
  rw [finiteFourierPi_tensorFin S Φ hS h0, matrixTensor]
  simp_rw [entriesAtT_finPartPi_matrixCoordT]
  have harch : archSchwartz (archMatrixFourier φ) (archMat y) =
      (mixedFourierPiSchwartz K φ) (infPartPi (matrixCoordT y)) := by
    rw [archSchwartz, archMatrixFourier, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    rfl
  rw [harch]
  ring

theorem localMatrixFourier_tensor_hyps (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (hS : ∀ v ∈ S, IsSchwartzBruhat (Φ v))
    (h0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n) :
    (∀ v ∈ S ∪ ramifiedPlaces K, IsSchwartzBruhat (localMatrixFourier (localAdelicChar K v) (Φ v))) ∧
      ∀ v ∉ S ∪ ramifiedPlaces K,
        localMatrixFourier (localAdelicChar K v) (Φ v) = integralIndicator (v.adicCompletion K) n := by
  refine ⟨fun v _ ↦ ?_, fun v hv ↦ ?_⟩
  · have hΦ : IsSchwartzBruhat (Φ v) := by
      by_cases hvS : v ∈ S
      · exact hS v hvS
      · rw [h0 v hvS]
        exact isSchwartzBruhat_integralIndicator
    exact hΦ.localMatrixFourier (continuous_localAdelicChar v) (localAdelicChar_ne_one v)
  · rw [Finset.mem_union, not_or] at hv
    rw [h0 v hv.1, localMatrixFourier_integralIndicator hv.2]

end GJStandardL

end

end GroundTheory.Automorphic
