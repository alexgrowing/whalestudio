import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def embLinear (σ : K →+* ℂ) : K →ₗ[𝓞 K] ComplexAt σ where
  toFun x := ofComplex σ (σ x)
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    rw [RingHom.id_apply, smul_def, Algebra.smul_def, map_mul, map_mul]

def fieldCoord (σ : K →+* ℂ) : Fibre σ K →ₗ[ℂ] ℂ :=
  (ofComplex σ).symm.toLinearEquiv.toLinearMap ∘ₗ
    ((embLinear σ).liftBaseChange (ComplexAt σ)).restrictScalars ℂ

theorem fieldCoord_tmul (σ : K →+* ℂ) (z : ComplexAt σ) (x : K) :
    fieldCoord σ (z ⊗ₜ x) = (ofComplex σ).symm z * σ x :=
  rfl

theorem eq_fieldCoord_tmul_one (σ : K →+* ℂ) (t : Fibre σ K) :
    t = ofComplex σ (fieldCoord σ t) ⊗ₜ (1 : K) := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, zero_tmul]
  | tmul z x =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    have hb' : algebraMap (𝓞 K) K b ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact nonZeroDivisors.ne_zero hb
    have hσb : σ (algebraMap (𝓞 K) K b) ≠ 0 := by rwa [map_ne_zero]
    set w : ComplexAt σ := ofComplex σ ((σ (algebraMap (𝓞 K) K b))⁻¹ * (ofComplex σ).symm z)
    have e1 : z = b • w := by
      rw [smul_def]
      apply (ofComplex σ).symm.injective
      simp only [w, map_mul, AlgEquiv.symm_apply_apply]
      rw [← mul_assoc, mul_inv_cancel₀ hσb, one_mul]
    have e2 : b • (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) = a • (1 : K) := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_div_cancel₀ _ hb']
    calc z ⊗ₜ[𝓞 K] (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b)
        = (b • w) ⊗ₜ[𝓞 K] (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) := by rw [← e1]
      _ = w ⊗ₜ[𝓞 K] (a • (1 : K)) := by rw [smul_tmul, e2]
      _ = (a • w) ⊗ₜ[𝓞 K] (1 : K) := (smul_tmul a w 1).symm
      _ = _ := by
        congr 1
        rw [fieldCoord_tmul, smul_def]
        apply (ofComplex σ).symm.injective
        simp only [w, map_mul, AlgEquiv.symm_apply_apply, map_div₀]
        rw [div_eq_mul_inv]
        ring
  | add s t hs ht =>
    rw [map_add, map_add, add_tmul, ← hs, ← ht]

theorem fieldCoord_injective (σ : K →+* ℂ) : Function.Injective (fieldCoord σ) := by
  intro s t h
  rw [eq_fieldCoord_tmul_one σ s, eq_fieldCoord_tmul_one σ t, h]

theorem fieldCoord_conjMap (σ : K →+* ℂ) (t : Fibre σ K) :
    fieldCoord (conjugate σ) (conjMap σ K t) = starRingEnd ℂ (fieldCoord σ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul z x =>
    rw [conjMap_tmul, fieldCoord_tmul, fieldCoord_tmul, map_mul]
    rfl
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

def fieldStdCoord (σ : K →+* ℂ) (n : ℕ) : Fibre σ (Fin n → K) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
  (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
    (LinearMap.pi fun i ↦ fieldCoord σ ∘ₗ LinearMap.proj i) ∘ₗ
      ((piRight (𝓞 K) (ComplexAt σ) (ComplexAt σ) fun _ : Fin n ↦ K).restrictScalars ℂ).toLinearMap

theorem fieldStdCoord_apply (σ : K →+* ℂ) (n : ℕ) (x : Fibre σ (Fin n → K)) (i : Fin n) :
    fieldStdCoord σ n x i = fieldCoord σ (piRight (𝓞 K) (ComplexAt σ) (ComplexAt σ)
      (fun _ : Fin n ↦ K) x i) :=
  rfl

theorem fieldStdCoord_injective (σ : K →+* ℂ) (n : ℕ) : Function.Injective (fieldStdCoord σ n) := by
  intro x y h
  apply (piRight (𝓞 K) (ComplexAt σ) (ComplexAt σ) fun _ : Fin n ↦ K).injective
  funext i
  apply fieldCoord_injective σ
  rw [← fieldStdCoord_apply, ← fieldStdCoord_apply, h]

theorem fieldStdCoord_conjMap (σ : K →+* ℂ) (n : ℕ) (x : Fibre σ (Fin n → K)) (i : Fin n) :
    fieldStdCoord (conjugate σ) n (conjMap σ _ x) i = starRingEnd ℂ (fieldStdCoord σ n x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, PiLp.zero_apply]
  | tmul z f =>
    rw [conjMap_tmul, fieldStdCoord_apply, fieldStdCoord_apply, piRight_apply, piRight_apply,
      piRightHom_tmul, piRightHom_tmul, fieldCoord_tmul, fieldCoord_tmul, map_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, PiLp.add_apply, hx, hy, map_add, PiLp.add_apply, map_add]

variable (K) in

def HermitianNorms.standard (n : ℕ) : HermitianNorms K (Fin n → K) where
  form σ := coreOfInjective (fieldStdCoord σ n) (fieldStdCoord_injective σ n)
  form_conj σ x y := by
    simp only [coreOfInjective_inner, PiLp.inner_apply, RCLike.inner_apply, fieldStdCoord_conjMap,
      map_sum, map_mul, Complex.conj_conj]

variable (K) in

def FullLattice.standard (n : ℕ) : FullLattice K (Fin n → K) where
  carrier := Submodule.span (𝓞 K) (Set.range fun i : Fin n ↦ (Pi.single i 1 : Fin n → K))
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq := by
    have e : (Set.range fun i : Fin n ↦ (Pi.single i 1 : Fin n → K)) =
        Set.range (Pi.basisFun K (Fin n)) :=
      congrArg Set.range (funext fun i ↦ (Pi.basisFun_apply K (Fin n) i).symm)
    rw [Submodule.span_span_of_tower, e, (Pi.basisFun K (Fin n)).span_eq]

example : HermitianBundle K := (HermitianNorms.standard K 2).bundle (FullLattice.standard K 2)

section Local

variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (v : HeightOneSpectrum (𝓞 K))

theorem localLattice_span (S : Set V) :
    localLattice v (Submodule.span (𝓞 K) S) = Submodule.span _ (toLocal v '' S) := by
  apply le_antisymm
  · rw [localLattice, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [toLocal_smul]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem localLattice_isLocalLattice (L : FullLattice K V) :
    IsLocalLattice v (localLattice v L.carrier) := by
  classical
  constructor
  · obtain ⟨S, hS⟩ := L.fg
    refine ⟨S.image (toLocal v), ?_⟩
    rw [Finset.coe_image, ← hS, localLattice_span]
  · set W := Submodule.span (v.adicCompletion K)
      (localLattice v L.carrier : Set (v.adicCompletion K ⊗[K] V))
    have h1 : ∀ x ∈ L.carrier, toLocal v x ∈ W := fun x hx ↦
      Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
    have h2 : ∀ x : V, toLocal v x ∈ W := by
      intro x
      have hx : x ∈ Submodule.span K (L.carrier : Set V) := L.span_eq ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem y hy => exact h1 y hy
      | zero => rw [map_zero]; exact W.zero_mem
      | add y z _ _ hy hz => rw [map_add]; exact W.add_mem hy hz
      | smul c y _ hy =>
        rw [map_smul, ← algebraMap_smul (v.adicCompletion K) c]
        exact W.smul_mem _ hy
    rw [eq_top_iff]
    rintro t -
    induction t using TensorProduct.induction_on with
    | zero => exact W.zero_mem
    | tmul a x =>
      have e : a ⊗ₜ[K] x = a • toLocal v x := by
        rw [toLocal, TensorProduct.mk_apply, smul_tmul', smul_eq_mul, mul_one]
      rw [e]
      exact W.smul_mem a (h2 x)
    | add s t hs ht => exact W.add_mem hs ht

theorem localLattice_baseChange (e : V ≃ₗ[K] V) (L : Submodule (𝓞 K) V)
    (he : L.map (e.toLinearMap.restrictScalars (𝓞 K)) = L) :
    (localLattice v L : Set (v.adicCompletion K ⊗[K] V)) =
      e.baseChange K (v.adicCompletion K) V V '' localLattice v L := by
  set f := ((e.baseChange K (v.adicCompletion K) V V).toLinearMap.restrictScalars
    (v.adicCompletionIntegers K))
  have hf : ∀ x : V, f (toLocal v x) = toLocal v (e x) := fun x ↦ rfl
  change _ = (f : _ → _) '' _
  rw [← Submodule.map_coe, localLattice, Submodule.map_span, Set.image_image]
  simp only [hf]
  have hL : (e : V → V) '' (L : Set V) = L := by
    conv_rhs => rw [← he]
    rw [Submodule.map_coe]
    rfl
  rw [← Set.image_image (toLocal v) (e : V → V), hL]

end Local

theorem nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
  refine ⟨⟨m, hm.isPrime, fun h ↦ NumberField.RingOfIntegers.not_isField K ?_⟩⟩
  exact Ring.isField_iff_maximal_bot.mpr (h ▸ hm)

def swapCoord : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) := LinearEquiv.funCongrLeft K K (Equiv.swap 0 1)

theorem swapCoord_standard :
    (FullLattice.standard K 2).carrier.map ((swapCoord (K := K)).toLinearMap.restrictScalars (𝓞 K)) =
      (FullLattice.standard K 2).carrier := by
  rw [FullLattice.standard, Submodule.map_span, ← Set.range_comp]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨Equiv.swap 0 1 i, ?_⟩
    funext j
    fin_cases i <;> fin_cases j <;> rfl
  · rintro ⟨i, rfl⟩
    refine ⟨Equiv.swap 0 1 i, ?_⟩
    funext j
    fin_cases i <;> fin_cases j <;> rfl

def swapAt (v₀ : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K ⊗[K] (Fin 2 → K)) ≃ₗ[v.adicCompletion K]
      (v.adicCompletion K ⊗[K] (Fin 2 → K)) :=
  open Classical in
  if v = v₀ then swapCoord.baseChange K (v.adicCompletion K) _ _ else 1

theorem swapAt_finite (v₀ : HeightOneSpectrum (𝓞 K)) : {v | swapAt v₀ v ≠ 1}.Finite := by
  refine (Set.finite_singleton v₀).subset fun v hv ↦ ?_
  by_contra h
  rw [Set.mem_singleton_iff] at h
  exact hv (by simp only [swapAt, if_neg h])

theorem localLattice_swapAt (v₀ v : HeightOneSpectrum (𝓞 K)) :
    (localLattice v (FullLattice.standard K 2).carrier : Set _) =
      swapAt v₀ v '' localLattice v (FullLattice.standard K 2).carrier := by
  by_cases h : v = v₀
  · simp only [swapAt, if_pos h]
    exact localLattice_baseChange v swapCoord _ swapCoord_standard
  · simp only [swapAt, if_neg h, LinearEquiv.coe_one, Set.image_id]

end

end GroundTheory.Heights₂.Heights
