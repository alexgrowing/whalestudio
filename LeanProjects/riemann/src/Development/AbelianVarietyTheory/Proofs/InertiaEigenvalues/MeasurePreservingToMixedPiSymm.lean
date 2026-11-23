import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus

noncomputable section

namespace GlobalTheory.ThetaPoisson

open NumberField MeasureTheory Matrix GroundTheory.Global GroundTheory.Automorphic.GJMatrix GlobalTheory.CuspRep
open GroundTheory.Automorphic.GJGlobal.Modulus
open scoped NumberField.AdeleRing nonZeroDivisors SchwartzMap FourierTransform ContDiff Classical ENNReal

section General

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem vecMul_map_inv {R S : Type} [CommRing R] [CommRing S] (ρ : R →+* S) (g : GL (Fin n) R) (x : Fin n → S) :
    (x ᵥ* (g : Matrix (Fin n) (Fin n) R).map ρ) ᵥ* ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map ρ = x := by
  rw [vecMul_vecMul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.map_one _ (map_zero ρ) (map_one ρ), vecMul_one]

theorem comp_vecMul_mem (h : GL (Fin n) 𝔸[K]) {F : (Fin n → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi K (Fin n)) :
    (fun x => F (x ᵥ* (h : Matrix (Fin n) (Fin n) 𝔸[K]))) ∈ schwartzBruhatPi K (Fin n) := by
  let q : 𝔸[K] →+* mixedEmbedding.mixedSpace K :=
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.comp (RingHom.fst (InfiniteAdeleRing K) 𝔸ᶠ[K])
  let p : 𝔸[K] →+* 𝔸ᶠ[K] := RingHom.snd (InfiniteAdeleRing K) 𝔸ᶠ[K]
  let A : (Fin n → mixedEmbedding.mixedSpace K) ≃L[ℝ] (Fin n → mixedEmbedding.mixedSpace K) :=
    LinearEquiv.toContinuousLinearEquiv
      { toFun := fun x => x ᵥ* (h : Matrix (Fin n) (Fin n) 𝔸[K]).map q
        invFun := fun x => x ᵥ* ((h⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]).map q
        map_add' := fun x y => add_vecMul _ _ _
        map_smul' := fun r x => smul_vecMul _ _ _
        left_inv := fun x => vecMul_map_inv q h x
        right_inv := fun x => by simpa using vecMul_map_inv q h⁻¹ x }
  let B : (Fin n → 𝔸ᶠ[K]) ≃ₜ (Fin n → 𝔸ᶠ[K]) :=
      { toFun := fun x => x ᵥ* (h : Matrix (Fin n) (Fin n) 𝔸[K]).map p
        invFun := fun x => x ᵥ* ((h⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K]).map p
        left_inv := fun x => vecMul_map_inv p h x
        right_inv := fun x => by simpa using vecMul_map_inv p h⁻¹ x
        continuous_toFun := continuous_id.matrix_vecMul continuous_const
        continuous_invFun := continuous_id.matrix_vecMul continuous_const }
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    have hg' : (g ∘ B) ∈ finiteSchwartzBruhatPi K :=
      ⟨hg.1.comp_continuous B.continuous, hg.2.comp_homeomorph B⟩
    convert schwartzBruhatTensorPi_mem (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A φ) hg' using 1
    funext x
    have h1 : infPartPi (x ᵥ* (h : Matrix (Fin n) (Fin n) 𝔸[K])) = A (infPartPi x) :=
      funext fun i => RingHom.map_vecMul q _ x i
    have h2 : finPartPi (x ᵥ* (h : Matrix (Fin n) (Fin n) 𝔸[K])) = B (finPartPi x) :=
      funext fun i => RingHom.map_vecMul p _ x i
    simp only [schwartzBruhatTensorPi, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, h1, h2]
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul r G _ hG => exact Submodule.smul_mem _ r hG

theorem adelicFourierPi_comp_vecMul (h : GL (Fin n) 𝔸[K]) (F : (Fin n → 𝔸[K]) → ℂ) (y : Fin n → 𝔸[K]) :
    adelicFourierPi K (fun x => F (x ᵥ* (h : Matrix (Fin n) (Fin n) 𝔸[K]))) y =
      (((IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det h) : ℝ)⁻¹ : ℝ) : ℂ) *
        adelicFourierPi K F (y ᵥ* ((h⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])ᵀ) := by
  set z := y ᵥ* ((h⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])ᵀ with hz
  have hp : ∀ x : Fin n → 𝔸[K], ∑ i, x i * y i = ∑ i, (x ᵥ* (h : Matrix (Fin n) (Fin n) 𝔸[K])) i * z i := by
    intro x
    change x ⬝ᵥ y = (x ᵥ* (h : Matrix (Fin n) (Fin n) 𝔸[K])) ⬝ᵥ z
    rw [hz, vecMul_transpose, dotProduct_mulVec, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      vecMul_one]
  have hm := (vecMulHomeomorph h).measurableEmbedding.integral_map (μ := adeleMeasurePi K)
    (fun x => F x * (adelicChar K (∑ i, x i * z i) : ℂ))
  have hmap : (adeleMeasurePi K).map (vecMulHomeomorph h) = _ := map_vecMul_adeleMeasurePi h
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal
    (inv_nonneg.2 (IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det h)).2.le), Complex.real_smul] at hm
  simp only [adelicFourierPi, hp]
  exact hm.symm

theorem poisson_vecMul (h : GL (Fin n) 𝔸[K]) {F : (Fin n → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi K (Fin n)) :
    Summable (fun ξ : Fin n → K =>
      ‖F ((fun i => algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin n) (Fin n) 𝔸[K]))‖) ∧
    Summable (fun ξ : Fin n → K => ‖adelicFourierPi K F
      ((fun i => algebraMap K 𝔸[K] (ξ i)) ᵥ* ((h⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])ᵀ)‖) ∧
    ∑' ξ : Fin n → K, F ((fun i => algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin n) (Fin n) 𝔸[K])) =
      (((IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det h) : ℝ)⁻¹ : ℝ) : ℂ) *
        ∑' ξ : Fin n → K, adelicFourierPi K F
          ((fun i => algebraMap K 𝔸[K] (ξ i)) ᵥ* ((h⁻¹ : GL (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) 𝔸[K])ᵀ) := by
  obtain ⟨h1, h2, h3⟩ := poisson_of_mem_schwartzBruhatPi (comp_vecMul_mem h hF)
  simp only [adelicFourierPi_comp_vecMul, norm_mul] at h2 h3
  refine ⟨h1, (summable_mul_left_iff ?_).1 h2, h3.trans tsum_mul_left⟩
  exact norm_ne_zero_iff.2 (Complex.ofReal_ne_zero.2
    (inv_ne_zero (IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det h)).2.ne'))

end General

section Complex

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]

def toMixedRing : Cinf E ≃+* mixedEmbedding.mixedSpace E :=
  (infEq E).trans (InfiniteAdeleRing.ringEquiv_mixedSpace E)

theorem toMixedRing_snd (x : Cinf E) (w : {w : InfinitePlace E // w.IsComplex}) :
    (toMixedRing E x).2 w = x w.1 :=
  (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w.1)).apply_symm_apply (x w.1)

theorem isEmpty_isReal : IsEmpty {w : InfinitePlace E // w.IsReal} :=
  ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩

def toMixed : Cinf E ≃L[ℝ] mixedEmbedding.mixedSpace E :=
  LinearEquiv.toContinuousLinearEquiv
    { (toMixedRing E).toAddEquiv with
      map_smul' := fun r x => Prod.ext (funext fun w => ((isEmpty_isReal E).false w).elim)
        (funext fun w => (toMixedRing_snd E _ w).trans (congrArg (r • ·) (toMixedRing_snd E x w).symm)) }

theorem toMixed_apply (x : Cinf E) : toMixed E x = toMixedRing E x := rfl

theorem toMixed_pInf (x : Ad E) : toMixed E (pInf E x) = homeomorphMixedSpace E x.1 :=
  congrArg (InfiniteAdeleRing.ringEquiv_mixedSpace E) ((infEq E).apply_symm_apply x.1)

def placeEquiv : {w : InfinitePlace E // w.IsComplex} ≃ InfinitePlace E :=
  Equiv.subtypeUnivEquiv IsTotallyComplex.isComplex

theorem measurePreserving_toMixed_symm : MeasurePreserving (toMixed E).symm volume volume := by
  have := isEmpty_isReal E
  have : IsProbabilityMeasure (volume : Measure ({w : InfinitePlace E // w.IsReal} → ℝ)) :=
    ⟨by rw [volume_pi, Measure.pi_univ]; simp⟩
  have h := (volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace E => ℂ) (placeEquiv E)).comp
    (measurePreserving_snd (μ := (volume : Measure ({w : InfinitePlace E // w.IsReal} → ℝ))))
  suffices e : ⇑(toMixed E).symm =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : InfinitePlace E => ℂ) (placeEquiv E)) ∘ Prod.snd by
    rw [e]; exact h
  funext y w
  obtain ⟨w, rfl⟩ := (placeEquiv E).surjective w
  simp only [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  conv_rhs => rw [← (toMixed E).apply_symm_apply y]
  exact (toMixedRing_snd E _ w).symm

theorem mixedTraceForm_toMixed (x u : Cinf E) :
    mixedTraceForm E (toMixed E x) (toMixed E u) = ∑ w, 2 * (x w * u w).re := by
  have := isEmpty_isReal E
  rw [mixedTraceForm_apply', Finset.univ_eq_empty, Finset.sum_empty, zero_add, ← (placeEquiv E).sum_comp]
  simp only [toMixed_apply, toMixedRing_snd]
  rfl

variable (n : ℕ)

def toMixedPi : (Fin n → Cinf E) ≃L[ℝ] (Fin n → mixedEmbedding.mixedSpace E) :=
  ContinuousLinearEquiv.piCongrRight fun _ => toMixed E

def infMeasure : Measure (Fin n → Cinf E) :=
  (2 ^ (Fintype.card (InfinitePlace E) * n) : ℝ≥0∞) • volume

theorem measurePreserving_toMixedPi_symm :
    MeasurePreserving (toMixedPi E n).symm (mixedMeasurePi E) (infMeasure E n) := by
  have hc : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := Fintype.card_congr (placeEquiv E)
  have h1 : MeasurePreserving (toMixed E).symm (selfDualMeasure E)
      ((2 ^ Fintype.card (InfinitePlace E) : ℝ≥0∞) • volume) := by
    rw [selfDualMeasure, hc]
    exact (measurePreserving_toMixed_symm E).smul_measure _
  haveI : SigmaFinite ((2 ^ Fintype.card (InfinitePlace E) : ℝ≥0∞) • (volume : Measure (Cinf E))) := by
    have : (2 ^ Fintype.card (InfinitePlace E) : ℝ≥0∞) = ((2 ^ Fintype.card (InfinitePlace E) : NNReal) : ℝ≥0∞) := by
      simp
    rw [this]
    exact inferInstanceAs (SigmaFinite ((2 ^ Fintype.card (InfinitePlace E) : NNReal) • (volume : Measure (Cinf E))))
  have h2 := measurePreserving_pi (fun _ : Fin n => selfDualMeasure E) _ fun _ => h1
  have h3 : (Measure.pi fun _ : Fin n => (2 ^ Fintype.card (InfinitePlace E) : ℝ≥0∞) • (volume : Measure (Cinf E))) =
      infMeasure E n := by
    refine Measure.pi_eq fun s _ => ?_
    simp only [infMeasure, Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, pow_mul, volume_pi_pi]
  rw [h3] at h2
  exact h2

variable {E n}

def infFourier (f : (Fin n → Cinf E) → ℂ) (u : Fin n → Cinf E) : ℂ :=
  ∫ x, f x * (𝐞 (-∑ i, ∑ w, 2 * (x i w * u i w).re) : ℂ) ∂infMeasure E n

theorem adelicChar_sInf_sum (x u : Fin n → Cinf E) :
    (adelicChar E (sInf E (∑ i, x i * u i)) : ℂ) = (𝐞 (-∑ i, ∑ w, 2 * (x i w * u i w).re) : ℂ) := by
  have h := adelicChar_sum_mul_eq_pi (fun i => sInf E (x i)) (fun i => sInf E (u i))
  have h0 : ∀ v : Fin n → Cinf E, finPartPi (fun i => sInf E (v i)) = 0 := fun v => rfl
  have h1 : ∀ v : Fin n → Cinf E, infPartPi (fun i => sInf E (v i)) = fun i => toMixed E (v i) := fun v => rfl
  simp only [h0, h1, mixedPairingPi, mixedTraceForm_toMixed, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at h
  rw [← h, map_sum]
  simp only [map_mul]

def toMixedSch (f : 𝓢(Fin n → Cinf E, ℂ)) : 𝓢(Fin n → mixedEmbedding.mixedSpace E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toMixedPi E n).symm f

theorem mixedFourierPi_toMixedSch (f : 𝓢(Fin n → Cinf E, ℂ)) (u : Fin n → Cinf E) :
    mixedFourierPi E (toMixedSch f) (toMixedPi E n u) = infFourier f u := by
  rw [infFourier, ← (measurePreserving_toMixedPi_symm E n).integral_comp
    (toMixedPi E n).symm.toHomeomorph.measurableEmbedding, mixedFourierPi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  obtain ⟨x, rfl⟩ := (toMixedPi E n).surjective y
  have h : mixedPairingPi E (toMixedPi E n x) (toMixedPi E n u) = ∑ i, ∑ w, 2 * (x i w * u i w).re :=
    Finset.sum_congr rfl fun i _ => mixedTraceForm_toMixed E (x i) (u i)
  simp only [h, toMixedSch, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply, Circle.smul_def, smul_eq_mul]
  exact mul_comm _ _

omit [IsTotallyComplex E] in

def latt (n : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : Set (Fin n → Af E) := {z | ∀ i, z i ∈ idealFiniteAdeles J}

def thetaFn (f : (Fin n → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin n → Af E)
    (y : Fin n → Ad E) : ℂ :=
  f (fun i => pInf E (y i)) * (latt n J).indicator 1 ((fun i => pFin E (y i)) - η)

theorem toMixedPi_pInf (y : Fin n → Ad E) : toMixedPi E n (fun i => pInf E (y i)) = infPartPi y :=
  funext fun i => toMixed_pInf E (y i)

theorem thetaFn_eq (f : 𝓢(Fin n → Cinf E, ℂ)) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin n → Af E) :
    thetaFn f J η = schwartzBruhatTensorPi (toMixedSch f) (finiteTensor fun i => cosetIndicator J (η i)) := by
  funext y
  rw [thetaFn, schwartzBruhatTensorPi, ← toMixedPi_pInf]
  simp only [toMixedSch, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply, finiteTensor, cosetIndicator_apply, Finset.prod_boole, Finset.mem_univ,
    true_implies, Set.indicator_apply, latt, Pi.one_apply]
  rfl

theorem thetaFn_mem (f : 𝓢(Fin n → Cinf E, ℂ)) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin n → Af E) :
    thetaFn f J η ∈ schwartzBruhatPi E (Fin n) := by
  rw [thetaFn_eq]
  exact schwartzBruhatTensorPi_mem _ (finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J (η i))

omit [IsTotallyComplex E] in

theorem finiteMeasurePi_latt (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    (finiteMeasurePi E (latt n J)).toReal = (finiteAdeleMeasure E (idealFiniteAdeles J)).toReal ^ n := by
  have : latt n J = Set.univ.pi fun _ => (idealFiniteAdeles J : Set (Af E)) := by
    ext z; simp [latt]
  rw [this, finiteMeasurePi, Measure.pi_pi]
  simp

theorem adelicFourierPi_thetaFn (f : 𝓢(Fin n → Cinf E, ℂ)) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin n → Af E)
    (y : Fin n → Ad E) :
    adelicFourierPi E (thetaFn f J η) y =
      infFourier f (fun i => pInf E (y i)) * (finiteAdelicChar E (∑ i, η i * pFin E (y i)) : ℂ) *
        (latt n (traceDualIdeal E J)).indicator 1 (fun i => pFin E (y i)) *
        ((finiteMeasurePi E (latt n J)).toReal : ℂ) := by
  rw [thetaFn_eq, adelicFourierPi_schwartzBruhatTensorPi, schwartzBruhatTensorPi, mixedFourierPiSchwartz_apply,
    ← toMixedPi_pInf, mixedFourierPi_toMixedSch, finiteFourierPi_finiteTensor, finiteMeasurePi_latt, addChar_sum]
  simp only [finiteTensor, finiteFourier_cosetIndicator, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Set.indicator_apply, Finset.prod_boole, Finset.mem_univ, true_implies, latt, Pi.one_apply,
    SetLike.mem_coe, Set.mem_setOf_eq, Complex.ofReal_pow]
  change _ * (_ * ((∏ i, (finiteAdelicChar E (η i * pFin E (y i)) : ℂ)) *
    if ∀ i, pFin E (y i) ∈ idealFiniteAdeles (traceDualIdeal E J) then 1 else 0)) = _
  ring

omit [IsTotallyComplex E] in
variable (E) in

def differentUnit : (FractionalIdeal (𝓞 E)⁰ E)ˣ :=
  FractionalIdeal.mk0 E ⟨differentIdeal ℤ (𝓞 E), mem_nonZeroDivisors_of_ne_zero (differentIdeal_ne_bot (A := ℤ))⟩

end Complex

end GlobalTheory.ThetaPoisson
