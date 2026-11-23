import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasis
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsEqAdelicCharMul
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.FouCoord

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta NumberField NumberField.mixedEmbedding
  IsDedekindDomain MeasureTheory Matrix
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap nonZeroDivisors Classical

set_option synthInstance.maxSize 1000
set_option maxSynthPendingDepth 1

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]

theorem exists_test (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] :
    ∃ f ∈ schwartzBruhatPi K ι, HasCompactSupport f ∧ f 0 = 1 := by
  let β : ContDiffBump (0 : ι → mixedSpace K) := ⟨1, 2, one_pos, one_lt_two⟩
  have hs : HasCompactSupport fun z => ((β z : ℝ) : ℂ) := β.hasCompactSupport.comp_left Complex.ofReal_zero
  let φ : 𝓢(ι → mixedSpace K, ℂ) := hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff)
  let g : (ι → 𝔸ᶠ[K]) → ℂ := finiteTensor fun _ ↦ cosetIndicator (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) 0
  have hg : g ∈ finiteSchwartzBruhatPi K := finiteTensor_mem fun _ ↦ cosetIndicator_mem_finiteSchwartzBruhat _ _
  have hφ : HasCompactSupport φ := hs
  have hgc : HasCompactSupport g := ((mem_finiteSchwartzBruhatPi K).1 hg).2
  refine ⟨schwartzBruhatTensorPi φ g, schwartzBruhatTensorPi_mem φ hg, ?_, ?_⟩
  · let T : (ι → mixedSpace K) × (ι → 𝔸ᶠ[K]) → (ι → 𝔸[K]) :=
      fun p i => ((homeomorphMixedSpace K).symm (p.1 i), p.2 i)
    have hT : Continuous T := continuous_pi fun i =>
      ((homeomorphMixedSpace K).symm.continuous.comp ((continuous_apply i).comp continuous_fst)).prodMk
        ((continuous_apply i).comp continuous_snd)
    refine HasCompactSupport.intro ((hφ.isCompact.prod hgc.isCompact).image hT) fun x hx => ?_
    have hx' : T (infPartPi x, finPartPi x) = x := by
      funext i
      refine Prod.ext ?_ rfl
      exact (homeomorphMixedSpace K).symm_apply_apply _
    show φ (infPartPi x) * g (finPartPi x) = 0
    by_cases h1 : infPartPi x ∈ tsupport φ
    · by_cases h2 : finPartPi x ∈ tsupport g
      · exact absurd ⟨(infPartPi x, finPartPi x), ⟨h1, h2⟩, hx'⟩ hx
      · rw [image_eq_zero_of_notMem_tsupport h2, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
  · have hinf : infPartPi (0 : ι → 𝔸[K]) = 0 := by
      rw [infPartPi_eq_adeleInfHom]
      funext i
      simp
    have hfin : finPartPi (0 : ι → 𝔸[K]) = 0 := by
      rw [finPartPi_eq_adeleFinHom]
      funext i
      simp
    show φ (infPartPi 0) * g (finPartPi 0) = 1
    rw [hinf, hfin]
    have h1 : φ 0 = 1 := by
      show ((β 0 : ℝ) : ℂ) = 1
      rw [β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le), Complex.ofReal_one]
    rw [h1, one_mul]
    simp [g, finiteTensor, cosetIndicator_apply]

section Transfer

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V]
  [BorelSpace V] [DecidableEq ι] (e : V ≃ₜ+ (ι → 𝔸[K]))

def mu0 : Measure V := (adeleMeasurePi K).map e.symm

theorem measurableEmbedding_symm : MeasurableEmbedding e.symm :=
  e.symm.toHomeomorph.measurableEmbedding

variable (G N : Matrix ι ι K) (χ : V → V → ℂ)

theorem integral_selfDual_eq_adelic_fourier
    (hχ : ∀ x y, χ x y = (adelicChar K (∑ i, e x i * (G.map (algebraMap K 𝔸[K]) *ᵥ e y) i) : ℂ))
    (f : V → ℂ) (y : V) :
    ∫ x, f x * χ x y ∂(mu0 e) = adelicFourierPi K (f ∘ e.symm) (G.map (algebraMap K 𝔸[K]) *ᵥ e y) := by
  rw [mu0, (measurableEmbedding_symm e).integral_map, adelicFourierPi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hχ, Function.comp_apply, ContinuousAddEquiv.apply_symm_apply]

variable {G N χ}

theorem fourier_selfDual_coordinates
    (hχ : ∀ x y, χ x y = (adelicChar K (∑ i, e x i * (G.map (algebraMap K 𝔸[K]) *ᵥ e y) i) : ℂ))
    (f : V → ℂ) :
    (fun y => ∫ x, f x * χ x y ∂(mu0 e)) ∘ e.symm =
      fun u => adelicFourierPi K (f ∘ e.symm) (G.map (algebraMap K 𝔸[K]) *ᵥ u) := by
  funext u
  simp only [Function.comp_apply, integral_selfDual_eq_adelic_fourier e G χ hχ, ContinuousAddEquiv.apply_symm_apply]

theorem fourier_selfDual_mem_schwartzBruhat (hNG : N * G = 1) (hGN : G * N = 1)
    (hχ : ∀ x y, χ x y = (adelicChar K (∑ i, e x i * (G.map (algebraMap K 𝔸[K]) *ᵥ e y) i) : ℂ))
    {f : V → ℂ} (hf : f ∘ e.symm ∈ schwartzBruhatPi K ι) :
    (fun y => ∫ x, f x * χ x y ∂(mu0 e)) ∘ e.symm ∈ schwartzBruhatPi K ι := by
  rw [fourier_selfDual_coordinates e hχ]
  exact comp_mulVec_mem_schwartzBruhatPi G N hNG hGN (adelicFourierPi_mem_schwartzBruhatPi hf)

theorem fourier_selfDual_inversion (hNG : N * G = 1) (hGN : G * N = 1) (hs : Gᵀ = G)
    (hχ : ∀ x y, χ x y = (adelicChar K (∑ i, e x i * (G.map (algebraMap K 𝔸[K]) *ᵥ e y) i) : ℂ))
    {f : V → ℂ} (hf : f ∘ e.symm ∈ schwartzBruhatPi K ι) (z : V) :
    ∫ y, (∫ x, f x * χ x y ∂(mu0 e)) * χ y z ∂(mu0 e) = f (-z) := by
  have hT : (N.map (algebraMap K 𝔸[K]))ᵀ * G.map (algebraMap K 𝔸[K]) = 1 := by
    calc (N.map (algebraMap K 𝔸[K]))ᵀ * G.map (algebraMap K 𝔸[K])
        = (N.map (algebraMap K 𝔸[K]))ᵀ * (Gᵀ).map (algebraMap K 𝔸[K]) := by rw [hs]
      _ = (N.map (algebraMap K 𝔸[K]))ᵀ * (G.map (algebraMap K 𝔸[K]))ᵀ := by
          rw [Matrix.transpose_map]
      _ = (G.map (algebraMap K 𝔸[K]) * N.map (algebraMap K 𝔸[K]))ᵀ := by
          rw [Matrix.transpose_mul]
      _ = 1 := by rw [map_mul_map_eq_one _ hGN, Matrix.transpose_one]
  rw [integral_selfDual_eq_adelic_fourier e G χ hχ (fun y => ∫ x, f x * χ x y ∂(mu0 e)) z, fourier_selfDual_coordinates e hχ,
    adelicFourierPi_comp_mulVec G N hNG hGN, Matrix.mulVec_mulVec, hT, Matrix.one_mulVec,
    adelicFourierPi_adelicFourierPi hf]
  simp only [Function.comp_apply, ← map_neg, ContinuousAddEquiv.symm_apply_apply]

instance isAddHaar_selfDualMeasure : (mu0 e).IsAddHaarMeasure :=
  Measure.isAddHaarMeasure_map _ (e.symm : (ι → 𝔸[K]) ≃+ V).toAddMonoidHom e.symm.continuous
    e.symm.surjective e.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact

theorem joinEquiv_eq_at_reference (hNG : N * G = 1) (hGN : G * N = 1) (hs : Gᵀ = G)
    (hχ : ∀ x y, χ x y = (adelicChar K (∑ i, e x i * (G.map (algebraMap K 𝔸[K]) *ᵥ e y) i) : ℂ))
    (dx : Measure V) (hdx : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual dx χ) : dx = mu0 e := by
  haveI : LocallyCompactSpace V := e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology V := e.toHomeomorph.secondCountableTopology
  have hH := hdx.1
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, dx = c • mu0 e := ⟨_, Measure.isAddLeftInvariant_eq_smul dx (mu0 e)⟩
  obtain ⟨f₀, hf₀, hcs, h1⟩ := exists_test K ι
  set Φ : V → ℂ := f₀ ∘ e with hΦ
  have hΦ' : Φ ∘ e.symm = f₀ := by
    funext u
    simp [hΦ]
  have hm : Φ ∘ e.symm ∈ schwartzBruhatPi K ι := hΦ' ▸ hf₀
  have hcont : Continuous Φ := (continuous_of_mem_schwartzBruhatPi hf₀).comp e.continuous
  have hsupp : HasCompactSupport Φ := hcs.comp_homeomorph e.toHomeomorph
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂dx = (c : ℂ) * ∫ x, Φ x * χ x y ∂(mu0 e) := by
    intro y
    rw [hc, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hI0 : Integrable (fun y => ∫ x, Φ x * χ x y ∂(mu0 e)) (mu0 e) := by
    rw [mu0, (measurableEmbedding_symm e).integrable_map_iff]
    exact integrable_of_mem_schwartzBruhatPi (fourier_selfDual_mem_schwartzBruhat e hNG hGN hχ hm)
  have hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂dx) dx := by
    simp only [hT]
    rw [hc]
    exact (hI0.const_mul (c : ℂ)).smul_measure_nnreal
  have h2 := hdx.2 Φ hcont hsupp hI 0
  have h3 := fourier_selfDual_inversion e hNG hGN hs hχ hm 0
  have hval : Φ (-0) = 1 := by
    simp [hΦ, h1]
  simp only [hT] at h2
  rw [hc, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h2
  have h4 : ∫ y, ((c : ℂ) * ∫ x, Φ x * χ x y ∂(mu0 e)) * χ y 0 ∂(mu0 e) =
      (c : ℂ) * ∫ y, (∫ x, Φ x * χ x y ∂(mu0 e)) * χ y 0 ∂(mu0 e) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  rw [h4, h3, hval, mul_one] at h2
  have h5 : (c : ℝ) * c = 1 := by exact_mod_cast h2
  have h6 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
  have h7 : c = 1 := by exact_mod_cast h6
  rw [hc, h7, one_smul]

theorem fou_of_coord (hNG : N * G = 1) (hGN : G * N = 1) (hs : Gᵀ = G)
    (hχ : ∀ x y, χ x y = (adelicChar K (∑ i, e x i * (G.map (algebraMap K 𝔸[K]) *ᵥ e y) i) : ℂ))
    (dx : Measure V) (hdx : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual dx χ)
    {f : V → ℂ} (hf : f ∘ e.symm ∈ schwartzBruhatPi K ι) :
    (fun y => ∫ x, f x * χ x y ∂dx) ∘ e.symm ∈ schwartzBruhatPi K ι ∧
      ∀ z, ∫ y, (∫ x, f x * χ x y ∂dx) * χ y z ∂dx = f (-z) := by
  obtain rfl := joinEquiv_eq_at_reference e hNG hGN hs hχ dx hdx
  exact ⟨fourier_selfDual_mem_schwartzBruhat e hNG hGN hχ hf, fourier_selfDual_inversion e hNG hGN hs hχ hf⟩

end Transfer

section Coords

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def crd (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (M : ℕ) :
    (Fin 1 → Fin M → R ⊗[F] E) ≃ₜ+ (Fin M × Fin d → R) where
  toFun X p := (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2
  invFun Y _ i := (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm fun k => Y (i, k)
  left_inv X := by
    funext a i
    rw [Subsingleton.elim a 0]
    exact (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm_apply_apply (X 0 i)
  right_inv Y := by
    funext p
    obtain ⟨i, k⟩ := p
    exact congrFun ((GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).apply_symm_apply fun k => Y (i, k)) k
  map_add' X Y := by
    funext p
    simp
  continuous_toFun := by
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.2).comp ((GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).continuous.comp
      ((continuous_apply p.1).comp (continuous_apply 0)))
  continuous_invFun := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    exact (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo R b).symm.continuous.comp
      (continuous_pi fun k => continuous_apply (i, k))

theorem crd_apply (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (M : ℕ) (X : Fin 1 → Fin M → R ⊗[F] E) (p : Fin M × Fin d) :
    crd R b M X p = (Algebra.TensorProduct.basis R b).repr (X 0 p.1) p.2 := rfl

theorem repr_map {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S] (f : R →ₐ[F] S) {d : ℕ}
    (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp [hx, hy]

def mx (ι : Type) : (ι → Ainf F) ≃ₜ+ (ι → mixedSpace F) where
  toFun u i := homeomorphMixedSpace F (u i)
  invFun u i := (homeomorphMixedSpace F).symm (u i)
  left_inv u := by
    funext i
    exact (homeomorphMixedSpace F).symm_apply_apply _
  right_inv u := by
    funext i
    exact (homeomorphMixedSpace F).apply_symm_apply _
  map_add' u v := by
    funext i
    simp only [Pi.add_apply, homeomorphMixedSpace_apply]
    exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (u i) (v i)
  continuous_toFun := continuous_pi fun i =>
    (homeomorphMixedSpace F).continuous.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i =>
    (homeomorphMixedSpace F).symm.continuous.comp (continuous_apply i)

def crdInf {d : ℕ} (b : Module.Basis (Fin d) F E) (M : ℕ) :
    (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (Fin M × Fin d → mixedSpace F) :=
  (crd (Ainf F) b M).trans (mx _)

theorem infPartPi_crd {d : ℕ} (b : Module.Basis (Fin d) F E) {M : ℕ}
    (X : Fin 1 → Fin M → AF F ⊗[F] E) :
    infPartPi (crd (AF F) b M X) = crdInf b M (projInf X) := by
  funext p
  show homeomorphMixedSpace F ((crd (AF F) b M X p).1) =
    homeomorphMixedSpace F (crd (Ainf F) b M (projInf X) p)
  rw [crd_apply, crd_apply]
  exact congrArg _ (repr_map (fstA F) b (X 0 p.1) p.2).symm

theorem finPartPi_crd {d : ℕ} (b : Module.Basis (Fin d) F E) {M : ℕ}
    (X : Fin 1 → Fin M → AF F ⊗[F] E) :
    finPartPi (crd (AF F) b M X) = crd (Af F) b M (projFin X) := by
  funext p
  rw [crd_apply]
  exact (repr_map (sndA F) b (X 0 p.1) p.2).symm

theorem exists_schwartz_of_arch {d : ℕ} (b : Module.Basis (Fin d) F E) {M : ℕ}
    {P : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ} (hP : IsSchwartzArch P) :
    ∃ φ : 𝓢(Fin M × Fin d → mixedSpace F, ℂ), ∀ X, φ (crdInf b M X) = P X := by
  obtain ⟨N, e', c1, c2, f, hf⟩ := hP
  let L : (Fin M × Fin d → mixedSpace F) ≃+ (Fin N → ℝ) :=
    ((crdInf b M).symm : (Fin M × Fin d → mixedSpace F) ≃+ _).trans e'
  have hL : Continuous L := c1.comp (crdInf b M).symm.continuous
  have hL' : Continuous L.symm := (crdInf b M).continuous.comp c2
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (L.toRealLinearEquiv hL hL') f, fun X => ?_⟩
  rw [hf X]
  show f (e' ((crdInf b M).symm (crdInf b M X))) = _
  rw [ContinuousAddEquiv.symm_apply_apply]

theorem isSchwartzArch_of_schwartz {d : ℕ} (b : Module.Basis (Fin d) F E) {M : ℕ}
    (φ : 𝓢(Fin M × Fin d → mixedSpace F, ℂ)) : IsSchwartzArch fun X => φ (crdInf b M X) := by
  let eB := (Module.finBasis ℝ (Fin M × Fin d → mixedSpace F)).equivFunL
  let e' : (Fin 1 → Fin M → Ainf F ⊗[F] E) ≃+ _ :=
    ((crdInf b M : _ ≃+ (Fin M × Fin d → mixedSpace F))).trans eB.toLinearEquiv.toAddEquiv
  refine ⟨_, e', eB.continuous.comp (crdInf b M).continuous,
    (crdInf b M).symm.continuous.comp eB.symm.continuous,
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eB.symm φ, fun X => ?_⟩
  show _ = φ (eB.symm (eB (crdInf b M X)))
  rw [ContinuousLinearEquiv.symm_apply_apply]

variable {M n : ℕ}

theorem sb_zero : IsSchwartzBruhat (0 : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun X => by simp⟩

theorem sb_add {Φ Ψ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ} (h : IsSchwartzBruhat Φ)
    (h' : IsSchwartzBruhat Ψ) : IsSchwartzBruhat (Φ + Ψ) := by
  obtain ⟨k, a, c, ha, hc, hs⟩ := h
  obtain ⟨k', a', c', ha', hc', hs'⟩ := h'
  refine ⟨k + k', Fin.append a a', Fin.append c c', fun i => ?_, fun i => ?_, fun X => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ha i
    · rw [Fin.append_right]; exact ha' i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact hc i
    · rw [Fin.append_right]; exact hc' i
  · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply, hs, hs']

theorem sb_smul (c : ℂ) {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ} (h : IsSchwartzBruhat Φ) :
    IsSchwartzBruhat (c • Φ) := by
  obtain ⟨k, a, g, ha, hg, hs⟩ := h
  refine ⟨k, a, fun i => c • g i, ha, fun i => ⟨(hg i).1.comp (c • ·),
    (hg i).2.comp_left (smul_zero c)⟩, fun X => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hs, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

variable [NumberField E]

theorem isSchwartzBruhat_iff {d : ℕ} (b : Module.Basis (Fin d) F E)
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) :
    IsSchwartzBruhat Φ ↔ Φ ∘ (crd (AF F) b M).symm ∈ schwartzBruhatPi F (Fin M × Fin d) := by
  constructor
  · rintro ⟨k, Φinf, Φf, hi, hf, hs⟩
    choose φ hφ using fun i => exists_schwartz_of_arch b (hi i)
    have hg : ∀ i, Φf i ∘ (crd (Af F) b M).symm ∈ finiteSchwartzBruhatPi F := fun i =>
      (mem_finiteSchwartzBruhatPi F).2 ⟨(hf i).1.comp_continuous (crd (Af F) b M).symm.continuous,
        (hf i).2.comp_homeomorph (crd (Af F) b M).symm.toHomeomorph⟩
    have key : Φ ∘ (crd (AF F) b M).symm =
        ∑ i, schwartzBruhatTensorPi (φ i) (Φf i ∘ (crd (Af F) b M).symm) := by
      funext x
      obtain ⟨X, rfl⟩ := (crd (AF F) b M).surjective x
      simp only [Function.comp_apply, ContinuousAddEquiv.symm_apply_apply, Finset.sum_apply,
        schwartzBruhatTensorPi, infPartPi_crd, finPartPi_crd, hφ, hs]
    rw [key]
    exact Submodule.sum_mem _ fun i _ => schwartzBruhatTensorPi_mem _ (hg i)
  · intro h
    have main : ∀ f ∈ schwartzBruhatPi F (Fin M × Fin d),
        IsSchwartzBruhat (f ∘ crd (AF F) b M) := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem G hG =>
        obtain ⟨φ, g, hg, rfl⟩ := hG
        obtain ⟨g1, g2⟩ := (mem_finiteSchwartzBruhatPi F).1 hg
        refine isSchwartzBruhat_of_prod (isSchwartzArch_of_schwartz b φ)
          (Φf := g ∘ crd (Af F) b M) ⟨g1.comp_continuous (crd (Af F) b M).continuous,
            g2.comp_homeomorph (crd (Af F) b M).toHomeomorph⟩ fun X => ?_
        simp only [Function.comp_apply, schwartzBruhatTensorPi, infPartPi_crd, finPartPi_crd]
      | zero => exact sb_zero
      | add G H _ _ hG hH => exact sb_add hG hH
      | smul c G _ hG => exact sb_smul c hG
    have := main _ h
    convert this using 1
    funext X
    simp

end Coords

section Main

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct

theorem fouV_schwartzBruhat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 2 < M →
    ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E),
    SdW F E σ M J (AF F) ψ 1 dx → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ →
    IsSchwartzBruhat (fouV σ J ψ dx Φ) ∧ ∀ z, fouV σ J ψ dx (fouV σ J ψ dx Φ) z = Φ (-z) := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ ψ hψ dx hdx Φ hΦ
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨B, hsym, hdet, -, hR'⟩ := GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord F E σ hCM M J hJ _ b
  obtain ⟨ξ, hξ, hψξ⟩ := GlobalTheory.CompanionTheory.SW.CharDual.exists_eq_adelicChar_mul ψ hψ
  obtain ⟨h1, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI := hBor 1 M
  have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hdet
  have hNG : (ξ⁻¹ • B⁻¹) * (ξ • B) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hξ, one_smul,
      Matrix.nonsing_inv_mul B hu]
  have hGN : (ξ • B) * (ξ⁻¹ • B⁻¹) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hξ, one_smul,
      Matrix.mul_nonsing_inv B hu]
  have hs : (ξ • B)ᵀ = ξ • B := by
    rw [Matrix.transpose_smul, hsym.eq]
  have hχ : ∀ X Y : Fin 1 → Fin M → AF F ⊗[F] E, ψ (BR (AF F) σ J X Y) =
      (adelicChar F (∑ i, crd (AF F) b M X i *
        ((ξ • B).map (algebraMap F (AF F)) *ᵥ crd (AF F) b M Y) i) : ℂ) := by
    intro X Y
    rw [hψξ]
    congr 2
    have e1 : (ξ • B).map (algebraMap F (AF F)) = algebraMap F (AF F) ξ • B.map (algebraMap F (AF F)) := by
      ext i j
      simp
    rw [e1, Matrix.smul_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hh : Algebra.trace (AF F) (AF F ⊗[F] E) (hR (AF F) σ J (X 0) (Y 0)) =
        crd (AF F) b M X ⬝ᵥ (B.map (algebraMap F (AF F)) *ᵥ crd (AF F) b M Y) := (hR' (AF F)).1 (X 0) (Y 0)
    rw [BR, Fin.sum_univ_one, hh, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hf := (isSchwartzBruhat_iff b Φ).1 hΦ
  obtain ⟨c1, c2⟩ := fou_of_coord (crd (AF F) b M) hNG hGN hs hχ dx hdx hf
  exact ⟨(isSchwartzBruhat_iff b _).2 c1, c2⟩

end Main

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.FouCoord
