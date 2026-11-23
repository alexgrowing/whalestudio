import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Matrix Classical

namespace UpperTheory.Dv.LagrForm

variable {F : Type} [Field F] [NumberField F] {κ ι : Type} [Fintype κ] [Fintype ι]

private theorem hom_mulVec {R S : Type} [CommRing R] [CommRing S] (q : R →+* S) (M : Matrix κ ι R) (x : ι → R) :
    (fun k => q ((M *ᵥ x) k)) = M.map q *ᵥ fun i => q (x i) := by
  funext k
  simp [Matrix.mulVec, dotProduct, map_sum]

private theorem left_inv {R : Type} [CommRing R] (a : F →+* R) (M : Matrix κ ι F) (N : Matrix ι κ F) (h : N * M = 1)
    (x : ι → R) : N.map a *ᵥ (M.map a *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero a) (map_one a), Matrix.one_mulVec]

theorem comp_pureA (M : Matrix κ ι F) (N : Matrix ι κ F) (h : N * M = 1)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ g' ∈ SB (ι → FiniteAdeleRing (𝓞 F) F), ∃ T : SInf F κ →L[ℂ] SInf F ι,
      ∀ f : SInf F κ, (fun x : ι → AF F => pureA F f g (M.map (algebraMap F (AF F)) *ᵥ x)) = pureA F (T f) g' := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := e.toRingHom.comp GlobalTheory.HeisSchA.p1
  let a₁ : F →+* mixedEmbedding.mixedSpace F := q.comp (algebraMap F (AF F))
  let a₂ : F →+* FiniteAdeleRing (𝓞 F) F := GlobalTheory.HeisSchA.p2.comp (algebraMap F (AF F))
  let L : (ι → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    LinearMap.toContinuousLinearMap ((Matrix.mulVecLin (M.map a₁)).restrictScalars ℝ)
  let L' : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] (ι → mixedEmbedding.mixedSpace F) :=
    LinearMap.toContinuousLinearMap ((Matrix.mulVecLin (N.map a₁)).restrictScalars ℝ)
  have hL : ∀ x, L' (L x) = x := fun x => left_inv a₁ M N h x
  have hd : Continuous fun y : ι → FiniteAdeleRing (𝓞 F) F => M.map a₂ *ᵥ y :=
    continuous_const.matrix_mulVec continuous_id
  have hr : Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F => N.map a₂ *ᵥ y :=
    continuous_const.matrix_mulVec continuous_id
  refine ⟨fun y => g (M.map a₂ *ᵥ y), ⟨hg.1.comp_continuous hd, ?_⟩,
    SchwartzMap.compCLM ℂ L.hasTemperateGrowth ⟨1, ‖L'‖, fun x => ?_⟩, fun f => funext fun x => ?_⟩
  · refine HasCompactSupport.intro (hg.2.isCompact.image hr) fun y hy => ?_
    by_contra h0
    exact hy ⟨M.map a₂ *ᵥ y, subset_tsupport _ h0, left_inv a₂ M N h y⟩
  · have h1 := L'.le_opNorm (L x)
    rw [hL] at h1
    have h0 := norm_nonneg L'
    rw [pow_one]
    nlinarith
  · change f (fun k => q ((M.map (algebraMap F (AF F)) *ᵥ x) k)) *
      g (fun k => GlobalTheory.HeisSchA.p2 ((M.map (algebraMap F (AF F)) *ᵥ x) k)) =
      f (M.map a₁ *ᵥ fun i => q (x i)) * g (M.map a₂ *ᵥ fun i => GlobalTheory.HeisSchA.p2 (x i))
    rw [hom_mulVec q, hom_mulVec GlobalTheory.HeisSchA.p2]
    rfl

private theorem exists_left_inv (v : ι → κ → F) (hv : LinearIndependent F v) :
    ∃ N : Matrix ι κ F, N * (Matrix.of v)ᵀ = 1 := by
  have hinj : LinearMap.ker (Matrix.toLin' (Matrix.of v)ᵀ) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have := Fintype.linearIndependent_iff.1 hv c (by
      funext k
      have := congrFun hc k
      simpa [Matrix.mulVec, dotProduct, mul_comm] using this)
    exact funext this
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  refine ⟨LinearMap.toMatrix' G, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', hG, Matrix.toLin'_one]

private theorem schr_zero_eq (ψ : AddChar (AF F) ℂ) (u : ι → (κ → F) × (κ → F)) (φ : (κ → AF F) → ℂ) :
    (fun x : ι → AF F => schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)),
      (fun k => algebraMap F (AF F) ((u j).2 k)))) φ 0) =
    GlobalTheory.AdelicSvNQuad.mulQ ψ (⅟2) (Matrix.of fun i j => algebraMap F (AF F) ((u i).1 ⬝ᵥ (u j).2))
      (fun x => φ (((Matrix.of fun j => (u j).1)ᵀ).map (algebraMap F (AF F)) *ᵥ x)) := by
  funext x
  rw [GlobalTheory.AdelicSvNQuad.mulQ_apply, schr, zero_dotProduct, zero_add, zero_add, GlobalTheory.AdelicSvNQuad.quad]
  congr 3
  · simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, sum_dotProduct, dotProduct_sum,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  · funext k
    simp [Prod.fst_sum, Finset.sum_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem schr_zero_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (u : ι → (κ → F) × (κ → F))
    (hu : LinearIndependent F (fun j => (u j).1))
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ g' ∈ SB (ι → FiniteAdeleRing (𝓞 F) F), ∃ T : SInf F κ →L[ℂ] SInf F ι,
      ∀ f : SInf F κ, (fun x : ι → AF F => schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)),
        (fun k => algebraMap F (AF F) ((u j).2 k)))) (pureA F f g) 0) = pureA F (T f) g' := by
  obtain ⟨N, hN⟩ := exists_left_inv _ hu
  obtain ⟨g₁, hg₁, T₁, h₁⟩ := comp_pureA _ N hN hg
  obtain ⟨g₂, hg₂, T₂, h₂⟩ := GlobalTheory.AdelicSvNQuad.mulQ_pureA ψ hψ (⅟2)
    (Matrix.of fun i j => algebraMap F (AF F) ((u i).1 ⬝ᵥ (u j).2)) hg₁
  refine ⟨g₂, hg₂, T₂.comp T₁, fun f => ?_⟩
  rw [schr_zero_eq, h₁, h₂]
  rfl

theorem schr_zero_mem (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (u : ι → (κ → F) × (κ → F))
    (hu : LinearIndependent F (fun j => (u j).1)) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    (fun x : ι → AF F => schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)),
        (fun k => algebraMap F (AF F) ((u j).2 k)))) φ 0) ∈ schA F ι := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    obtain ⟨g', hg', T, hT⟩ := schr_zero_pureA ψ hψ u hu hg
    exact Submodule.subset_span ⟨T f, g', hg', hT f⟩
  | zero =>
    convert Submodule.zero_mem (schA F ι) using 1
    funext x; simp [schr]
  | add x y _ _ hx hy =>
    convert Submodule.add_mem _ hx hy using 1
    funext x; simp only [schr, Pi.add_apply, mul_add]
  | smul c x _ hx =>
    convert Submodule.smul_mem _ c hx using 1
    funext x; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring

private theorem haar_property_of_scalar_multiples (P : ∀ {m : MeasurableSpace (ι → AF F)}, @Measure (ι → AF F) m → Prop)
    (hP : ∀ c : NNReal, P (c • adeleMeasurePi F (ι := ι)))
    (μ : @Measure (ι → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) : P μ := by
  let _ : MeasurableSpace (AdeleRing (𝓞 F) F) := measurableSpace_adeleRing F
  have : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleRing F
  have hb : BorelSpace (ι → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have key : ∀ (m : MeasurableSpace (ι → AF F)) (_ : m = MeasurableSpace.pi) (μ : @Measure (ι → AF F) m),
      @Measure.IsAddHaarMeasure _ _ _ m μ → P μ := by
    rintro m rfl μ hμ
    rw [Measure.isAddLeftInvariant_eq_smul μ (adeleMeasurePi F)]
    exact hP _
  exact key _ hb.measurable_eq.symm μ hμ

theorem integrable_of_mem {φ : (ι → AF F) → ℂ} (hφ : φ ∈ schA F ι)
    (μ : @Measure (ι → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) : Integrable φ μ := by
  refine haar_property_of_scalar_multiples (fun μ => Integrable φ μ) (fun c => ?_) μ hμ
  rw [GlobalTheory.AdelicSvN.Weyl.schA_eq] at hφ
  exact (integrable_of_mem_schwartzBruhatPi hφ).smul_measure_nnreal

theorem integral_pureA (g : (ι → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (μ : @Measure (ι → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ T : SInf F ι →L[ℂ] ℂ, ∀ f : SInf F ι, ∫ x, pureA F f g x ∂μ = T f := by
  refine haar_property_of_scalar_multiples (fun μ => ∃ T : SInf F ι →L[ℂ] ℂ, ∀ f : SInf F ι, ∫ x, pureA F f g x ∂μ = T f) (fun c => ?_) μ hμ
  have hb : BorelSpace (ι → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  refine ⟨((c : ℂ) * ∫ y, g y ∂(finiteMeasurePi F)) •
    SchwartzMap.integralCLM ℂ (mixedMeasurePi F (ι := ι)), fun f => ?_⟩
  have h := (measurePreserving_splitEquivPi (K := F) (ι := ι)).integral_comp' (fun p => f p.1 * g p.2)
  rw [integral_prod_mul] at h
  rw [integral_smul_nnreal_measure, ContinuousLinearMap.smul_apply, SchwartzMap.integralCLM_apply]
  have h' : ∫ x, pureA F f g x ∂(adeleMeasurePi F) = _ := h
  rw [h', NNReal.smul_def, Complex.real_smul, smul_eq_mul]
  ring

theorem integrable_schr_zero (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (u : ι → (κ → F) × (κ → F))
    (hu : LinearIndependent F (fun j => (u j).1))
    (μ : @Measure (ι → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    Integrable (fun x : ι → AF F => schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)),
        (fun k => algebraMap F (AF F) ((u j).2 k)))) φ 0) μ :=
  integrable_of_mem (schr_zero_mem ψ hψ u hu hφ) μ hμ

theorem integral_schr_zero (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (u : ι → (κ → F) × (κ → F))
    (hu : LinearIndependent F (fun j => (u j).1))
    (μ : @Measure (ι → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ T : SInf F κ →L[ℂ] ℂ, ∀ f : SInf F κ,
      ∫ x, schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)),
        (fun k => algebraMap F (AF F) ((u j).2 k)))) (pureA F f g) 0 ∂μ = T f := by
  obtain ⟨g', -, T, hT⟩ := schr_zero_pureA ψ hψ u hu hg
  obtain ⟨U, hU⟩ := integral_pureA g' μ hμ
  exact ⟨U.comp T, fun f => by rw [hT f, hU]; rfl⟩

end UpperTheory.Dv.LagrForm

end
