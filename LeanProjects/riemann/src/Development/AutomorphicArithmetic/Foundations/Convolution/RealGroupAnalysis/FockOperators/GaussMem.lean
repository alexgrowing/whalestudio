import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical SchwartzMap

private theorem mixed_coord {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : V4 F) (i : Fin 4)
    (w : InfinitePlace F) :
    (infPartPi v i).1 ⟨w, IsTotallyReal.isReal w⟩ = TR.pInf F (v i) w := by
  rfl

private theorem pInf_rt_neg {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (hδ : ∀ φ : F →+* ℝ, φ δ < 0) (w : InfinitePlace F) : TR.pInf F (rt δ) w < 0 := by
  have h : TR.pInf F (rt δ) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) δ :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal w) (WithAbs.toAbs _ δ)
  rw [h]
  exact hδ _

private noncomputable def coordLin {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (c : Fin 4 × InfinitePlace F → ℝ) :
    (Fin 4 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4 × InfinitePlace F) where
  toFun u := WithLp.toLp 2 fun p => c p * (u p.1).1 ⟨p.2, IsTotallyReal.isReal p.2⟩
  map_add' u u' := by
    ext p
    simp [mul_add]
  map_smul' a u := by
    ext p
    simp [mul_left_comm]

private theorem coordLin_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (c : Fin 4 × InfinitePlace F → ℝ) (u : Fin 4 → mixedEmbedding.mixedSpace F) (p : Fin 4 × InfinitePlace F) :
    coordLin c u p = c p * (u p.1).1 ⟨p.2, IsTotallyReal.isReal p.2⟩ := by
  rfl

private theorem coordLin_inj {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (c : Fin 4 × InfinitePlace F → ℝ) (hc : ∀ p, c p ≠ 0) : LinearMap.ker (coordLin c) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro u hu
  funext i
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · have h := congrArg (fun y : EuclideanSpace ℝ (Fin 4 × InfinitePlace F) => y (i, w.1)) hu
    simp only [coordLin_apply] at h
    exact (mul_eq_zero.1 h).resolve_left (hc _)
  · exact (InfinitePlace.not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1) w.2).elim

private theorem exists_sch {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (hδ : ∀ φ : F →+* ℝ, φ δ < 0) :
    ∃ f : 𝓢(Fin 4 → mixedEmbedding.mixedSpace F, ℂ), ∀ v : V4 F, f (infPartPi v) = gauss δ v := by
  let k : Fin 4 × InfinitePlace F → ℝ := fun p => ![1, 1, 2, -2 * TR.pInf F (rt δ) p.2] p.1
  have hk : ∀ p, 0 < k p := by
    rintro ⟨i, w⟩
    have hd := pInf_rt_neg δ hδ w
    fin_cases i <;> simp [k] <;> linarith
  let c : Fin 4 × InfinitePlace F → ℝ := fun p => Real.sqrt (k p)
  have hc : ∀ p, c p ≠ 0 := fun p => (Real.sqrt_pos.2 (hk p)).ne'
  obtain ⟨K, -, hK⟩ := LinearMap.exists_antilipschitzWith (coordLin c) (coordLin_inj c hc)
  let T := LinearMap.toContinuousLinearMap (coordLin c)
  have hT : ∀ u, T u = coordLin c u := fun _ => rfl
  have hg : Function.HasTemperateGrowth T := T.hasTemperateGrowth
  have hK' : AntilipschitzWith K T := hK
  refine ⟨SchwartzMap.compCLMOfAntilipschitz ℂ hg hK' (gaussianSchwartz _), fun v => ?_⟩
  have hn : ‖T (infPartPi v)‖ ^ 2 = ∑ w, TR.pInf F (v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)) w := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hs : ∀ i, (T (infPartPi v) (i, w)) ^ 2 = k (i, w) * TR.pInf F (v i) w ^ 2 := fun i => by
      rw [hT, coordLin_apply, mixed_coord, mul_pow, Real.sq_sqrt (hk _).le]
    simp only [hs, Fin.sum_univ_four, k, map_add, map_mul, map_sub, map_pow, map_ofNat, Pi.add_apply,
      Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.ofNat_apply]
    simp
    ring
  rw [SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply, gaussianSchwartz_apply, hn, gauss]
  push_cast
  rfl

theorem UpperTheory.ConvolutionTheory.R2.Fo.gaussMem :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), ∀ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), (fun v => gauss D.δ v * g (finPartPi v)) ∈ schwartzBruhatPi F (Fin 4) := by
  intro F E _ _ _ _ _ _ _ D g hg
  obtain ⟨f, hf⟩ := exists_sch D.δ D.neg
  have h : (fun v => gauss D.δ v * g (finPartPi v)) = schwartzBruhatTensorPi f g := by
    funext v
    simp only [schwartzBruhatTensorPi, hf]
  rw [h]
  exact schwartzBruhatTensorPi_mem f hg
