import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QmapPres
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.PresOfOrder
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AutOrder
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.galCusp :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (σ : K ≃+* K) (e : G1 K n ≃ₜ* G1 K n),
      (∀ g : G1 K n, ((e g : G1 K n) : AdelicGLn.AdelicGL K n) =
        Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) (g : AdelicGLn.AdelicGL K n)) →
      (∀ g, e g ∈ Gam K n ↔ g ∈ Gam K n) → MeasurePreserving e μ μ → ∀ φ ψ : L2 μ, φ ∈ cuspidalL2 μ →
      ((ψ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
        fun y => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e (Quotient.out y)))) → ψ ∈ cuspidalL2 μ := by
  intro K _ _ n μ _ σ e he hg hp φ ψ hφ hψ r hr hrn
  obtain ⟨h1, -⟩ := qmapPres (Gam K n) μ e hg hp
  obtain ⟨a1, a2, a3⟩ := adBasic K
  have hinv : ∀ (τ : K ≃+* K) a, Formalism.L2.Host.CT.adMap τ.symm (Formalism.L2.Host.CT.adMap τ a) = a := fun τ a => by
    rw [← a3, RingEquiv.self_trans_symm, a2]
  let s : (AutomorphicForm.UPos n r → AdeleRing (𝓞 K) K) ≃ₜ+ (AutomorphicForm.UPos n r → AdeleRing (𝓞 K) K) :=
    { toFun := fun X p => Formalism.L2.Host.CT.adMap σ (X p)
      invFun := fun X p => Formalism.L2.Host.CT.adMap σ.symm (X p)
      left_inv := fun X => funext fun p => hinv σ _
      right_inv := fun X => funext fun p => hinv σ.symm _
      map_add' := fun X Y => funext fun p => map_add _ _ _
      continuous_toFun := continuous_pi fun p => (Formalism.L2.Host.CT.continuous_adMap σ).comp (continuous_apply p)
      continuous_invFun := continuous_pi fun p => (Formalism.L2.Host.CT.continuous_adMap σ.symm).comp (continuous_apply p) }
  set ν := AutomorphicForm.unipMeasure K n r with hν
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : (Measure.map s ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν s
  haveI : (Measure.map s.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν s.symm
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map s ν = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hq : Measure.QuasiMeasurePreserving s.symm ν ν :=
    ⟨s.symm.continuous.measurable, by
      rw [Measure.isAddLeftInvariant_eq_smul (Measure.map s.symm ν) ν]
      exact Measure.smul_absolutelyContinuous⟩
  have hL : ∀ (τ : K ≃+* K) (X : AutomorphicForm.UPos n r → AdeleRing (𝓞 K) K), X ∈ AutomorphicForm.unipLattice K n r →
      (fun p => Formalism.L2.Host.CT.adMap τ (X p)) ∈ AutomorphicForm.unipLattice K n r := by
    rintro τ _ ⟨ξ, rfl⟩
    exact ⟨fun p => τ (ξ p), funext fun p => (a1 τ (ξ p)).symm⟩
  have hD := (AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain (K := K) (n := n) (r := r))
  have hD' : IsAddFundamentalDomain (AutomorphicForm.unipLattice K n r)
      (s.symm ⁻¹' AutomorphicForm.unipFundamentalDomain K n r) ν := by
    refine hD.preimage_of_equiv hq (e := fun g => ⟨s g, hL σ g g.2⟩) ⟨fun a b h => ?_, fun b => ?_⟩ fun g X => ?_
    · exact Subtype.ext (s.injective (congrArg Subtype.val h))
    · exact ⟨⟨s.symm b, hL σ.symm b b.2⟩, Subtype.ext (s.apply_symm_apply _)⟩
    · change s.symm (s g + X) = g + s.symm X
      rw [map_add, s.symm_apply_apply]
  have hu : ∀ X, e (unipOne K n r X) = unipOne K n r (s X) := by
    intro X
    refine Subtype.ext ?_
    rw [he]
    ext i j : 2
    change Formalism.L2.Host.CT.adMap σ (AutomorphicForm.unipMatrix X i j) = AutomorphicForm.unipMatrix (s X) i j
    simp only [AutomorphicForm.unipMatrix, Matrix.add_apply, AutomorphicForm.blockEntry_apply, Matrix.one_apply, map_add]
    congr 1
    · split_ifs <;> simp
    · split_ifs
      · rfl
      · exact map_zero _
  have key : ∀ y, ctFun K n r (fun z => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e (Quotient.out z)))) y =
      (c : ℝ) • constantTermL2 μ r φ (e y) := by
    intro y
    let F : (AutomorphicForm.UPos n r → AdeleRing (𝓞 K) K) → ℂ := fun X => φ (mk (Gam K n) (unipOne K n r X * e y))
    have e1 := setIntegral_map_equiv (μ := ν) s.toHomeomorph.toMeasurableEquiv F
      (s.symm ⁻¹' AutomorphicForm.unipFundamentalDomain K n r)
    have e2 : s.toHomeomorph.toMeasurableEquiv ⁻¹' (s.symm ⁻¹' AutomorphicForm.unipFundamentalDomain K n r) =
        AutomorphicForm.unipFundamentalDomain K n r := by
      ext X
      change s.symm (s X) ∈ AutomorphicForm.unipFundamentalDomain K n r ↔ _
      rw [s.symm_apply_apply]
    rw [e2] at e1
    change ∫ X in _, F X ∂Measure.map s ν = ∫ X in _, F (s X) ∂ν at e1
    rw [hc, Measure.restrict_smul, integral_smul_nnreal_measure] at e1
    have e3 : ∫ X in s.symm ⁻¹' AutomorphicForm.unipFundamentalDomain K n r, F X ∂ν =
        ∫ X in AutomorphicForm.unipFundamentalDomain K n r, F X ∂ν := by
      refine hD'.setIntegral_eq hD fun ξ X => ?_
      change φ (mk (Gam K n) (unipOne K n r (ξ + X) * e y)) = _
      rw [unipOne_add, mul_assoc, mk_mul_of_mem (unipOne_mem_rationalGLOne r ξ)]
    rw [e3] at e1
    simp only [ctFun, constantTermL2, h1, map_mul, hu]
    exact e1.symm
  have h4 : ∀ᵐ y ∂μ, constantTermL2 μ r φ (e y) = 0 := hp.quasiMeasurePreserving.ae ((hφ : IsCuspidalL2 μ φ) r hr hrn)
  filter_upwards [ae_ctFun_congr μ r hψ, h4] with y hy1 hy2
  rw [constantTermL2, hy1, key, hy2, smul_zero, Pi.zero_apply]
