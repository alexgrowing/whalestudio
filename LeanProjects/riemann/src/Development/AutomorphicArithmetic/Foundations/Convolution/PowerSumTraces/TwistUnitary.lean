import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QmapPres

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.C

theorem UpperTheory.ConvolutionTheory.C.twistUnitary :
    UpperTheory.ConvolutionTheory.C.TwistUnitary := by
  intro K _ _ n μ _ θ
  have hp' : MeasurePreserving θ.e.symm μ μ := θ.pres.symm θ.e.toHomeomorph.toMeasurableEquiv
  have hg' : ∀ g, θ.e.symm g ∈ Gam K n ↔ g ∈ Gam K n := fun g => by
    rw [← θ.mem_gam, θ.e.apply_symm_apply]
  obtain ⟨h1, q1⟩ := UpperTheory.ConvolutionTheory.K.qmapPres (Gam K n) μ θ.e θ.mem_gam θ.pres
  obtain ⟨h2, q2⟩ := UpperTheory.ConvolutionTheory.K.qmapPres (Gam K n) μ θ.e.symm hg' hp'
  let Ul : L2 μ →ₗᵢ[ℂ] L2 μ := Lp.compMeasurePreservingₗᵢ ℂ _ q2
  let Ui : L2 μ →ₗᵢ[ℂ] L2 μ := Lp.compMeasurePreservingₗᵢ ℂ _ q1
  have hUl : ∀ ψ : L2 μ, (Ul ψ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
      fun y => (ψ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (θ.e.symm (Quotient.out y))) :=
    fun ψ => Lp.coeFn_compMeasurePreserving ψ q2
  have hUi : ∀ ψ : L2 μ, (Ui ψ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
      fun y => (ψ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (θ.e (Quotient.out y))) :=
    fun ψ => Lp.coeFn_compMeasurePreserving ψ q1
  have hUθ : ∀ ψ : L2 μ, θ.U ψ = Ul ψ := fun ψ =>
    Lp.ext ((θ.U_spec ψ).trans (hUl ψ).symm)
  have hTS : ∀ y : RightCosetSpace (Gam K n),
      mk (Gam K n) (θ.e.symm (Quotient.out (mk (Gam K n) (θ.e (Quotient.out y))))) = y := fun y => by
    have := h2 (θ.e (Quotient.out y))
    rw [θ.e.symm_apply_apply] at this
    exact this.trans (Quotient.out_eq y)
  have hST : ∀ y : RightCosetSpace (Gam K n),
      mk (Gam K n) (θ.e (Quotient.out (mk (Gam K n) (θ.e.symm (Quotient.out y))))) = y := fun y => by
    have := h1 (θ.e.symm (Quotient.out y))
    rw [θ.e.apply_symm_apply] at this
    exact this.trans (Quotient.out_eq y)
  have hlr : ∀ v : L2 μ, Ul (Ui v) = v := fun v => by
    refine Lp.ext ?_
    filter_upwards [hUl (Ui v), q2.quasiMeasurePreserving.ae_eq_comp (hUi v)] with y a b
    simp only [Function.comp_apply] at b
    rw [a, b, hST]
  have hrl : ∀ v : L2 μ, Ui (Ul v) = v := fun v => by
    refine Lp.ext ?_
    filter_upwards [hUi (Ul v), q1.quasiMeasurePreserving.ae_eq_comp (hUl v)] with y a b
    simp only [Function.comp_apply] at b
    rw [a, b, hTS]
  let U : L2 μ ≃ₗᵢ[ℂ] L2 μ :=
    { toLinearEquiv := LinearEquiv.ofLinear Ul.toLinearMap Ui.toLinearMap
        (LinearMap.ext hlr) (LinearMap.ext hrl)
      norm_map' := Ul.norm_map }
  have hUU : ∀ v, U v = Ul v := fun _ => rfl
  have hcomm : ∀ v, Ul (Pc μ v) = Pc μ (Ul v) := fun v => by
    have := DFunLike.congr_fun θ.U_comm v
    simp only [ContinuousLinearMap.comp_apply] at this
    rwa [hUθ, hUθ] at this
  have hmem : ∀ v : L2 μ, v ∈ cuspidalL2 μ ↔ Pc μ v = v := fun v =>
    (Submodule.starProjection_eq_self_iff).symm
  refine ⟨U, ?_, ?_, ?_⟩
  · ext1 v
    exact (hUθ v).symm
  · intro g v
    rw [hUU, hUU]
    refine Lp.ext ?_
    have r1 := (measurePreserving_rightMul (Γ := Gam K n) μ (θ.e g)).quasiMeasurePreserving
    filter_upwards [hUl (rightRegularRep (Gam K n) μ g v),
      q2.quasiMeasurePreserving.ae_eq_comp (coeFn_rightRegularRep (Gam K n) μ g v),
      coeFn_rightRegularRep (Gam K n) μ (θ.e g) (Ul v),
      r1.ae_eq_comp (hUl v)] with y a b c d
    simp only [Function.comp_apply] at b d
    rw [a, b, c, d]
    congr 1
    obtain ⟨x, rfl⟩ := mk_surjective (Gam K n) y
    have e1 := congrArg (rightMul (Gam K n) g) (h2 x)
    simp only [rightMul_mk] at e1
    rw [rightMul_mk, rightMul_mk, h2 (x * θ.e g), map_mul, θ.e.symm_apply_apply]
    exact e1
  · apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      have hv' := (hmem v).1 hv
      refine (hmem _).2 ?_
      change Pc μ (Ul v) = Ul v
      rw [← hcomm, hv']
    · intro w hw
      refine ⟨Ui w, ?_, hlr w⟩
      have hw' := (hmem w).1 hw
      refine (hmem _).2 ?_
      have : Ul (Pc μ (Ui w)) = Ul (Ui w) := by rw [hcomm, hlr, hw']
      exact Ul.injective this
