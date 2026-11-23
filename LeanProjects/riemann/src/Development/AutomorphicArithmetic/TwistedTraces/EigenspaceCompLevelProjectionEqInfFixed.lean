import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.FixLev
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C

theorem UpperTheory.eigenspace_comp_levelProjection_eq_inf_fixed :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
        (V : Submodule ℂ (LL μ)) (a : TI K n) (x : ℝ) (P : Finset (Pl K)) (Uv : ∀ v : Pl K, Subgroup (Gw n v)), x ≠ 0 →
        eigIn V (Oinf μ ν a ∘L prj (fixF μ (levOn P Uv))) x =
          (eigIn V (Oinf μ ν a) x ⊓ sphOff μ P) ⊓ ⨅ v ∈ P, fixL μ v (Uv v) := by
  intro K _ _ n hn μ _ ν _ V a x P Uv hx
  obtain ⟨-, hmem, hp1, hp2, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (levOn P Uv)
  obtain ⟨m, hm, -⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ ν
  haveI := hm
  have hcomm : ∀ h, Commute (Oinf μ ν a) (rhoF μ h) := fun h =>
    (UpperTheory.ConvolutionTheory.Tf.opAlg K n μ ν m).2.2.2.2.2.2.2.2 a h
  have hpres : ∀ v ∈ fixF μ (levOn P Uv), Oinf μ ν a v ∈ fixF μ (levOn P Uv) := fun v hv => by
    refine (hmem _).2 fun u hu => ?_
    have h1 : rhoF μ u (Oinf μ ν a v) = Oinf μ ν a (rhoF μ u v) :=
      (DFunLike.congr_fun (hcomm u) v).symm
    rw [h1, (hmem v).1 hv u hu]
  have hfix := UpperTheory.ConvolutionTheory.C.fixLev K n μ P Uv
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  ext w
  have hE : ∀ (A : LL μ →L[ℂ] LL μ), w ∈ eigIn V A x ↔ w ∈ V ∧ A w = (x : ℂ) • w := fun A => by
    simp [eigIn, Module.End.mem_eigenspace_iff]
  have hF : w ∈ fixF μ (levOn P Uv) ↔ w ∈ sphOff μ P ∧ w ∈ ⨅ v ∈ P, fixL μ v (Uv v) := by
    rw [hfix, Submodule.mem_inf]
  rw [Submodule.mem_inf, Submodule.mem_inf, hE, hE]
  constructor
  · rintro ⟨hV, hA⟩
    have hA' : Oinf μ ν a (prj (fixF μ (levOn P Uv)) w) = (x : ℂ) • w := hA
    have hw : w ∈ fixF μ (levOn P Uv) := by
      have h1 : w = (x : ℂ)⁻¹ • Oinf μ ν a (prj (fixF μ (levOn P Uv)) w) := by
        rw [hA', smul_smul, inv_mul_cancel₀ hx', one_smul]
      rw [h1]
      exact Submodule.smul_mem _ _ (hpres _ (hp1 w))
    rw [hp2 w hw] at hA'
    exact ⟨⟨⟨hV, hA'⟩, (hF.1 hw).1⟩, (hF.1 hw).2⟩
  · rintro ⟨⟨⟨hV, hA⟩, h1⟩, h2⟩
    refine ⟨hV, ?_⟩
    show Oinf μ ν a (prj (fixF μ (levOn P Uv)) w) = (x : ℂ) • w
    rw [hp2 w (hF.2 ⟨h1, h2⟩), hA]
