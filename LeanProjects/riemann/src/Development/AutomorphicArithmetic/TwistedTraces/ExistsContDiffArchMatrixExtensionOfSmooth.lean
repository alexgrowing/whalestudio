import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.DixmierMalliavin

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private theorem UpperTheory.exists_smooth_bump_units {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] (h : IsExpLieAlgebra (⊤ : Subgroup 𝔸ˣ) (⊤ : Submodule ℝ 𝔸))
    (κ : (⊤ : Subgroup 𝔸ˣ) → ℝ) (hs : h.IsSmoothFun (fun A => (κ A : ℂ)))
    (hc : HasCompactSupport κ) :
    ∃ β : 𝔸 → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧ HasCompactSupport β ∧
      tsupport β ⊆ Set.range (Units.val : 𝔸ˣ → 𝔸) ∧
      ∀ A : (⊤ : Subgroup 𝔸ˣ), β ((A : 𝔸ˣ) : 𝔸) = κ A := by
  classical
  let ι : (⊤ : Subgroup 𝔸ˣ) → 𝔸 := fun A => ((A : 𝔸ˣ) : 𝔸)
  have hemb : Topology.IsOpenEmbedding ι :=
    Units.isOpenEmbedding_val.comp (IsOpen.isOpenEmbedding_subtypeVal (by simp))
  have hinj := hemb.injective
  let β : 𝔸 → ℝ := Function.extend ι κ 0
  have hβ : ∀ A, β (ι A) = κ A := fun A => hinj.extend_apply _ _ A
  have hβ0 : ∀ x, x ∉ Set.range ι → β x = 0 := fun x hx =>
    Function.extend_apply' _ _ _ (by simpa using hx)
  have hCc : IsCompact (ι '' tsupport κ) := IsCompact.image hc hemb.continuous
  have hCcl := hCc.isClosed
  have hsupp : Function.support β ⊆ ι '' tsupport κ := by
    intro x hx
    by_cases hr : x ∈ Set.range ι
    · obtain ⟨A, rfl⟩ := hr
      refine ⟨A, subset_tsupport _ ?_, rfl⟩
      rw [Function.mem_support, ← hβ]
      exact hx
    · exact absurd (hβ0 x hr) hx
  have hts : tsupport β ⊆ ι '' tsupport κ := closure_minimal hsupp hCcl
  refine ⟨β, ?_, hCc.of_isClosed_subset (isClosed_tsupport β) hts, ?_, hβ⟩
  · rw [contDiff_iff_contDiffAt]
    intro X
    by_cases hX : X ∈ ι '' tsupport κ
    · obtain ⟨g, -, rfl⟩ := hX
      let e := expPartialHomeomorph ℝ 𝔸
      have hF := (h.isSmoothFun_iff.1 hs) g
      have hF' : ContDiff ℝ ∞ fun Y : (⊤ : Submodule ℝ 𝔸) => κ (g * h.expG Y) :=
        Complex.reCLM.contDiff.comp hF
      let gi : 𝔸 := (((g : 𝔸ˣ)⁻¹ : 𝔸ˣ) : 𝔸)
      have hm : ContDiff ℝ ∞ (fun x : 𝔸 => gi * x) := contDiff_const.mul contDiff_id
      have h1 : gi * ι g = 1 := Units.inv_mul _
      have hn : e.target ∈ nhds (gi * ι g) := by
        rw [h1]; exact e.open_target.mem_nhds (one_mem_expPartialHomeomorph_target ℝ _)
      have hl : ContDiffAt ℝ ∞
          (fun x => subspaceProj (⊤ : Submodule ℝ 𝔸) (e.symm (gi * x))) (ι g) :=
        (subspaceProj (⊤ : Submodule ℝ 𝔸)).contDiff.contDiffAt.comp _
          (((contDiffOn_expPartialHomeomorph_symm ℝ _).contDiffAt hn).comp _ hm.contDiffAt)
      refine (hF'.contDiffAt.comp _ hl).congr_of_eventuallyEq ?_
      filter_upwards [hm.continuous.continuousAt.preimage_mem_nhds hn] with x hx
      have hexp : NormedSpace.exp (e.symm (gi * x)) = gi * x := e.right_inv hx
      have key : ι (g * h.expG (subspaceProj (⊤ : Submodule ℝ 𝔸) (e.symm (gi * x)))) = x := by
        simp only [ι, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
        rw [subspaceProj_of_mem Submodule.mem_top, hexp, ← mul_assoc]
        simp [gi]
      rw [Function.comp_apply, ← hβ, key]
    · have hz : β =ᶠ[nhds X] fun _ => (0 : ℝ) := by
        filter_upwards [hCcl.isOpen_compl.mem_nhds hX] with x hx
        by_contra hne
        exact hx (hsupp hne)
      exact contDiffAt_const.congr_of_eventuallyEq hz
  · intro x hx
    obtain ⟨A, -, rfl⟩ := hts hx
    exact ⟨(A : 𝔸ˣ), rfl⟩

theorem UpperTheory.exists_contDiff_archMatrix_extension_of_smooth :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (κ : archGroup K n → ℝ),
        (isExpLieAlgebra K n).IsSmoothFun (fun A => (κ A : ℂ)) → HasCompactSupport κ →
        ∃ β : ArchMatrix K n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧ HasCompactSupport β ∧
          tsupport β ⊆ Set.range (Units.val : ArchUnits K n → ArchMatrix K n) ∧
          ∀ A : archGroup K n, β ((A : ArchUnits K n) : ArchMatrix K n) = κ A := by
  intro K _ _ n κ hs hc
  exact UpperTheory.exists_smooth_bump_units (isExpLieAlgebra K n) κ hs hc
