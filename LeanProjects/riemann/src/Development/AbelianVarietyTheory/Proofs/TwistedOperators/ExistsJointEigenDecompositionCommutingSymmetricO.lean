import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionSmoothCommuting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightTranslateCommutesCenterAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmOfMemGkGen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.JointSpectral

theorem exists_finset_joint_eigen : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (Z : Submodule ℂ E), FiniteDimensional ℂ Z →
    (∀ i, ∀ x ∈ Z, F i x ∈ Z) → (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ Z, F i (a • x) = a • F i x) → (∀ i j, ∀ x ∈ Z, F i (F j x) = F j (F i x)) →
    ∀ b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ, (∀ x ∈ Z, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ Z, ∀ y ∈ Z, star (b x y) = b y x) →
    (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, b x (F i y) = b (F i x) y) →
    ∃ C : Finset (ι → ℂ), ∀ x ∈ Z, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h} := by
  intro E ι _ _ F Z hfd hmap hadd hsmul hcomm b hpos hsymm hadj
  let T : ι → Module.End ℂ Z := fun i =>
    { toFun := fun x => ⟨F i x, hmap i x x.2⟩
      map_add' := fun x y => Subtype.ext (hadd i x x.2 y y.2)
      map_smul' := fun a x => Subtype.ext (hsmul i a x x.2) }
  let core : InnerProductSpace.Core ℂ Z :=
    { inner := fun x y => b x y
      conj_inner_symm := fun x y => by
        show star (b (y : E) x) = b x y
        exact hsymm y y.2 x x.2
      re_inner_nonneg := fun x => by
        show 0 ≤ (b (x : E) x).re
        by_cases hx : (x : E) = 0
        · rw [hx]; simp
        · exact (hpos x x.2 hx).le
      add_left := fun x y z => by
        show b ((x : E) + y) z = b x z + b y z
        rw [map_add, LinearMap.add_apply]
      smul_left := fun x y r => by
        show b (r • (x : E)) y = starRingEnd ℂ r * b x y
        rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
      definite := fun x hx => by
        by_contra h0
        have h1 := hpos x x.2 (fun e => h0 (Subtype.ext e))
        have h2 : b (x : E) x = 0 := hx
        rw [h2] at h1
        simp at h1 }
  letI : NormedAddCommGroup Z := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (cd := core)
  letI : InnerProductSpace ℂ Z := InnerProductSpace.ofCore core.toCore
  have hT : ∀ i, (T i).IsSymmetric := fun i x y => (hadj i x x.2 y y.2).symm
  have hC : Pairwise (Function.onFun Commute T) := fun i j _ =>
    LinearMap.ext fun x => Subtype.ext (hcomm i j x x.2)
  have key := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC
  have htop : IsCompactElement (⊤ : Submodule ℂ Z) :=
    (Submodule.fg_iff_compact _).1 (Module.finite_def.1 hfd)
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ htop
    (fun χ : ι → ℂ => ⨅ i, Module.End.eigenspace (T i) (χ i)) key.ge
  have hle : (⊤ : Submodule ℂ Z) ≤
      (⨆ c ∈ s, Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h}).comap Z.subtype := by
    refine hs.trans (iSup₂_le fun c hc y hy => ?_)
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hy
    refine Submodule.mem_comap.2 ((le_iSup₂ (f := fun c (_ : c ∈ s) =>
      Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h}) c hc) (Submodule.subset_span ⟨y.2, fun i => ?_⟩))
    exact congrArg Subtype.val (hy i)
  exact ⟨s, fun x hx => hle (x := ⟨x, hx⟩) Submodule.mem_top⟩

end GlobalTheory.JointSpectral
