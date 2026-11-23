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

namespace GlobalTheory

theorem mem_iSup_jointEigen_inf_of_stable : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (G P : Submodule ℂ E) (C : Finset (ι → ℂ)),
    (∀ i, ∀ x ∈ G, F i x ∈ G) → (∀ i, ∀ x ∈ G, ∀ y ∈ G, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ G, F i (a • x) = a • F i x) → P ≤ G → (∀ i, ∀ x ∈ P, F i x ∈ P) →
    (∀ x ∈ G, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ G ∧ ∀ i, F i h = c i • h}) →
    ∀ x ∈ P, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} := by
  intro E ι _ _ F G P C hFG hadd hsmul hPG hFP hdec
  have hF0 : ∀ i, F i 0 = 0 := by
    intro i
    have := hsmul i 0 0 G.zero_mem
    simpa using this
  obtain ⟨V, hV⟩ : ∃ V : (ι → ℂ) → Submodule ℂ E,
      ∀ c x, x ∈ V c ↔ (x ∈ G ∧ ∀ i, F i x = c i • x) :=
    ⟨fun c =>
      { carrier := {h | h ∈ G ∧ ∀ i, F i h = c i • h}
        add_mem' := by
          rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
          refine ⟨G.add_mem hx hy, fun i => ?_⟩
          rw [hadd i x hx y hy, hx' i, hy' i, smul_add]
        zero_mem' := ⟨G.zero_mem, fun i => by rw [hF0 i, smul_zero]⟩
        smul_mem' := by
          rintro a x ⟨hx, hx'⟩
          refine ⟨G.smul_mem a hx, fun i => ?_⟩
          rw [hsmul i a x hx, hx' i]
          exact smul_comm _ _ _ }, fun c x => Iff.rfl⟩
  have hVG : ∀ c, V c ≤ G := fun c x hx => ((hV c x).1 hx).1
  have hSG : ∀ s : Finset (ι → ℂ), (⨆ c ∈ s, V c) ≤ G := fun s => iSup₂_le fun c _ => hVG c
  have hmemS : ∀ (s : Finset (ι → ℂ)) c, c ∈ s → V c ≤ ⨆ c ∈ s, V c := fun s c hc =>
    le_iSup₂_of_le (f := fun c (_ : c ∈ s) => V c) c hc le_rfl
  have hT : ∀ (i : ι) (b : ℂ) (s : Finset (ι → ℂ)), ∀ z ∈ ⨆ c ∈ s, V c,
      F i z - b • z ∈ ⨆ c ∈ s, V c := by
    intro i b s
    obtain ⟨M, hM⟩ : ∃ M : Submodule ℂ E,
        ∀ v, v ∈ M ↔ (v ∈ G ∧ F i v - b • v ∈ ⨆ c ∈ s, V c) :=
      ⟨{ carrier := {v | v ∈ G ∧ F i v - b • v ∈ ⨆ c ∈ s, V c}
         add_mem' := by
           rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
           refine ⟨G.add_mem hx hy, ?_⟩
           have : F i (x + y) - b • (x + y) = (F i x - b • x) + (F i y - b • y) := by
             rw [hadd i x hx y hy, smul_add]; abel
           rw [this]; exact Submodule.add_mem _ hx' hy'
         zero_mem' := ⟨G.zero_mem, by simp [hF0 i]⟩
         smul_mem' := by
           rintro a x ⟨hx, hx'⟩
           refine ⟨G.smul_mem a hx, ?_⟩
           have : F i (a • x) - b • (a • x) = a • (F i x - b • x) := by
             rw [hsmul i a x hx, smul_sub, smul_comm b a x]
           rw [this]; exact Submodule.smul_mem _ a hx' }, fun v => Iff.rfl⟩
    have hle : (⨆ c ∈ s, V c) ≤ M := iSup₂_le fun c hc v hv => by
      rw [hM]
      obtain ⟨hvG, hv'⟩ := (hV c v).1 hv
      refine ⟨hvG, ?_⟩
      rw [hv' i, ← sub_smul]
      exact hmemS s c hc ((V c).smul_mem _ hv)
    intro z hz
    exact ((hM z).1 (hle hz)).2
  have hB : ∀ (a : ι → ℂ) (s : Finset (ι → ℂ)), a ∉ s → ∀ y ∈ V a, ∀ z ∈ ⨆ c ∈ s, V c,
      y + z ∈ P → y ∈ P := by
    intro a s
    induction s using Finset.induction_on with
    | empty =>
      intro _ y _ z hz hyz
      simp at hz
      rw [hz, add_zero] at hyz; exact hyz
    | insert b t hbt ih =>
      intro ha y hy z hz hyz
      rw [Finset.mem_insert, not_or] at ha
      obtain ⟨hab, hat⟩ := ha
      rw [Finset.iSup_insert, Submodule.mem_sup] at hz
      obtain ⟨zb, hzb, zt, hzt, rfl⟩ := hz
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hab
      obtain ⟨hyG, hy'⟩ := (hV a y).1 hy
      obtain ⟨hzbG, hzb'⟩ := (hV b zb).1 hzb
      have hztG := hSG t hzt
      have hP1 : F i (y + (zb + zt)) - b i • (y + (zb + zt)) ∈ P :=
        P.sub_mem (hFP i _ hyz) (P.smul_mem _ hyz)
      have heq : F i (y + (zb + zt)) - b i • (y + (zb + zt))
          = (a i - b i) • y + (F i zt - b i • zt) := by
        rw [hadd i y hyG _ (G.add_mem hzbG hztG), hadd i zb hzbG zt hztG, hy' i, hzb' i]
        simp only [smul_add, sub_smul]; abel
      rw [heq] at hP1
      have hy2 : (a i - b i) • y ∈ V a := (V a).smul_mem _ hy
      have h3 := ih hat _ hy2 _ (hT i (b i) t zt hzt) hP1
      have hne : a i - b i ≠ 0 := sub_ne_zero.2 hi
      have h4 := P.smul_mem (a i - b i)⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4
  have hspan : ∀ c, Submodule.span ℂ {h | h ∈ G ∧ ∀ i, F i h = c i • h} = V c := fun c =>
    le_antisymm (Submodule.span_le.2 fun x hx => (hV c x).2 hx)
      fun x hx => Submodule.subset_span ((hV c x).1 hx)
  have hmain : ∀ s : Finset (ι → ℂ), ∀ x ∈ P, x ∈ ⨆ c ∈ s, V c →
      x ∈ ⨆ c ∈ s, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ hx; simpa using hx
    | insert a s has ih =>
      intro x hxP hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      have hyP : y ∈ P := hB a s has y hy z hz hxP
      have hzP : z ∈ P := by
        have := P.sub_mem hxP hyP; simpa using this
      rw [Finset.iSup_insert]
      exact Submodule.mem_sup.2 ⟨y, Submodule.subset_span ⟨hyP, ((hV a y).1 hy).2⟩, z, ih z hzP hz, rfl⟩
  intro x hx
  have h := hdec x (hPG hx)
  simp only [hspan] at h
  exact hmain C x hx h

end GlobalTheory
