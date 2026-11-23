import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DropPlInsert
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPlacesThetaFunctionFixedVectorShapeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLocalGenerationInertPlaceOffLevelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLocalGenerationSplitPlaceOffLevelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGenerationThetaFunAtTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGenerationThetaFunctionsTwistPlaceStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section
namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem transl_mem_span_gen (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i))
    {φ : WO (Vc D i) (Wc D i) → ℂ} (hφ : φ ∈ Submodule.span ℂ (Gen R i t)) :
    R.ωP i t (1, g) φ ∈ Submodule.span ℂ (Gen R i t) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g', f', hf', rfl⟩ := hx
    refine Submodule.subset_span ⟨g * g', f', hf', ?_⟩
    have hm : ((1, g) : GA D (Vc D i) × GA D (Wc D i)) * (1, g') = (1, g * g') := by
      rw [Prod.mk_mul_mk, mul_one]
    rw [← hm, map_mul, Module.End.mul_apply]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem finLike_of_likeOff_empty (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {f : WO (Vc D i) (Wc D i) → ℂ}
    (hf : LikeOff R i t ∅ f) : FinLike R i t f :=
  ⟨hf.1, fun c hc h0 => hf.2 c (fun u hu => ⟨hc u hu, fun v hv => absurd hv (Finset.notMem_empty v)⟩) h0⟩

theorem mem_span_gen_of_step (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (hst : ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb →
      ∀ f, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → f ∈ Submodule.span ℂ (StepGen R i t (dropPl Sb v)))
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∀ f, TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → f ∈ Submodule.span ℂ (Gen R i t) := by
  classical
  induction Sb using Finset.induction_on with
  | empty =>
    intro f _ _ hL
    refine Submodule.subset_span ⟨1, f, finLike_of_likeOff_empty R i t hL, ?_⟩
    have h1 : ((1, 1) : GA D (Vc D i) × GA D (Wc D i)) = 1 := rfl
    rw [h1, map_one, Module.End.one_apply]
  | insert v s hv ih =>
    intro f hT hC hL
    have h := hst (insert v s) v (Finset.mem_insert_self v s) f hT hC hL
    rw [dropPl_insert hv] at h
    refine (Submodule.span_le.2 ?_) h
    rintro φ ⟨g, f', hT', hC', hL', rfl⟩
    exact transl_mem_span_gen R i t g (ih f' hT' hC' hL')

end GlobalTheory.DownLift.GenFinite

namespace GlobalTheory.DownLift.GenFinite

theorem gen_of_type_clean : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeVec R i t f → GlobalTheory.DownLift.GenFinite.Clean R i t f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.Gen R i t) := by
  intro hH D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t f hT hC
  obtain ⟨Sb, hL⟩ := GlobalTheory.T.exists_places_thetaFunction_fixedVectorShape D G Pl0 T A Ks R F hG hP i t f hT.1
  refine mem_span_gen_of_step R i t ?_ Sb f ⟨hT.1, fun κ hκ _ => hT.2 κ hκ⟩
    (fun PP a ha tr ε hε _ κ hκ _ => hC PP a ha tr ε hε κ hκ) hL
  intro Sb v hv f hT hC hL
  by_cases hpg : ∃ PP ∈ R.Pg, Over PP v
  · exact GlobalTheory.T.local_generation_thetaFun_at_type_prime D G Pl0 T A Ks R F hG hP i t Sb v hv hpg f hT hC hL
  by_cases hq : ∃ PP ∈ R.Q t, Over PP v
  · exact GlobalTheory.T.localGeneration_thetaFunctions_twistPlace D G Pl0 T A Ks R F hG hP i t Sb v hv (fun PP h ho => hpg ⟨PP, h, ho⟩) hq f hT hC hL
  have hoff : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ¬ Over PP v := by
    rintro PP (h | h) ho
    · exact hpg ⟨PP, h, ho⟩
    · exact hq ⟨PP, h, ho⟩
  by_cases hs : ∃ ε e, IsPlaceIdem D v ε ∧ IsSplitIdem D e ∧ e * algebraMap (AF D.host.F) (AE D) ε ≠ 0
  · exact GlobalTheory.T.thetaFunction_localGeneration_splitPlaceOffLevels D G Pl0 T A Ks R F hG hP i t Sb v hv hs hoff f hT hC hL
  · refine GlobalTheory.T.thetaFunction_local_generation_inertPlace_offLevel hH D G Pl0 T A Ks R F hG hP i t Sb v hv ?_ hoff f hT hC hL
    intro ε hε e he
    by_contra hne
    exact hs ⟨ε, e, hε, he, hne⟩

end GlobalTheory.DownLift.GenFinite
