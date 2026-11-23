import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetIsProjOverDescends
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsDescendToLargeSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpObjDescendsToLargeSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescentSmoothDimension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFieldExtensionBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PolCountableDescent

theorem countable_closure {K : Type} [Field K] (s : Finset K) :
    Countable (Subfield.closure (s : Set K)) := by
  rw [← Cardinal.mk_le_aleph0_iff]
  refine (Subfield.cardinalMk_closure_le_max _).trans ?_
  exact max_le (Cardinal.mk_le_aleph0_iff.2 s.countable_toSet.to_subtype) le_rfl

theorem subset_closure_of_subset {K : Type} [Field K] {s s' : Finset K} (h : s ⊆ s') :
    (s : Set K) ⊆ Subfield.closure (s' : Set K) :=
  fun _ hx => Subfield.subset_closure (h hx)

theorem spMap_subtype_comp {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]; rfl

theorem polAV_descends_to_countable_subfield :
    ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (J I : Type) [Finite J] [Finite I] (a : J → (P.A ⟶ P.A)) (x : I → (𝟙_ (Over (Sp K)) ⟶ P.A)), ∃ (K₀ : Subfield K) (P₀ : PolAV (Sp K₀)) (Φ : P.A.left ⟶ P₀.A.left) (a₀ : J → (P₀.A ⟶ P₀.A)) (x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A)), Countable K₀ ∧ IsGrpPullback P.A P₀.A (spMap K₀.subtype) Φ ∧ LBIso P.L (P₀.L.pull Φ) ∧ (∀ j, (a j).left ≫ Φ = Φ ≫ (a₀ j).left) ∧ ∀ i, (x i).left ≫ Φ = spMap K₀.subtype ≫ (x₀ i).left := by
  intro K _ P J I _ _ a x
  classical
  obtain ⟨s₀, H₀⟩ := GlobalTheory.exists_finset_isProjOver_descends K ⊥ P.A.left P.A.hom
    (GlobalTheory.ProjSpace.isProjOver_of_relAmple P.ample)
  let K₀ : Subfield K := Subfield.closure (s₀ : Set K)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ K₀ bot_le Subfield.subset_closure
  have : IsProper p₀ := by
    obtain ⟨N, i, hi, rfl⟩ := hp₀
    have := isProper_str K₀ N
    infer_instance
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := GlobalTheory.grpObj_descends_to_large_subfield K K₀ (Over.mk p₀) P.A φ sq
  obtain ⟨s₂, H₂⟩ := GlobalTheory.LBDescent.exists_lb_subfield K K₀ X₀ P.A.left p₀ P.A.hom φ P.L P.isLB sq
  obtain ⟨s₃, H₃⟩ := GlobalTheory.morphisms_descend_to_large_subfield K K₀ X₀ P.A.left p₀ P.A.hom φ X₀ p₀ J
    (fun j => (a j).left ≫ φ) sq
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, Over.w])
  obtain ⟨s₄, H₄⟩ := GlobalTheory.morphisms_descend_to_large_subfield K K₀ (Sp K₀) (Sp K) (𝟙 _) (𝟙 _)
    (spMap K₀.subtype) X₀ p₀ I (fun i => (x i).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (fun i => by
      have e : (x i).left ≫ P.A.hom = 𝟙 _ := Over.w (x i)
      rw [Category.assoc, sq.w, ← Category.assoc, e]; simp)
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃ ∪ s₄
  let K₁ : Subfield K := Subfield.closure (s : Set K)
  have h : K₀ ≤ K₁ := Subfield.closure_mono (Finset.coe_subset.2 (fun y hy => by simp [s, hy]))
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp K₁) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : P.A.left ⟶ A₁.left := sq₁.lift φ (P.A.hom ≫ spMap K₁.subtype)
    (by rw [Category.assoc, spMap_subtype_comp h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = P.A.hom ≫ spMap K₁.subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hL⟩ := H₂ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨f₁, hf₁⟩ := H₃ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨x₁, hx₁⟩ := H₄ K₁ h (subset_closure_of_subset (fun y hy => by simp [s, hy])) (Sp K₁) (𝟙 _) inc
    (spMap K₁.subtype) (IsPullback.of_vert_isIso ⟨by simp [inc]⟩) (spMap_subtype_comp h) (by simp)
  let act₁ : J → (A₁ ⟶ A₁) := fun j =>
    Over.homMk (sq₁.lift (f₁ j) A₁.hom (by rw [(hf₁ j).2, sq₁.w])) (sq₁.lift_snd _ _ _)
  let pt₁ : I → (𝟙_ (Over (Sp K₁)) ⟶ A₁) := fun i =>
    Over.homMk (sq₁.lift (x₁ i) (𝟙 _) (by rw [(hx₁ i).2]; simp)) (sq₁.lift_snd _ _ _)
  obtain ⟨hab, hdim⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend K₁ K K₁.subtype A₁ P.A ψ hG P.isAb
  obtain ⟨hrig, hsym, hkt⟩ := GlobalTheory.PolDescent.rigidified_sym_kTriv_descend K₁ K K₁.subtype A₁ P.A ψ L₁ P.L
    hab hG hL₁ P.isLB hL
  have hamp := GlobalTheory.AmpleDescent.relAmple_of_fieldExtension K₁ K K₁.subtype A₁ P.A ψ L₁ P.L
    hab hG hL₁ P.isLB hL P.ample
  let P₁ : PolAV (Sp K₁) :=
    { A := A₁, grp := gr₁, isAb := hab, g := P.g, smoothDim := hdim P.g P.smoothDim, L := L₁,
      isLB := hL₁, rigid := hrig P.rigid, sym := hsym P.sym, ample := hamp, ktriv := hkt P.ktriv }
  refine ⟨K₁, P₁, ψ, act₁, pt₁, countable_closure s, hG, hL, fun j => ?_, fun i => ?_⟩
  · change (a j).left ≫ ψ = ψ ≫ (act₁ j).left
    have e₁ : (act₁ j).left ≫ φ₁ = f₁ j := sq₁.lift_fst _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, e₁, (hf₁ j).1]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hψ₂]
  · change (x i).left ≫ ψ = spMap K₁.subtype ≫ (pt₁ i).left
    have e : (x i).left ≫ P.A.hom = 𝟙 _ := Over.w (x i)
    have e₁ : (pt₁ i).left ≫ φ₁ = x₁ i := sq₁.lift_fst _ _ _
    have e₂ : (pt₁ i).left ≫ A₁.hom = 𝟙 _ := sq₁.lift_snd _ _ _
    apply sq₁.hom_ext
    · rw [Category.assoc, hψ₁]
      exact ((hx₁ i).1.symm.trans (congrArg _ e₁.symm)).trans (Category.assoc _ _ _).symm
    · rw [Category.assoc, hψ₂, ← Category.assoc, e]
      refine (Category.id_comp _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      exact ((congrArg _ e₂).trans (Category.comp_id _)).symm

end GlobalTheory.PolCountableDescent
end
