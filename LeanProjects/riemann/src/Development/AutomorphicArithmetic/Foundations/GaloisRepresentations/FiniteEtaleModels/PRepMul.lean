import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.repMul_holds :
    CrtMul → CrtProj → RepMul := by
  intro hM hP p _ D R _ b N S s o 𝔞 𝔟 hab h₁ h₂
  obtain ⟨Y₁, π₁, lu₁, hf₁, he₁, hl₁, hu₁⟩ := h₁
  obtain ⟨Y₂, π₂, lu₂, hf₂, he₂, hl₂, hu₂⟩ := h₂
  haveI := hf₁
  haveI := hf₂
  haveI := he₁
  haveI := he₂
  obtain ⟨ea, hea, eb, heb, hsum⟩ :=
    Submodule.mem_sup.1 (show (1 : 𝓞 D.F) ∈ 𝔞 ⊔ 𝔟 by rw [hab]; exact Submodule.mem_top)
  have kill : ∀ {𝔠 : Ideal (𝓞 D.F)} {T : Over S} {l : D.La → (T ⟶ o.A)}, IsEtLevOver o 𝔠 1 l →
      ∀ e ∈ 𝔠, ∀ y, l (algebraMap (𝓞 D.F) D.O e • y) = 1 := fun h e he y =>
    h.2.2.1 _ (Submodule.subset_span ⟨e, by simpa using he, y, rfl⟩)
  have dec : ∀ y : D.La, algebraMap (𝓞 D.F) D.O ea • y + algebraMap (𝓞 D.F) D.O eb • y = y := by
    intro y
    rw [← add_smul, ← map_add, hsum, map_one, one_smul]
  have r₁ : ∀ y, lu₁ (algebraMap (𝓞 D.F) D.O eb • y) = lu₁ y := by
    intro y
    conv_rhs => rw [← dec y, hl₁.1, kill hl₁ ea hea, _root_.one_mul]
  have r₂ : ∀ y, lu₂ (algebraMap (𝓞 D.F) D.O ea • y) = lu₂ y := by
    intro y
    conv_rhs => rw [← dec y, hl₂.1, kill hl₂ eb heb, _root_.mul_one]
  let π : pullback π₁ π₂ ⟶ S := pullback.fst π₁ π₂ ≫ π₁
  let f₁ : Over.mk π ⟶ Over.mk π₁ := Over.homMk (pullback.fst π₁ π₂) rfl
  let f₂ : Over.mk π ⟶ Over.mk π₂ := Over.homMk (pullback.snd π₁ π₂) pullback.condition.symm
  refine ⟨pullback π₁ π₂, π, fun y => (f₁ ≫ lu₁ y) * (f₂ ≫ lu₂ y), inferInstance, inferInstance, ?_, ?_⟩
  · exact hM p D R b N S s o 𝔞 𝔟 hab _ _ _ (GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 1 _ _ lu₁ f₁ hl₁)
      (GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔟 1 _ _ lu₂ f₂ hl₂)
  · intro T l hl
    have hA := hP p D R b N S s o 𝔞 𝔟 eb heb (by rw [← hsum, add_sub_cancel_right]; exact hea) T l hl
    have hB := hP p D R b N S s o 𝔟 𝔞 ea hea (by rw [← hsum, add_sub_cancel_left]; exact heb) T l
      (by rwa [_root_.mul_comm])
    obtain ⟨g₁, hg₁, hv₁⟩ := hu₁ T _ hA
    obtain ⟨g₂, hg₂, hv₂⟩ := hu₂ T _ hB
    have hg₁' : ∀ y, g₁ ≫ lu₁ y = l (algebraMap (𝓞 D.F) D.O eb • y) := hg₁
    have hg₂' : ∀ y, g₂ ≫ lu₂ y = l (algebraMap (𝓞 D.F) D.O ea • y) := hg₂
    have hw : g₁.left ≫ π₁ = g₂.left ≫ π₂ := (Over.w g₁).trans (Over.w g₂).symm
    let f : T ⟶ Over.mk π := Over.homMk (pullback.lift g₁.left g₂.left hw) (by
      show pullback.lift g₁.left g₂.left hw ≫ pullback.fst π₁ π₂ ≫ π₁ = T.hom
      rw [← Category.assoc, pullback.lift_fst]
      exact Over.w g₁)
    have c₁ : f ≫ f₁ = g₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ hw)
    have c₂ : f ≫ f₂ = g₂ := Over.OverMorphism.ext (pullback.lift_snd _ _ hw)
    refine ⟨f, ?_, ?_⟩
    · intro y
      show f ≫ ((f₁ ≫ lu₁ y) * (f₂ ≫ lu₂ y)) = l y
      rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, c₁, c₂, hg₁', hg₂', ← hl.1,
        add_comm, dec]
    · intro f' hf'
      have hf'' : ∀ y, f' ≫ ((f₁ ≫ lu₁ y) * (f₂ ≫ lu₂ y)) = l y := hf'
      have a₁ : f' ≫ f₁ = g₁ := hv₁ _ (fun y => by
        have := hf'' (algebraMap (𝓞 D.F) D.O eb • y)
        rw [kill hl₂ eb heb, r₁, MonObj.comp_mul, MonObj.comp_one, MonObj.comp_one, _root_.mul_one,
          ← Category.assoc] at this
        exact this)
      have a₂ : f' ≫ f₂ = g₂ := hv₂ _ (fun y => by
        have := hf'' (algebraMap (𝓞 D.F) D.O ea • y)
        rw [kill hl₁ ea hea, r₂, MonObj.comp_mul, MonObj.comp_one, MonObj.comp_one, _root_.one_mul,
          ← Category.assoc] at this
        exact this)
      refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
      · have := congrArg (fun u => u.left) (a₁.trans c₁.symm)
        simpa [f₁] using this
      · have := congrArg (fun u => u.left) (a₂.trans c₂.symm)
        simpa [f₂] using this
