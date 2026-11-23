import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.ResBasic

variable {C : Type*} [Category C] [Abelian C] {X : C} (I : InjectiveResolution X)

theorem aug_comm : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ≫
    (I.cochainComplexXIso 0 0 rfl).hom =
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 X).inv ≫ I.ι.f 0 := by
  rw [InjectiveResolution.ι'_f_zero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  erw [Category.id_comp]

end GlobalTheory.EtC.ResBasic

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
private theorem injectiveResolution_cochainComplex_exact_and_exactAt {C : Type*} [Category C] [Abelian C]
    {X : C} (I : InjectiveResolution X) :
    (∀ n : ℤ, Injective (I.cochainComplex.X n)) ∧
    (∀ n : ℤ, n < 0 → IsZero (I.cochainComplex.X n)) ∧
    Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ∧
    (∃ w : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ≫
        I.cochainComplex.d 0 1 = 0, (ShortComplex.mk _ _ w).Exact) ∧
    (∀ n : ℤ, n ≠ 0 → I.cochainComplex.ExactAt n) := by
  refine ⟨fun n => inferInstance, fun n hn => ?_, ?_, ?_, fun n hn => ?_⟩
  · exact HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
      have h : (ComplexShape.embeddingUpNat.f i : ℤ) = i := rfl
      omega)
  · rw [I.ι'_f_zero]
    erw [Iso.inv_hom_id_assoc]
    exact mono_comp (I.ι.f 0) _
  · have hw : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ I.ι'.f 0) ≫
        I.cochainComplex.d 0 1 = 0 := by
      rw [I.ι'_f_zero, I.cochainComplex_d 0 1 0 1 rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      erw [Category.assoc, Iso.inv_hom_id_assoc, I.ι_f_zero_comp_complex_d_assoc, zero_comp]
      rfl
    refine ⟨hw, ?_⟩
    refine (ShortComplex.exact_iff_of_iso ?_).mpr I.exact₀
    refine ShortComplex.isoMk (Iso.refl _) (I.cochainComplexXIso 0 0 rfl)
      (I.cochainComplexXIso 1 1 rfl) ?_ ?_
    · dsimp only
      rw [I.ι'_f_zero]
      erw [Category.id_comp, Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, Iso.inv_hom_id_assoc]
    · dsimp only
      rw [I.cochainComplex_d 0 1 0 1 rfl rfl]
      simp
  · exact (quasiIsoAt_iff_exactAt I.ι' n (HomologicalComplex.exactAt_single_obj _ _ _ _ hn)).mp
      inferInstance

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in

theorem _root_.GlobalTheory.EtC.res_basic : ∀ (R : Type) [CommRing R] (F : _root_.GlobalTheory.EtC.Shv R), (∀ n : ℤ, Injective ((_root_.GlobalTheory.EtC.res R F).X n)) ∧
    (∀ n : ℤ, n < 0 → IsZero ((_root_.GlobalTheory.EtC.res R F).X n)) ∧ Mono (_root_.GlobalTheory.EtC.resι R F) ∧
    (∃ w : _root_.GlobalTheory.EtC.resι R F ≫ (_root_.GlobalTheory.EtC.res R F).d 0 1 = 0, (ShortComplex.mk _ _ w).Exact) ∧
    (∀ n : ℤ, n ≠ 0 → (_root_.GlobalTheory.EtC.res R F).ExactAt n) ∧
    ∀ (E : _root_.GlobalTheory.EtC.Spc) (n : ℤ), 0 < n → IsZero (((_root_.GlobalTheory.EtC.chains R).obj E).X n) := by
  intro R _ F
  unfold _root_.GlobalTheory.EtC.res _root_.GlobalTheory.EtC.resι _root_.GlobalTheory.EtC.chains
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := injectiveResolution_cochainComplex_exact_and_exactAt (injectiveResolution F)
  refine ⟨h₁, h₂, h₃, h₄, h₅, fun E n hn => ?_⟩
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
    have h : (ComplexShape.embeddingDownNat.f i : ℤ) = -i := rfl
    omega)
