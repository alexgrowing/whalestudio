import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsCechNerveQuasiIsoOfSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafMapMonoEpiIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsIsoOfFreeIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

lemma isIso_mapCechNerve_app_of_mono {A B C : PSh} (π : A ⟶ B) (ι : B ⟶ C) [Mono ι] (φ : A ⟶ C)
    (h : π ≫ ι = φ) (n : SimplexCategoryᵒᵖ) :
    IsIso ((Arrow.mapCechNerve
      (Arrow.homMk (𝟙 A) ι (by simp [h]) : Arrow.mk π ⟶ Arrow.mk φ)).app n) := by
  subst h
  have e : (Arrow.mapCechNerve
      (Arrow.homMk (𝟙 A) ι (by simp) : Arrow.mk π ⟶ Arrow.mk (π ≫ ι))).app n =
      WidePullback.lift (WidePullback.base (fun _ : Fin (n.unop.len + 1) => π) ≫ ι)
        (fun i => WidePullback.π (fun _ : Fin (n.unop.len + 1) => π) i)
        (fun j => by
          show _ ≫ (π ≫ ι) = _
          rw [← Category.assoc, WidePullback.π_arrow]) := by
    apply WidePullback.hom_ext
    · intro j
      erw [WidePullback.lift_π]
    · erw [WidePullback.lift_base]
  rw [e]
  refine ⟨WidePullback.lift (WidePullback.π _ 0 ≫ π) (fun i => WidePullback.π _ i) ?_, ?_, ?_⟩
  · intro i
    rw [← cancel_mono ι]
    simp only [Category.assoc]
    exact (WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π ≫ ι) i).trans
      (WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π ≫ ι) 0).symm
  · apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_π, WidePullback.lift_π]
      rfl
    · rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_base]
      rw [← Category.assoc]
      erw [WidePullback.lift_π]
      exact WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π) 0
  · apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_π, WidePullback.lift_π]
    · rw [Category.assoc, Category.id_comp]
      erw [WidePullback.lift_base]
      rw [← Category.assoc]
      erw [WidePullback.lift_base]
      rw [Category.assoc]
      exact WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => π ≫ ι) 0

end GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem quasiIso_chains_cech_of_locSurj (R : Type) [CommRing R] {P Q : PSh} (φ : P ⟶ Q)
    (hφ : ∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, φ.app (op V) x = Q.map g.op y) :
    QuasiIso ((chains R).map (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from
      (Arrow.mk φ).augmentedCechNerve.hom)) := by
  let aφ : (Arrow.mk φ).cechNerve ⟶ disc.obj Q := (Arrow.mk φ).augmentedCechNerve.hom
  change QuasiIso ((chains R).map aφ)
  have hπι : Subfunctor.toRange φ ≫ (Subfunctor.range φ).ι = φ := Subfunctor.toRange_ι φ
  set π := Subfunctor.toRange φ with hπ
  set ι := (Subfunctor.range φ).ι with hι
  let F : Arrow.mk π ⟶ Arrow.mk φ := Arrow.homMk (𝟙 P) ι (by simp [hπι])
  let aπ : (Arrow.mk π).cechNerve ⟶ disc.obj _ := (Arrow.mk π).augmentedCechNerve.hom
  have sq : Arrow.mapCechNerve F ≫ aφ = aπ ≫ disc.map ι := by
    ext n : 1
    erw [NatTrans.comp_app, NatTrans.comp_app]
    erw [Arrow.augmentedCechNerve_hom_app, Arrow.augmentedCechNerve_hom_app, WidePullback.lift_base]
    rfl
  have hsurj : ∀ U, Function.Surjective (π.app U) := fun U =>
    (epi_iff_surjective _).1 ((NatTrans.epi_iff_epi_app _).1 (inferInstance : Epi π) U)
  have h1 : QuasiIso ((chains R).map aπ) := GlobalTheory.T.quasiIso_chains_cechNerve_of_surjective R π hsurj
  have hιfree : IsIso ((free R).map ι) := by
    refine (GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R ι).2.2 ?_ ?_
    · intro U y
      exact GlobalTheory.EtC.loc_calculus.2.1 U _ _ (hφ U y) fun V g ⟨x, hx⟩ => ⟨π.app (op V) x, hx⟩
    · intro U x x' hxx
      have : x = x' := Subtype.ext hxx
      subst this
      exact GlobalTheory.EtC.loc_calculus.1 U _ fun _ _ => rfl
  have h2 : IsIso ((chains R).map (disc.map ι)) :=
    isIso_chains_map_of_isIso_free R _ fun n => hιfree
  have h3 : IsIso ((chains R).map (Arrow.mapCechNerve F)) :=
    isIso_chains_map_of_isIso_free R _ fun n => by
      have := isIso_mapCechNerve_app_of_mono π ι φ hπι n
      exact Functor.map_isIso _ _
  have key : (chains R).map (Arrow.mapCechNerve F) ≫ (chains R).map aφ =
      (chains R).map aπ ≫ (chains R).map (disc.map ι) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq]
  rw [← quasiIso_iff_comp_left ((chains R).map (Arrow.mapCechNerve F)), key]
  haveI := h1
  haveI := h2
  have h2' : QuasiIso ((chains R).map (disc.map ι)) := inferInstance
  exact quasiIso_comp ((chains R).map aπ) ((chains R).map (disc.map ι)) (hφ := h1) (hφ' := h2')

end GlobalTheory.EtC
