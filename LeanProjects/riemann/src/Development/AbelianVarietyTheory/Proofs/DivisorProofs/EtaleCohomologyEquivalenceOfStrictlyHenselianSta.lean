import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitarySheafContinuousBaseChangeLevelwiseQcqsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianEtaleStalkOverPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyStalkLocalClassesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyBaseChangeCoprodBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LocGlob

variable {S : Scheme.{0}} {ι : Type} (V : ι → Over S)

def cop : Over S := Over.mk (Sigma.desc fun i => (V i).hom)

def cι (i : ι) : V i ⟶ cop V := Over.homMk (Sigma.ι (fun i => (V i).left) i) (by simp [cop])

def cdesc {U : Over S} (h : ∀ i, V i ⟶ U) : cop V ⟶ U :=
  Over.homMk (Sigma.desc fun i => (h i).left) (by
    apply Sigma.hom_ext
    intro i
    simp [cop])

theorem cι_cdesc {U : Over S} (h : ∀ i, V i ⟶ U) (i : ι) : cι V i ≫ cdesc V h = h i := by
  ext1
  change Sigma.ι (fun i => (V i).left) i ≫ Sigma.desc (fun i => (h i).left) = (h i).left
  exact Sigma.ι_desc _ _

def cop_isColimit : IsColimit (Cofan.mk (cop V).left (fun i => (cι V i).left)) :=
  coproductIsCoproduct _

theorem cop_etale (hV : ∀ i, Etale (V i).hom) : Etale (cop V).hom := by
  have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hV

end GlobalTheory.EtC.LocGlob

open GlobalTheory.EtC.LocGlob in
theorem GlobalTheory.EtC.loc_glob_classes : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → ∀ (U : Over S), Etale U.hom → ∀ n : ℤ, (∀ x : H R ((bc (α ≫ p)).obj U) F n, ∃ (V : Over S) (h : V ⟶ U) (y : H R ((bc p).obj V) F n), Etale V.hom ∧ Surjective h.left ∧ pull R ((bcMap α p).app V) F n y = pull R ((bc (α ≫ p)).map h) F n x) ∧ ∀ y : H R ((bc p).obj U) F n, pull R ((bcMap α p).app U) F n y = 0 → ∃ (V : Over S) (h : V ⟶ U), Etale V.hom ∧ Surjective h.left ∧ pull R ((bc p).map h) F n y = 0 := by
  intro R _ F S E E' α p hF hq1 hq2 hEqv U hU n
  have cont1 := GlobalTheory.T.finitarySheaf_continuous_baseChange_levelwiseQcqs R F hF S E (α ≫ p) hq1
  have cont2 := GlobalTheory.T.finitarySheaf_continuous_baseChange_levelwiseQcqs R F hF S E' p hq2
  choose O instO s g hs v hv using GlobalTheory.T.exists_strictlyHenselianEtaleStalk_over_point S U hU
  have loc := fun u => @GlobalTheory.T.etaleSpaceCohomology_stalk_local_classes R _ F S _ _ (bcMap α p) cont1 cont2 (O u) (instO u) (s u) (hs u)
    (@hEqv (O u) (instO u) (s u) (hs u)) U hU (g u) n
  have surjOf : ∀ (V : U.left → Over S) (g' : ∀ u, Over.mk (s u) ⟶ V u) (h : ∀ u, V u ⟶ U),
      (∀ u, g' u ≫ h u = g u) → Surjective (cdesc V h).left := by
    intro V g' h hg
    refine ⟨fun u0 => ⟨((g' u0 ≫ cι V u0).left) (v u0), ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Category.assoc, cι_cdesc, hg, hv]
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · choose V g' h y hV hg hy using fun u => (loc u).1 x
    obtain ⟨Y, hY⟩ := (GlobalTheory.T.etaleSpaceCohomology_baseChange_coprod_bijective R F S E' p (cop V) U.left V (cι V) (cop_isColimit V) n).2 y
    refine ⟨cop V, cdesc V h, Y, cop_etale V hV, surjOf V g' h hg, ?_⟩
    apply (GlobalTheory.T.etaleSpaceCohomology_baseChange_coprod_bijective R F S E (α ≫ p) (cop V) U.left V (cι V) (cop_isColimit V) n).1
    funext u
    simp only
    have hYu : pull R ((bc p).map (cι V u)) F n Y = y u := congrFun hY u
    rw [← pull_comp, ← pull_comp, (bcMap α p).naturality, ← Functor.map_comp, cι_cdesc, pull_comp,
      hYu, hy u]
  · choose V g' h hV hg hy0 using fun u => (loc u).2 y hy
    refine ⟨cop V, cdesc V h, cop_etale V hV, surjOf V g' h hg, ?_⟩
    apply (GlobalTheory.T.etaleSpaceCohomology_baseChange_coprod_bijective R F S E' p (cop V) U.left V (cι V) (cop_isColimit V) n).1
    funext u
    simp only [map_zero]
    rw [← pull_comp, ← Functor.map_comp, cι_cdesc, hy0 u]

example : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → ∀ (U : Over S), Etale U.hom → ∀ n : ℤ, (∀ x : H R ((bc (α ≫ p)).obj U) F n, ∃ (V : Over S) (h : V ⟶ U) (y : H R ((bc p).obj V) F n), Etale V.hom ∧ Surjective h.left ∧ pull R ((bcMap α p).app V) F n y = pull R ((bc (α ≫ p)).map h) F n x) ∧ ∀ y : H R ((bc p).obj U) F n, pull R ((bcMap α p).app U) F n y = 0 → ∃ (V : Over S) (h : V ⟶ U), Etale V.hom ∧ Surjective h.left ∧ pull R ((bc p).map h) F n y = 0 := GlobalTheory.EtC.loc_glob_classes

end
