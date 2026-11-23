import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomEqOneOfNilpotent
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory

namespace TorusThicken

theorem pullback_map_eq_of_comp {S S' S'' : Scheme.{0}} (s : S'' ⟶ S') (p : S' ⟶ S) {V W : Over S}
    {a b : V ⟶ W} (h : (Over.pullback p).map a = (Over.pullback p).map b) :
    (Over.pullback (s ≫ p)).map a = (Over.pullback (s ≫ p)).map b := by
  have ha := (Over.pullbackComp s p).hom.naturality a
  have hb := (Over.pullbackComp s p).hom.naturality b
  simp only [Functor.comp_map] at ha hb
  rw [← cancel_mono ((Over.pullbackComp s p).hom.app W), ha, hb, h]

theorem pullback_pullback_map_eq_of_comp {S S' S'' : Scheme.{0}} (s : S'' ⟶ S') (p : S' ⟶ S)
    {V W : Over S} {a b : V ⟶ W} (h : (Over.pullback (s ≫ p)).map a = (Over.pullback (s ≫ p)).map b) :
    (Over.pullback s).map ((Over.pullback p).map a) = (Over.pullback s).map ((Over.pullback p).map b) := by
  have ha := (Over.pullbackComp s p).hom.naturality a
  have hb := (Over.pullbackComp s p).hom.naturality b
  simp only [Functor.comp_map] at ha hb
  rw [← cancel_epi ((Over.pullbackComp s p).hom.app V), ← ha, ← hb, h]

end TorusThicken

open TorusThicken in

theorem splitTorus_hom_trivial_mod_pow (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (A : Type) [AddCommGroup A] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (f : splitTorus (Spec (CommRingCat.of R)) A ⟶ G) (hf : IsMonHom f)
    (h : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map f =
      (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map 1) (n : ℕ) :
    (Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map 1 := by
  set I := IsLocalRing.maximalIdeal R ^ (n + 1) with hI
  set p := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) with hp
  have hIt : I ≠ ⊤ := fun e => (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.1 (e ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hIt
  have : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  set J : Ideal (R ⧸ I) := (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I) with hJ
  have hJn : IsNilpotent J := ⟨n + 1, by
    rw [hJ, ← Ideal.map_pow, ← hI, Ideal.map_quotient_self]; rfl⟩
  set q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) with hq
  let ℓ : IsLocalRing.ResidueField R →+* (R ⧸ I) ⧸ J :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) ((Ideal.Quotient.mk J).comp (Ideal.Quotient.mk I))
      (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ ha)
  have hsq : q ≫ p = Spec.map (CommRingCat.ofHom ℓ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) := by
    rw [hq, hp, ← Spec.map_comp, ← Spec.map_comp]; rfl

  have h1 : (Over.pullback q).map ((Over.pullback p).map f) =
      (Over.pullback q).map ((Over.pullback p).map 1) := by
    apply pullback_pullback_map_eq_of_comp
    rw [hsq]
    exact pullback_map_eq_of_comp _ _ h
  obtain ⟨e, he, -⟩ := splitTorus_baseChange _ _ p A
  have hg : IsMonHom (e.hom ≫ (Over.pullback p).map f) := inferInstance
  have hp1 : (Over.pullback p).map (1 : splitTorus (Spec (CommRingCat.of R)) A ⟶ G) = 1 :=
    Functor.map_one _
  have key := splitTorus_hom_eq_one_of_nilpotent (R ⧸ I) J hJn A _ (e.hom ≫ (Over.pullback p).map f) hg
    (by rw [Functor.map_comp, h1, hp1, ← Functor.map_comp, ← Hom.one_def, MonObj.comp_one])
  rw [← cancel_epi e.hom, key, ← Hom.one_def, hp1, MonObj.comp_one]

end GlobalTheory
