import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitesimalPointTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatTorsionSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSubgroupUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleTorsionSubgroupUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelKernelUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenCondInjectiveGeomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenCondOntoStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem exists_etLevScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Scheme.{0}) (π : Y ⟶ S) (lu : D.La → (Over.mk π ⟶ o.A)), IsFinite π ∧ Etale π ∧ IsEtLevOver o w0 r lu ∧ ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), IsEtLevOver o w0 r l → ∃! f : T ⟶ Over.mk π, ∀ y, f ≫ lu y = l y := by
  intro p _ D R _ b N w0 r _hNp hw S _ s o
  obtain ⟨r', hrr', H, i, hHf, hHfl, hHk, hHu⟩ := GlobalTheory.T.finite_flat_torsion_subgroup p D R b N w0 hw.1 hw.2.1 S s o r
  have hHe : Etale H.hom := GlobalTheory.T.torsion_subgroup_universal p D R b N w0 r' S s o H i hHf hHfl hHk hHu
    (fun k _ _ x v h0 hv => GlobalTheory.T.infinitesimal_point_trivial p D R b N w0 r' hw S s o k x v h0 hv)
  obtain ⟨K, κ, hKf, hKe, hKk, hKu⟩ := GlobalTheory.T.etale_torsion_subgroup_universal p D R b N w0 r r' hrr' S s o H i hHf hHe hHk hHu
  obtain ⟨Z, et, hZf, hZe, eadd, elin, eker, huniv⟩ := GlobalTheory.T.etale_level_kernel_universal p D R b N w0 r hw S s o K κ hKf hKe hKk hKu
  have c1 := GlobalTheory.T.clopenCond_injective_geom_alt p D R b N w0 r hw S s o K κ hKf hKe hKk hKu Z et hZf hZe eadd elin eker
  have c2 := GlobalTheory.T.clopenCond_onto_alt p D R b N w0 r hw S s o K κ hKf hKe hKk hKu Z et hZf hZe eadd elin eker
  obtain ⟨U, hU, HU⟩ := c1.and c2
  haveI := hZf
  haveI := hZe
  obtain ⟨V, j, hV1, hV2, hmono, Hj⟩ := GlobalTheory.LevCover.exists_sub U hU
  have hPV := (HU V j).2 ((Hj V j).2 ⟨𝟙 V, Category.id_comp j⟩)
  refine ⟨V.left, V.hom, fun y => j ≫ et y, hV1, hV2, ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_,
    fun k _ _ x => ⟨hPV.1 k x, hPV.2 k x⟩⟩, fun T l hl => ?_⟩
  · beta_reduce
    rw [eadd, MonObj.comp_mul]
  · beta_reduce
    rw [elin, Category.assoc]
  · beta_reduce
    rw [eker x hx, MonObj.comp_one]
  obtain ⟨hadd, hlin, hker, hgeo⟩ := hl
  obtain ⟨h, hh, hu⟩ := huniv T l hadd hlin hker
  have hP : (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
      ∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ h ≫ et y = 1 → y ∈ wSub D w0 r) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
        ∀ g : Over.mk (x ≫ T.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
          ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ h ≫ et y = g) := by
    refine ⟨fun k _ _ x y hy => (hgeo k x).1 y (by rw [← hh y]; exact hy), fun k _ _ x g hg => ?_⟩
    obtain ⟨y, hy⟩ := (hgeo k x).2 g hg
    exact ⟨y, by rw [hh y]; exact hy⟩
  obtain ⟨h', hh'⟩ := (Hj T h).1 ((HU T h).1 hP)
  refine ⟨h', fun y => ?_, fun g hg => ?_⟩
  · beta_reduce
    rw [← Category.assoc, hh', hh]
  · have : g ≫ j = h := hu _ fun y => by rw [Category.assoc]; exact hg y
    exact (cancel_mono j).1 (this.trans hh'.symm)

end GlobalTheory.UPel.HT.EtLev
