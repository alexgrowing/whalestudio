import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GlueSchemesOverOpensAlongCocycle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSemiAbelianTripleGlueCommonGenericPart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleGlueTwoOpenImmersions
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfBaseEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.GlueModel

theorem range_comp_iso_hom {W X Y : Scheme.{0}} (f : W ⟶ X) (e : X ≅ Y) :
    Set.range (f ≫ e.hom) = e.inv ⁻¹' Set.range f := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨w, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, e.hom_inv_id, Category.comp_id]
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [Scheme.Hom.comp_apply, hw, ← Scheme.Hom.comp_apply, e.inv_hom_id]
    rfl

theorem range_iso_hom_comp {X Y Z : Scheme.{0}} (e : X ≅ Y) (g : Y ⟶ Z) :
    Set.range (e.hom ≫ g) = Set.range g := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.hom x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e.inv y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Category.assoc, e.inv_hom_id, Category.id_comp]

theorem exists_gmod_charts : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} {I : Type} [Finite I] {R : I → Type} [∀ i, CommRing (R i)] {a : I → 𝓞 c.F} {b : ∀ i, 𝓞 c.F →+* R i}
    {ω : ∀ i, R i →+* c.F} (C : ∀ i, Model Xo c (ω i)) (A : Scheme.{0}) (F : A ⟶ Sp (𝓞 c.F)) (ψ : ∀ i, (C i).X ⟶ A)
    (t : SAB H A) (n : ∀ i, SABMap (C i).t t (ψ i)) (i₀ : I), IsCover (algebraMap (𝓞 c.F) c.F) R a b ω →
    (∀ i, IsPullback (ψ i) (C i).s F (spMap (b i))) → (∀ i k, (C i).j ≫ ψ i = (C k).j ≫ ψ k) →
    Geo.Tor.IsNormalScheme A → IsProjOver F → Flat F →
    ∃ (Z : GMod Xo c) (u : ∀ i, (C i).X ⟶ Z.X), ∀ i, IsChartOf Z (C i) (a i) (b i) (u i) := by
  intro E _ _ _ H D l Xo c I _ R _ a b ω C A F ψ t n i₀ hcov hψ hj hN hPr hFl
  obtain ⟨-, hω, -⟩ := hcov
  have e₀ : spMap (algebraMap (𝓞 c.F) c.F) = spMap (ω i₀) ≫ spMap (b i₀) := by
    rw [← spMap_comp, (hω i₀).2.1]
  have hP₀ : IsPullback (pullback.fst (C i₀).s (spMap (ω i₀)) ≫ ψ i₀) (pullback.snd (C i₀).s (spMap (ω i₀))) F
      (spMap (algebraMap (𝓞 c.F) c.F)) := by
    rw [e₀]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (hψ i₀)
  haveI := (C i₀).jQ_open
  have hfst : ((C i₀).jQ ≫ hP₀.isoPullback.hom) ≫ pullback.fst F (spMap (algebraMap (𝓞 c.F) c.F)) =
      (C i₀).j ≫ ψ i₀ := by
    rw [Category.assoc, hP₀.isoPullback_hom_fst, Model.j, Category.assoc]
  obtain ⟨m₁, -⟩ := ObjMaps.exists_sab_comp (n i₀) (C i₀).m
  obtain ⟨m, -⟩ := exists_sabMap_of_base_eq m₁ hfst.symm
  have hco : ⇑((C i₀).jQ ≫ hP₀.isoPullback.hom) = ⇑hP₀.isoPullback.hom ∘ ⇑(C i₀).jQ :=
    funext fun x => Scheme.Hom.comp_apply _ _ x
  let Z : GMod Xo c :=
    { X := A, s := F, normal := hN, proj := hPr, flat := hFl
      jQ := (C i₀).jQ ≫ hP₀.isoPullback.hom
      jQ_over := by rw [Category.assoc, hP₀.isoPullback_hom_snd, (C i₀).jQ_over]
      jQ_open := inferInstance
      jQ_dense := by
        show DenseRange _
        rw [hco]
        exact DenseRange.comp (Scheme.Hom.surjective _).denseRange (C i₀).jQ_dense hP₀.isoPullback.hom.continuous
      t := t, oF := (C i₀).oF, m0 := (C i₀).m0, m := m
      ab_gen := by
        ext x
        rw [range_comp_iso_hom, Set.mem_preimage, Set.mem_preimage, ← (C i₀).ab_gen, Set.mem_preimage,
          ← abLocus_pullback abLocusOne t.semi (n i₀).cart.1]
        have h := congrArg (fun g => g x) hP₀.isoPullback_inv_fst
        simp only [Scheme.Hom.comp_apply] at h
        rw [← h] }
  refine ⟨Z, ψ, fun i => ?_⟩
  letI := (b i).toAlgebra
  haveI : IsLocalization.Away (a i) (R i) := (hω i).2.2
  have hb : IsOpenImmersion (spMap (b i)) := IsOpenImmersion.of_isLocalization (a i)
  haveI : IsOpenImmersion (ψ i) := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hψ i).flip hb
  refine ⟨inferInstance, (hψ i).w, ?_, ?_, ⟨n i⟩⟩
  · have h1 : Set.range (ψ i) = Set.range (pullback.fst F (spMap (b i))) := by
      rw [← (hψ i).isoPullback_hom_fst, range_iso_hom_comp]
    show Set.range (ψ i) = F ⁻¹' _
    rw [h1, Scheme.Pullback.range_fst]
    congr 1
    exact PrimeSpectrum.localization_away_comap_range (R i) (a i)
  · show (C i).j ≫ ψ i = ((C i₀).jQ ≫ hP₀.isoPullback.hom) ≫ pullback.fst _ _
    rw [hfst, hj]

end GlobalTheory.GlueModel
