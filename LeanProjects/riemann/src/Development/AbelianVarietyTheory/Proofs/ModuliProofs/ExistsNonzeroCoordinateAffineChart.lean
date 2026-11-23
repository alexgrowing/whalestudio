import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocallyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinatesPullIsoNonzeroLocusStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.CoordChart

private theorem isIso_restrict_lemma {X Z Y : Scheme.{0}} (x : X ⟶ Z) [Mono x] (j : Y ⟶ X)
    [IsOpenImmersion (j ≫ x)] : IsIso (x ∣_ (j ≫ x).opensRange) := by
  set V := (j ≫ x).opensRange with hV
  let s : V.toScheme ⟶ X := (j ≫ x).isoOpensRange.inv ≫ j
  have hs : s ≫ x = V.ι := by
    rw [← cancel_epi (j ≫ x).isoOpensRange.hom]
    simp only [s, Category.assoc, Iso.hom_inv_id_assoc]
    exact (Scheme.Hom.isoOpensRange_hom_ι (j ≫ x)).symm
  have hr : Set.range s ⊆ Set.range (x ⁻¹ᵁ V).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show x (s y) ∈ V
    have e : x (s y) = V.ι y := by rw [← Scheme.Hom.comp_apply, hs]
    rw [e]
    have hm : V.ι y ∈ Set.range V.ι := ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι] at hm
    exact hm
  let s' := IsOpenImmersion.lift (x ⁻¹ᵁ V).ι s hr
  have h1 : s' ≫ (x ⁻¹ᵁ V).ι = s := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨s', ?_, ?_⟩⟩
  · rw [← cancel_mono ((x ⁻¹ᵁ V).ι ≫ x), Category.assoc, reassoc_of% h1, hs, morphismRestrict_ι,
      Category.id_comp]
  · rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, reassoc_of% h1, hs, Category.id_comp]

theorem isOpenImmersion_of_mono_of_local {X Z : Scheme.{0}} (x : X ⟶ Z) [Mono x]
    (h : ∀ p : X, ∃ (Y : Scheme.{0}) (j : Y ⟶ X), IsOpenImmersion (j ≫ x) ∧
      x p ∈ Set.range (j ≫ x)) : IsOpenImmersion x := by
  choose Y j hj hp using h
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsOpenImmersion)
    (fun p => (j p ≫ x).opensRange) ?_ (fun p => ?_)
  · rintro _ ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨p, by rw [Scheme.Hom.mem_opensRange]; exact hp p⟩
  · have := isIso_restrict_lemma x (j p)
    infer_instance

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have e := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using e

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (y : Sp B ⟶ Sp A) :
    ∃ f : A →+* B, y = spMap f := by
  refine ⟨(Spec.preimage y).hom, ?_⟩
  simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem mono_of_ring_points {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z)
    (h : ∀ (B : Type) [CommRing B] (f g : A →+* B), spMap f ≫ x = spMap g ≫ x → f = g) : Mono x := by
  refine ⟨fun {W} a b hab => ?_⟩
  have key : ∀ (B : Type) [CommRing B] (t : Sp B ⟶ W), t ≫ a = t ≫ b := by
    intro B _ t
    obtain ⟨f, hf⟩ := exists_spMap (t ≫ a)
    obtain ⟨g, hg⟩ := exists_spMap (t ≫ b)
    have hfg : f = g := h _ f g (by rw [← hf, ← hg, Category.assoc, Category.assoc, hab])
    rw [hf, hg, hfg]
  exact W.affineOpenCover.openCover.hom_ext a b
    (fun k => key (W.affineOpenCover.X k) (W.affineOpenCover.openCover.f k))

theorem exists_chart : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) (i : σ), ProjRep I s M th → ∃ x : Sp (MvPolynomial σ R ⧸ (I ⊔ Ideal.span {MvPolynomial.X i - 1})) ⟶ Z, IsOpenImmersion x ∧ Set.range x = (Out.nonzeroLocus (th i) : Set Z) ∧ x ≫ s = spMap ((Ideal.Quotient.mk _).comp MvPolynomial.C) ∧ SecCoord M th x (fun a => Ideal.Quotient.mk _ (MvPolynomial.X a)) := by
  intro R σ _ I Z s M th i hP
  obtain ⟨hM, hpts, hrep⟩ := hP
  set J := I ⊔ Ideal.span {MvPolynomial.X i - 1} with hJ
  set q := Ideal.Quotient.mk J with hq

  have hq1 : q (MvPolynomial.X i) = 1 := by
    rw [← sub_eq_zero, ← map_one q, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)

  have hev : ∀ F, MvPolynomial.eval₂ (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a)) F = q F := by
    intro F
    have e : MvPolynomial.eval₂Hom (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a)) = q :=
      MvPolynomial.ringHom_ext (fun r => by simp) (fun a => by simp)
    exact RingHom.congr_fun e F
  obtain ⟨x, ⟨hxs, hxc⟩, -⟩ := hrep _ (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a))
    (by rw [Ideal.eq_top_iff_one, ← hq1]; exact Ideal.subset_span ⟨i, rfl⟩)
    (fun F hF => by rw [hev, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_sup_left hF)

  have hmono : Mono x := by
    apply mono_of_ring_points
    intro B _ f g hfg
    have hcf := GlobalTheory.ZM.Coord.baseChange hxc f
    have hcg := GlobalTheory.ZM.Coord.baseChange hxc g
    rw [hfg] at hcf
    obtain ⟨u, hu⟩ := GlobalTheory.ZM.Coord.unique hM hcg hcf
    have hu1 : (u : B) = 1 := by
      have e := hu i
      simp only [hq1, map_one] at e
      simpa using e.symm
    have hv : ∀ a, f (q (MvPolynomial.X a)) = g (q (MvPolynomial.X a)) := fun a => by
      rw [hu a, hu1, _root_.one_mul]
    have hb : f.comp (q.comp MvPolynomial.C) = g.comp (q.comp MvPolynomial.C) := by
      apply spMap_inj
      rw [← spMap_comp (q.comp MvPolynomial.C) f, ← spMap_comp (q.comp MvPolynomial.C) g, ← hxs,
        reassoc_of% hfg]
    have hc : f.comp q = g.comp q :=
      MvPolynomial.ringHom_ext (fun r => by simpa using RingHom.congr_fun hb r) (fun a => by simpa using hv a)
    exact Ideal.Quotient.ringHom_ext hc

  have hsub : Set.range x ⊆ (Out.nonzeroLocus (th i) : Set Z) := by
    rintro _ ⟨p, rfl⟩
    refine (GlobalTheory.ZM.CoordMove.mem_nonzeroLocus_iff hM i p hxc).2 ?_
    show q (MvPolynomial.X i) ∉ p.asIdeal
    rw [hq1]
    exact fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

  have hloc : ∀ z ∈ (Out.nonzeroLocus (th i) : Set Z), ∃ (B : Type) (_ : CommRing B)
      (ψ : (MvPolynomial σ R ⧸ J) →+* B), IsOpenImmersion (spMap ψ ≫ x) ∧ z ∈ Set.range (spMap ψ ≫ x) := by
    intro z hz
    obtain ⟨R', _, x', v', hx'o, ⟨p, rfl⟩, hx'c⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally Z M σ th hM).2.2 z
    have hp : v' i ∉ p.asIdeal := (GlobalTheory.ZM.CoordMove.mem_nonzeroLocus_iff hM i p hx'c).1 hz
    have hunit : IsUnit (algebraMap R' (Localization.Away (v' i)) (v' i)) :=
      IsLocalization.Away.algebraMap_isUnit (v' i)
    have hc1 := GlobalTheory.ZM.Coord.scale (GlobalTheory.ZM.Coord.baseChange hx'c (algebraMap R' (Localization.Away (v' i))))
      hunit.unit⁻¹
    set w : σ → Localization.Away (v' i) :=
      fun a => ((hunit.unit⁻¹ : (Localization.Away (v' i))ˣ) : Localization.Away (v' i)) *
        algebraMap R' (Localization.Away (v' i)) (v' a) with hw
    have hwi : w i = 1 := by simp [w]
    obtain ⟨β', hβ'⟩ := exists_spMap ((spMap (algebraMap R' (Localization.Away (v' i))) ≫ x') ≫ s)
    obtain ⟨hspan, hI⟩ := hpts _ β' _ w hβ' hc1
    have hker : J ≤ RingHom.ker (MvPolynomial.eval₂Hom β' w) := by
      refine sup_le (fun F hF => hI F hF) (Ideal.span_le.2 ?_)
      rintro _ rfl
      simp [hwi]
    let ψ : (MvPolynomial σ R ⧸ J) →+* Localization.Away (v' i) :=
      Ideal.Quotient.lift J (MvPolynomial.eval₂Hom β' w) (fun F hF => hker hF)
    have hψC : ∀ r, ψ (q (MvPolynomial.C r)) = β' r := fun r =>
      (Ideal.Quotient.lift_mk J _ _).trans (by simp)
    have hψX : ∀ a, ψ (q (MvPolynomial.X a)) = w a := fun a =>
      (Ideal.Quotient.lift_mk J _ _).trans (by simp)
    obtain ⟨y, -, hyu⟩ := hrep _ β' w hspan hI
    have e2 : spMap (algebraMap R' (Localization.Away (v' i))) ≫ x' = y := hyu _ ⟨hβ', hc1⟩
    have e1 : spMap ψ ≫ x = y := by
      refine hyu _ ⟨?_, ?_⟩
      · rw [Category.assoc, hxs, spMap_comp]
        congr 1
        exact RingHom.ext hψC
      · have e := GlobalTheory.ZM.Coord.baseChange hxc ψ
        convert e using 2 with a
        exact (hψX a).symm
    have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away (v' i)) (v' i)
    have hpm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R' (Localization.Away (v' i)))) := by
      rw [hrange]
      exact hp
    obtain ⟨p', hp'⟩ := hpm
    refine ⟨Localization.Away (v' i), inferInstance, ψ, ?_, p', ?_⟩
    · rw [e1, ← e2]
      infer_instance
    · rw [e1, ← e2]
      show x' (PrimeSpectrum.comap (algebraMap R' (Localization.Away (v' i))) p') = x' p
      rw [hp']
  have := hmono
  refine ⟨x, ?_, ?_, hxs, hxc⟩
  · apply isOpenImmersion_of_mono_of_local x
    intro p
    obtain ⟨B, _, ψ, h1, h2⟩ := hloc (x p) (hsub ⟨p, rfl⟩)
    exact ⟨Sp B, spMap ψ, h1, h2⟩
  · refine Set.Subset.antisymm hsub (fun z hz => ?_)
    obtain ⟨B, _, ψ, -, ⟨b, hb⟩⟩ := hloc z hz
    exact ⟨(spMap ψ) b, hb⟩

end GlobalTheory.ZM.CoordChart
