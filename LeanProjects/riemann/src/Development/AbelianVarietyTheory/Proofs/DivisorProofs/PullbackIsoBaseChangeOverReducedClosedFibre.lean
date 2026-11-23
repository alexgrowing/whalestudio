import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFactorResidueFieldOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfIsIsoOnGeometricFibresOfSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftImmersionOfReducedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointRangeEqFixedGroupImageStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem spMap_residue_apply_eq_closedPoint (R : Type) [CommRing R] [IsLocalRing R] (w : Sp (ResidueField R)) :
    spMap (residue R) w = closedPoint R :=
  IsLocalRing.PrimeSpectrum.comap_residue _ _

theorem pullbackLeftPullbackSnd_congr_fst {X Y Z W : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y) (g'' : W ⟶ Z)
    (hg : g' ≫ g = g'') :
    (pullbackLeftPullbackSndIso f g g' ≪≫ pullback.congrHom rfl hg).hom ≫ pullback.fst f g'' =
      pullback.fst _ _ ≫ pullback.fst f g := by
  subst hg
  simp [pullback.map]

theorem pullbackLeftPullbackSnd_congr_snd {X Y Z W : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y) (g'' : W ⟶ Z)
    (hg : g' ≫ g = g'') :
    (pullbackLeftPullbackSndIso f g g' ≪≫ pullback.congrHom rfl hg).hom ≫ pullback.snd f g'' = pullback.snd _ _ := by
  subst hg
  simp [pullback.map]

theorem Emb.pullback_iso_of_closed (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R)
    (G' : Over S) [GrpObj G'] (hG : Smooth G'.hom) (E : Emb π G') (T : Scheme.{0}) (t : T ⟶ S)
    (k : T ⟶ Sp (ResidueField R)) (_hT : IsLocallyNoetherian T) (hTr : IsReduced T)
    (htk : t ≫ π = k ≫ spMap (residue R)) :
    ∃ (e : pullback G'.hom t ≅ pullback E.Y.hom k) (l : pullback G'.hom t ⟶ E.H.toScheme),
      e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ l ≫ E.H.ι = pullback.fst _ _ ∧
      l ≫ E.f = e.hom ≫ pullback.fst _ _ ≫ E.j := by
  haveI := hG
  haveI : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
  haveI : IsImmersion E.j := E.imm
  haveI : Smooth E.Y.hom := E.smooth
  have hclosed : ∀ w : (pullback G'.hom t : Scheme.{0}), π (G'.hom (pullback.fst G'.hom t w)) = closedPoint R := by
    intro w
    have h1 : π (G'.hom (pullback.fst G'.hom t w)) = (pullback.fst G'.hom t ≫ G'.hom ≫ π) w := by simp
    rw [h1, pullback.condition_assoc, htk]
    simp only [Scheme.Hom.comp_apply]
    exact spMap_residue_apply_eq_closedPoint R _
  have hrng : Set.range (pullback.fst G'.hom t) ⊆ Set.range E.H.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact E.H_all _ (hclosed w)
  let l : pullback G'.hom t ⟶ E.H.toScheme := IsOpenImmersion.lift E.H.ι (pullback.fst G'.hom t) hrng
  have hl : l ≫ E.H.ι = pullback.fst G'.hom t := IsOpenImmersion.lift_fac _ _ _
  haveI : IsReduced (pullback G'.hom t) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd G'.hom t)
  have hrj : Set.range (l ≫ E.f) ⊆ Set.range E.j := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨y, hy⟩ := (GlobalTheory.T.closedPoint_range_eq_fixedGroup_image R S π G' E).1 (l w) (by
      have e1 : E.H.ι (l w) = pullback.fst G'.hom t w := by rw [← Scheme.Hom.comp_apply, hl]
      rw [e1]; exact hclosed w)
    exact ⟨y, by rw [Scheme.Hom.comp_apply, hy]⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_lift_of_isReduced_of_isImmersion_range _ _ _ (l ≫ E.f) E.j inferInstance E.imm hrj
  have hgY : g ≫ E.Y.hom = pullback.snd G'.hom t ≫ k := by
    rw [← cancel_mono (spMap (residue R)), Category.assoc, ← E.j_over, reassoc_of% hg, E.f_over,
      reassoc_of% hl, pullback.condition_assoc, htk, Category.assoc]
  let h : pullback G'.hom t ⟶ pullback E.Y.hom k := pullback.lift g (pullback.snd G'.hom t) hgY
  have hh : h ≫ pullback.snd E.Y.hom k = pullback.snd G'.hom t := pullback.lift_snd _ _ _
  have hhf : h ≫ pullback.fst E.Y.hom k = g := pullback.lift_fst _ _ _
  haveI : IsIso h := by
    refine GlobalTheory.T.isIso_of_isIso_on_geometric_fibres_of_smooth T _ _ (pullback.snd G'.hom t) (pullback.snd E.Y.hom k) h hh inferInstance inferInstance ?_
    intro s
    let Ω := T.residueField s
    let x0 : Sp Ω ⟶ T := T.fromSpecResidueField s
    have hx : ∀ w, (x0 ≫ t ≫ π) w = closedPoint R := by
      intro w
      rw [htk]
      simp only [Scheme.Hom.comp_apply]
      exact spMap_residue_apply_eq_closedPoint R _
    obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (x0 ≫ t ≫ π) hx
    have hκk : x0 ≫ k = spMap κ := by
      rw [← cancel_mono (spMap (residue R)), Category.assoc, ← htk, hκ]
      simp only [spMap, ← Spec.map_comp]
      rfl
    obtain ⟨Ω', _, io, e', l', -, hl1, hl2⟩ := E.fib Ω (x0 ≫ t) κ (by rw [Category.assoc]; exact hκ)
    let x : Sp Ω' ⟶ T := spMap io ≫ x0
    refine ⟨Ω', inferInstance, x, ?_, ?_⟩
    · let w : Sp Ω' := closedPoint Ω'
      refine ⟨w, ?_⟩
      show (spMap io ≫ T.fromSpecResidueField s) w = s
      rw [Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    · have hxk : x ≫ k = spMap (io.comp κ) := by
        simp only [x, Category.assoc, hκk, spMap, ← Spec.map_comp]
        rfl
      let α : pullback (pullback.snd G'.hom t) x ≅ pullback G'.hom (spMap io ≫ x0 ≫ t) :=
        pullbackLeftPullbackSndIso G'.hom t x ≪≫ pullback.congrHom rfl (Category.assoc _ _ _)
      let β : pullback (pullback.snd E.Y.hom k) x ≅ pullback E.Y.hom (spMap (io.comp κ)) :=
        pullbackLeftPullbackSndIso E.Y.hom k x ≪≫ pullback.congrHom rfl hxk
      have hα : α.hom ≫ pullback.fst G'.hom (spMap io ≫ x0 ≫ t) =
          pullback.fst (pullback.snd G'.hom t) x ≫ pullback.fst G'.hom t :=
        pullbackLeftPullbackSnd_congr_fst _ _ _ _ _
      have hαs : α.hom ≫ pullback.snd G'.hom (spMap io ≫ x0 ≫ t) = pullback.snd (pullback.snd G'.hom t) x :=
        pullbackLeftPullbackSnd_congr_snd _ _ _ _ _
      have hβ : β.hom ≫ pullback.fst E.Y.hom (spMap (io.comp κ)) =
          pullback.fst (pullback.snd E.Y.hom k) x ≫ pullback.fst E.Y.hom k :=
        pullbackLeftPullbackSnd_congr_fst _ _ _ _ _
      have hβs : β.hom ≫ pullback.snd E.Y.hom (spMap (io.comp κ)) = pullback.snd (pullback.snd E.Y.hom k) x :=
        pullbackLeftPullbackSnd_congr_snd _ _ _ _ _
      have hll : pullback.fst (pullback.snd G'.hom t) x ≫ l = α.hom ≫ l' := by
        rw [← cancel_mono E.H.ι, Category.assoc, Category.assoc, hl, hl1, hα]
      have he's : e'.hom.left ≫ pullback.snd E.Y.hom (spMap (io.comp κ)) = pullback.snd G'.hom (spMap io ≫ x0 ≫ t) :=
        Over.w e'.hom
      let eb := α ≪≫ (Over.forget _).mapIso e' ≪≫ β.symm
      have key0 : ∀ φ : pullback (pullback.snd G'.hom t) x ⟶ pullback (pullback.snd E.Y.hom k) x,
          φ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ h → φ ≫ pullback.snd _ _ = pullback.snd _ _ → φ = eb.hom := by
        intro φ hφ hφs
        have heb : eb.hom = α.hom ≫ e'.hom.left ≫ β.inv := rfl
        rw [heb, ← Category.assoc, Iso.eq_comp_inv]
        apply pullback.hom_ext
        · rw [← cancel_mono E.j, Category.assoc, Category.assoc, reassoc_of% hβ, Category.assoc, Category.assoc,
            ← hl2, ← reassoc_of% hll, reassoc_of% hφ, reassoc_of% hhf, hg]
        · rw [Category.assoc, Category.assoc, hβs, he's, hαs, hφs]
      rw [key0 (pullback.map _ x _ x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) (pullback.lift_fst _ _ _)
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _))]
      infer_instance
  exact ⟨asIso h, l, hh, hl, by rw [asIso_hom, reassoc_of% hhf, hg]⟩

end GlobalTheory.Mum
