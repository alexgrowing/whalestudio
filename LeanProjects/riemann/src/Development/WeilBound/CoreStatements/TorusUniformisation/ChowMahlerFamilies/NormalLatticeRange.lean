import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

namespace PositivityTheory.Xgn.NormalLatticeRange

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

theorem specMap_dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') :
    Spec.map (CommRingCat.ofHom (dualMap g)) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom (dualMap (g.comp f))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, dualMap_comp]

theorem one_left {S : Scheme.{0}} (G : Over S) [GrpObj G] {T : Scheme.{0}} (x : T ⟶ S) :
    (1 : Over.mk x ⟶ G).left = x ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem transport {S : Scheme.{0}} (G : Over S) [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S)
    (hx : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    ∃ v' : epsAt x' ⟶ G, IsTanAt G x' v' ∧ v'.left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left := by
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left) ?_, ?_, rfl⟩
  · have hw := Over.w v
    simp only [Category.assoc, hw, epsAt, Over.mk_hom]
    rw [← hx, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => TrivSqZeroExt.ext (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
      (by simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
  · unfold IsTanAt at hv ⊢
    rw [one_left] at hv ⊢
    simp only [Over.homMk_left]
    have hring : (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap φ) =
        φ.comp (TrivSqZeroExt.fstHom R R R).toRingHom := RingHom.ext fun a => by simp [dualMap]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, hv, ← hx, Category.assoc]

end PositivityTheory.Xgn.NormalLatticeRange

open PositivityTheory.Xgn.NormalLatticeRange in
theorem PositivityTheory.Xgn.normal_lattice_range : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (h : IsCptGen ξ) (G : Over X) [GrpObj G] (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (Ep : Type) [AddCommGroup Ep] [Module (regAt ξ p) Ep] (Mp : LieModel G (regPt h p) Ep) (j : Ep →ₗ[regAt ξ p] E), (∀ e, (M.pt (j e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left) → (M.lat p : Set E) = Set.range j := by
  intro X Ω _ ξ h G _ E _ _ M p Ep _ _ Mp j hj
  simp only [spMap] at hj
  have hgen1 : (genMap ξ p).comp (regIso h p).symm.toRingHom = algebraMap (regAt ξ p) Ω :=
    RingHom.ext fun r => congrArg Subtype.val ((regIso h p).apply_symm_apply r)
  have hgen2 : (algebraMap (regAt ξ p) Ω).comp (regIso h p).toRingHom = genMap ξ p :=
    RingHom.ext fun a => rfl
  apply Set.Subset.antisymm
  · have hle : M.lat p ≤ LinearMap.range j := by
      apply Submodule.span_le.2
      rintro e ⟨v, hv, he⟩
      obtain ⟨v', hv', hv'l⟩ :=
        transport G (regIso h p).toRingHom (X.fromSpecStalk p.1) (regPt h p) rfl v hv
      obtain ⟨e', he'⟩ := Mp.onto v' hv'
      refine ⟨e', M.inj (Over.OverMorphism.ext ?_)⟩
      rw [hj, he', hv'l, he, ← Category.assoc, specMap_dualMap_comp, hgen2]
    exact fun e he => LinearMap.mem_range.1 (hle he)
  · rintro _ ⟨e', rfl⟩
    have hx : Spec.map (CommRingCat.ofHom (regIso h p).symm.toRingHom) ≫ regPt h p =
        X.fromSpecStalk p.1 := by
      have hid : (regIso h p).symm.toRingHom.comp (regIso h p).toRingHom = RingHom.id _ := by
        ext a
        simp
      simp only [regPt, spMap]
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hid]
      simp
    obtain ⟨v', hv', hv'l⟩ := transport G (regIso h p).symm.toRingHom (regPt h p) (X.fromSpecStalk p.1) hx
      (Mp.pt e') (Mp.tan e')
    exact Submodule.subset_span ⟨v', hv', by rw [hj, hv'l, ← Category.assoc, specMap_dualMap_comp, hgen1]⟩
