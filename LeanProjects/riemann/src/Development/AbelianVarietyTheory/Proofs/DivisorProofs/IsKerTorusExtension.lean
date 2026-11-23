import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackKernelBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusPart

def GoodCover {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (u : splitTorus S X ⟶ G) : Prop :=
  ∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen u V

def IsKer {S : Scheme.{0}} {T G B : Over S} [GrpObj G] [GrpObj B] (u : T ⟶ G) (q : G ⟶ B) : Prop :=
  IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧ IsPullback u (toUnit _) q η[B]

def TorPol {O : Type} [CommRing O] (c : O →+* O) {S : Scheme.{0}} {G : Over S} [GrpObj G] (i : OAct O G) {X : Type}
    [AddCommGroup X] (u : splitTorus S X ⟶ G) {K : Type} [Field K] (x : Sp K ⟶ S) : Prop :=
  ∃ (G' : Over (Sp K)) (_ : GrpObj G') (i' : OAct O G') (φ : G'.left ⟶ G.left) (u' : splitTorus (Sp K) X ⟶ G')
    (P : Out.PolAV (Sp K)) (q : G' ⟶ P.A) (j : OAct O P.A),
    IsActPull i' i x φ ∧ TorusCompat x φ u' u ∧ IsKer u' q ∧ (∀ a, i'.act a ≫ q = q ≫ j.act a) ∧ IsRosati c P j

def QFin {S : Scheme.{0}} (Z : Over S) : Prop :=
  Flat Z.hom ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ LocallyQuasiFinite Z.hom

def RatOver {S : Scheme.{0}} (Z : Over S) {K : Type} [Field K] (x : Sp K ⟶ S) : Prop :=
  ∀ (Ω : Type) [Field Ω] (β : K →+* Ω) (y : Sp Ω ⟶ Z.left), y ≫ Z.hom = spMap β ≫ x →
    ∃ y₁ : Sp K ⟶ Z.left, y₁ ≫ Z.hom = x ∧ spMap β ≫ y₁ = y

def WtGeneric : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G),
    IsIntegral (splitTorus S X ⊗ G).left → ∀ (V : G.left.Opens) (f : Γ(G.left, V)) (χ : X) (Z : Over S)
      (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), IsDominant (lift t g).left →
      ∀ (h₁ : ⊤ ≤ ((t ≫ u) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
        (((t ≫ u) * g).left.appLE _ ⊤ h₁).hom f =
          t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom f → Wt u V f χ

theorem isKer_of_isQuot {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsQuot u q) : IsKer u q :=
  have := h.2.2.2.2.1
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, inferInstance, h.2.2.2.2.2.1⟩

theorem isKer_torusExtension {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (T : TorusExtension G) :
    letI := T.addCommGroup; letI := T.grpB; IsKer T.i T.q :=
  ⟨T.q_hom, T.q_flat, T.q_surjective, T.q_quasiCompact, T.isKernel⟩

theorem IsKer.comp_iso {S : Scheme.{0}} {T G B B' : Over S} [GrpObj G] [GrpObj B] [GrpObj B'] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsKer u q) (e : B ≅ B') (he : IsMonHom (q ≫ e.hom)) : IsKer u (q ≫ e.hom) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  refine ⟨he, by rw [Over.comp_left]; infer_instance, by rw [Over.comp_left]; infer_instance,
    by rw [Over.comp_left]; infer_instance, h₅.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
      (by simp) ?_⟩
  rw [Iso.refl_hom, Category.id_comp, ← IsMonHom.one_hom q, Category.assoc, IsMonHom.one_hom]

theorem IsKer.baseChange {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G]
    [GrpObj B] {G' B' : Over S'} [GrpObj G'] [GrpObj B'] {φ : G'.left ⟶ G.left} {ψ : B'.left ⟶ B.left}
    (hφ : IsGrpPullback G' G f φ) (hψ : IsGrpPullback B' B f ψ) {u : splitTorus S X ⟶ G} {u' : splitTorus S' X ⟶ G'}
    (hT : TorusCompat f φ u' u) {q : G ⟶ B} (h : IsKer u q) :
    ∃ q' : G' ⟶ B', IsKer u' q' ∧ IsPullback φ q'.left q.left ψ := by
  obtain ⟨e, he, heF⟩ := grpPullback_iso hφ (isGrpPullback_pullback G f)
  obtain ⟨d, hd, hdF⟩ := grpPullback_iso (isGrpPullback_pullback B f) hψ
  obtain ⟨_, _, _, _, h₅⟩ := h
  have sq := isPullback_pullback_map_left f q
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hi : u' ≫ e.hom = (SplitTorus.bcIso f X).hom ≫ (Over.pullback f).map u := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have a := (isPullback_pullback_map_left f u).w
    have b := SplitTorus.bcIso_hom_fst f X
    exact ((Category.assoc _ _ _).trans ((congrArg (u'.left ≫ ·) heF).trans (torusCompat_iff.1 hT).symm)).trans
      ((congrArg (· ≫ u.left) b.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) a).trans (Category.assoc _ _ _).symm)))
  have hk : IsPullback u' (toUnit _) (e.hom ≫ (Over.pullback f).map q) (η[(Over.pullback f).obj B]) := by
    refine (isPullback_kernel_baseChange f h₅).of_iso (SplitTorus.bcIso f X).symm e.symm (Iso.refl _)
      (Iso.refl _) ?_ (toUnit_unique _ _) (by simp) (by simp)
    rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hi, Iso.inv_hom_id_assoc]
  have h₁ : Flat ((Over.pullback f).map q).left := MorphismProperty.of_isPullback (P := @Flat) sq inferInstance
  have h₂ : Surjective ((Over.pullback f).map q).left :=
    MorphismProperty.of_isPullback (P := @Surjective) sq inferInstance
  have h₃ : QuasiCompact ((Over.pullback f).map q).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have hK : IsKer u' (e.hom ≫ (Over.pullback f).map q) := ⟨inferInstance, by rw [Over.comp_left]; infer_instance,
    by rw [Over.comp_left]; infer_instance, by rw [Over.comp_left]; infer_instance, hk⟩
  refine ⟨_, hK.comp_iso d inferInstance, ?_⟩
  refine IsPullback.of_bot (v₂₁ := B'.hom) (v₂₂ := B.hom) ?_ ?_ hψ.1
  · rw [Over.w, Over.w]
    exact hφ.1
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hdF, ← heF, Category.assoc]
    exact congrArg (_ ≫ ·) sq.w

theorem IsKer.exists_oAct {S : Scheme.{0}} {T G B : Over S} [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsKer u q) {O : Type} [CommRing O] (i : OAct O G) (hu : ∀ a, u ≫ i.act a ≫ q = toUnit _ ≫ η[B]) :
    ∃ j : OAct O B, ∀ a, i.act a ≫ q = q ≫ j.act a := by
  obtain ⟨_, _, _, _, h₅⟩ := h
  have := i.hom
  have : Epi q := FlatQuotient.epi_of_flat_surjective q
  choose fB hm hfB using fun a => FlatQuotient.exists_desc q u (i.act a ≫ q) h₅ (hu a)
  refine ⟨⟨fB, hm, ?_, fun a b => ?_, fun a b => ?_⟩, fun a => (hfB a).symm⟩
  · rw [← cancel_epi q, hfB, i.one, Category.comp_id, Category.id_comp]
  · rw [← cancel_epi q, hfB, i.mul, Category.assoc, ← hfB, reassoc_of% hfB]
  · rw [← cancel_epi q, hfB, MonObj.comp_mul, hfB, hfB, i.add, MonObj.mul_comp]

theorem exists_isActPull {O : Type} [CommRing O] {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G]
    [IsCommMonObj G] (i : OAct O G) : IsActPull (OAct.pullback f G i) i f (pullback.fst G.hom f) :=
  ⟨isGrpPullback_pullback G f, fun _ => pullback.lift_fst _ _ _⟩

end GlobalTheory.TorusPart
