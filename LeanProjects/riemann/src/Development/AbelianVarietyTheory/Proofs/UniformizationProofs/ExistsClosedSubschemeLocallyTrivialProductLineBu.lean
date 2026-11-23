import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TrivOnOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenThetaAbelianVariety

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TrivSubscheme

theorem exists_idealSheaf {T : Scheme.{0}} (P : ∀ Y : Scheme.{0}, (Y ⟶ T) → Prop)
    (hcomp : ∀ (Y Z : Scheme.{0}) (x : Y ⟶ T) (h : Z ⟶ Y), P Y x → P Z (h ≫ x))
    (hloc : ∀ (Y : Scheme.{0}) (x : Y ⟶ T),
      (∀ y : Y, ∃ V : Y.affineOpens, y ∈ V.1 ∧ P _ (V.2.fromSpec ≫ x)) → P Y x)
    (haff : ∀ U : T.affineOpens, ∃ I : Ideal Γ(T, U), ∀ (S : CommRingCat.{0}) (g : Γ(T, U) ⟶ S),
      P _ (Spec.map g ≫ U.2.fromSpec) ↔ I ≤ RingHom.ker g.hom) :
    ∃ I : T.IdealSheafData, ∀ (Y : Scheme.{0}) (x : Y ⟶ T), P Y x ↔ I ≤ x.ker := by
  choose J hJ using haff
  have hmap : ∀ (U V : T.affineOpens) (h : V.1 ≤ U.1),
      (J U).map (T.presheaf.map (homOfLE h).op).hom = J V := by
    intro U V h
    have key : ∀ K : Ideal Γ(T, V), (J U).map (T.presheaf.map (homOfLE h).op).hom ≤ K ↔ J V ≤ K := by
      intro K
      have h₁ := hJ V _ (CommRingCat.ofHom (Ideal.Quotient.mk K))
      have h₂ := hJ U _ (T.presheaf.map (homOfLE h).op ≫ CommRingCat.ofHom (Ideal.Quotient.mk K))
      rw [Spec.map_comp, Category.assoc, IsAffineOpen.map_fromSpec U.2 V.2, h₁, CommRingCat.hom_comp,
        ← RingHom.comap_ker, CommRingCat.hom_ofHom, Ideal.mk_ker] at h₂
      rw [Ideal.map_le_iff_le_comap, h₂]
    exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)
  refine ⟨⟨J, fun U f => hmap U (T.affineBasicOpen f) _, _, rfl⟩, fun Y x => ?_⟩
  have hV : ∀ (U : T.affineOpens) (V : Y.affineOpens) (e : V.1 ≤ x ⁻¹ᵁ U.1),
      P _ (V.2.fromSpec ≫ x) ↔ J U ≤ RingHom.ker (x.appLE U.1 V.1 e).hom := fun U V e => by
    rw [← hJ, IsAffineOpen.SpecMap_appLE_fromSpec x U.2 V.2 e]
  have hex : ∀ (W : Y.Opens) (y : Y), y ∈ W → ∃ V : Y.affineOpens, y ∈ V.1 ∧ V.1 ≤ W := fun W y hy => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy W.isOpen
    exact ⟨⟨V, hV⟩, hyV, hle⟩
  constructor
  · intro hx
    refine Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U a ha => ?_
    refine Y.IsSheaf.section_ext fun y hy => ?_
    obtain ⟨V, hyV, hle⟩ := hex _ y hy
    refine ⟨V.1, hle, hyV, ?_⟩
    exact ((hV U V hle).1 (hcomp _ _ _ _ hx) ha).trans (map_zero _).symm
  · intro hx
    refine hloc Y x fun y => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (x y)) isOpen_univ
    obtain ⟨V, hyV, hle⟩ := hex (x ⁻¹ᵁ U) y hyU
    refine ⟨V, hyV, (hV ⟨U, hU⟩ V hle).2 fun a ha => ?_⟩
    have h₁ : (x.app U).hom a = 0 := x.ideal_ker_le ⟨U, hU⟩ (hx ⟨U, hU⟩ ha)
    rw [RingHom.mem_ker, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (congrArg _ h₁).trans (map_zero _)

theorem triv_pull_iff {X Y Z : Scheme.{0}} (M : LB X) (f : Y ⟶ X) (h : Z ⟶ Y) :
    Triv ((M.pull f).pull h) ↔ Triv (M.pull (h ≫ f)) :=
  ⟨fun ⟨t, ht⟩ => exists_isGen_linComb_of_pull M _ _ _ t ht, CubeOpen.triv_pull_pull f h⟩

variable {X T : Scheme.{0}} (p : X ⟶ T) (F : LB X)

def TrivOver {Y : Scheme.{0}} (x : Y ⟶ T) : Prop := Triv (F.pull (pullback.fst p x))

def LocTrivOver (Y : Scheme.{0}) (x : Y ⟶ T) : Prop :=
  ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ TrivOver p F (U.ι ≫ x)

variable {p F}

theorem TrivOver.triv {Y Z : Scheme.{0}} {x : Y ⟶ T} (H : TrivOver p F x) (k : Z ⟶ X) (z : Z ⟶ Y)
    (e : k ≫ p = z ≫ x) : Triv (F.pull k) :=
  CubeOpen.triv_comp (pullback.lift k z e) (pullback.lift_fst _ _ _) H

theorem TrivOver.comp {Y Z : Scheme.{0}} {x : Y ⟶ T} (H : TrivOver p F x) (h : Z ⟶ Y) {w : Z ⟶ T}
    (e : h ≫ x = w) : TrivOver p F w :=
  H.triv _ (pullback.snd _ _ ≫ h) (by rw [pullback.condition, Category.assoc, e])

theorem LocTrivOver.comp (Y Z : Scheme.{0}) (x : Y ⟶ T) (h : Z ⟶ Y) (H : LocTrivOver p F Y x) :
    LocTrivOver p F Z (h ≫ x) := fun z => by
  obtain ⟨U, hU, ht⟩ := H (h z)
  exact ⟨h ⁻¹ᵁ U, hU, ht.comp (h ∣_ U) (by rw [morphismRestrict_ι_assoc])⟩

theorem locTrivOver_of_affine (Y : Scheme.{0}) (x : Y ⟶ T)
    (H : ∀ y : Y, ∃ V : Y.affineOpens, y ∈ V.1 ∧ LocTrivOver p F _ (V.2.fromSpec ≫ x)) :
    LocTrivOver p F Y x := fun y => by
  obtain ⟨V, hy, hV⟩ := H y
  obtain ⟨q, rfl⟩ := V.2.range_fromSpec.ge hy
  obtain ⟨U, hU, ht⟩ := hV q
  haveI : IsOpenImmersion V.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec (U := V.1) V.2
  have hr : Set.range (V.2.fromSpec ''ᵁ U).ι ⊆ Set.range (U.ι ≫ V.2.fromSpec) := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  refine ⟨V.2.fromSpec ''ᵁ U, ⟨q, hU, rfl⟩, ht.comp (IsOpenImmersion.lift _ _ hr) ?_⟩
  rw [← Category.assoc U.ι, IsOpenImmersion.lift_fac_assoc]

theorem locTrivOver_iff {Y X' : Scheme.{0}} {x : Y ⟶ T} {π : X' ⟶ X} {f' : X' ⟶ Y} (h : IsPullback π f' p x) :
    LocTrivOver p F Y x ↔ ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ Triv (F.pull ((f' ⁻¹ᵁ U).ι ≫ π)) := by
  refine forall_congr' fun y => exists_congr fun U => and_congr_right fun _ => ⟨fun ht => ?_, fun ht => ?_⟩
  · exact ht.triv _ (f' ∣_ U) (by rw [morphismRestrict_ι_assoc, Category.assoc, h.w])
  · have hp := (isPullback_morphismRestrict f' U).flip.paste_horiz h
    exact CubeOpen.triv_comp (hp.lift _ _ pullback.condition) (hp.lift_fst _ _ _) ht

theorem exists_closed_locTriv : GlobalFnsSt → ∀ (R : Type) [CommRing R] (T B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ F : LB (T ⊗ B).left, F.IsLB → ∃ (H : Over (Spec (CommRingCat.of R))) (j : H ⟶ T), IsClosedImmersion j.left ∧ ∀ (T' : Over (Spec (CommRingCat.of R))) (x : T' ⟶ T), (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧ Triv ((F.pull (x ▷ B).left).pull ((fst T' B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T' ⟶ H, y ≫ j = x := by
  intro hG R _ T B _ hB hproj F hF
  have h₀ : IsPullback (pullback.snd T.hom B.hom) (fst T B).left B.hom T.hom :=
    (IsPullback.of_hasPullback T.hom B.hom).flip
  obtain ⟨I, hI⟩ := exists_idealSheaf (LocTrivOver (fst T B).left F) LocTrivOver.comp locTrivOver_of_affine
    (fun U => by
      let t : Spec (CommRingCat.of Γ(T.left, U)) ⟶ Spec (CommRingCat.of R) := U.2.fromSpec ≫ T.hom
      have h₁ : IsPullback (pullback.fst B.hom t) (pullback.snd B.hom t) B.hom (U.2.fromSpec ≫ T.hom) :=
        IsPullback.of_hasPullback _ _
      let φ := h₀.lift _ _ (h₁.w.trans (Category.assoc _ _ _).symm)
      have h₂ : IsPullback φ (pullback.snd B.hom t) (fst T B).left U.2.fromSpec :=
        IsPullback.of_right (by rw [h₀.lift_fst]; exact h₁) (h₀.lift_snd _ _ _) h₀
      obtain ⟨I, hI⟩ := TrivRep.exists_ideal_locTriv hG Γ(T.left, U) ((Over.pullback t).obj B)
        (CubeGen.isAb_baseChange hB t) (CubeProj.isProjBy_baseChange hproj h₁) (F.pull φ) (LB.isLB_pull hF φ)
      refine ⟨I, fun S g => ?_⟩
      have h₃ := IsPullback.of_hasPullback (pullback.snd B.hom t) (Spec.map g)
      rw [← hI S g.hom _ _ _ h₃, locTrivOver_iff (h₃.paste_horiz h₂)]
      refine forall_congr' fun y => exists_congr fun V => and_congr_right fun _ => ?_
      rw [← Category.assoc]
      exact ((triv_pull_iff _ _ _).trans (triv_pull_iff _ _ _)).symm)
  refine ⟨Over.mk (I.subschemeι ≫ T.hom), Over.homMk I.subschemeι rfl,
    inferInstanceAs (IsClosedImmersion I.subschemeι), fun T' x => ?_⟩
  have h₄ : IsPullback (x ▷ B).left (fst T' B).left (fst T B).left x.left := by
    refine IsPullback.of_right ?_ (Over.whiskerRight_left_fst x) h₀
    rw [Over.whiskerRight_left_snd, Over.w]
    exact (IsPullback.of_hasPullback T'.hom B.hom).flip
  simp only [triv_pull_iff]
  rw [← locTrivOver_iff h₄, hI]
  constructor
  · intro h
    have h' : I.subschemeι.ker ≤ x.left.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι x.left h') ?_, ?_⟩
    · exact (IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w x)
    · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  · rintro ⟨y, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp y.left I.subschemeι)

end GlobalTheory.TrivSubscheme
