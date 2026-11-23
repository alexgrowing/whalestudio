import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

namespace SchemeImage

variable {Y Z : Scheme.{u}} (f : Y ⟶ Z) [QuasiCompact f] (W : Z.Opens)

theorem ker_morphismRestrict : (f ∣_ W).ker = f.ker.comap W.ι := by
  ext V : 2
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f (f ∣_ W) (f ⁻¹ᵁ W).ι W.ι
    (isPullback_morphismRestrict f W) V,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]

theorem exists_lift_imageι_morphismRestrict {C : Scheme.{u}} (c : C ⟶ W.toScheme)
    [IsClosedImmersion c] (g : (f ⁻¹ᵁ W).toScheme ⟶ C) (hg : g ≫ c = f ∣_ W) :
    ∃ k : (f.imageι ⁻¹ᵁ W).toScheme ⟶ C, k ≫ c = f.imageι ∣_ W := by
  have H : c.ker ≤ (f.imageι ∣_ W).ker := by
    rw [ker_morphismRestrict, Scheme.IdealSheafData.ker_subschemeι, ← ker_morphismRestrict, ← hg]
    exact Scheme.Hom.le_ker_comp g c
  exact ⟨IsClosedImmersion.lift c _ H, IsClosedImmersion.lift_fac _ _ _⟩

def imageRestrictLift [IsClosedImmersion (f ∣_ W)] :
    (f.imageι ⁻¹ᵁ W).toScheme ⟶ (f ⁻¹ᵁ W).toScheme :=
  IsClosedImmersion.lift (f ∣_ W) (f.imageι ∣_ W) (by
    rw [ker_morphismRestrict, ker_morphismRestrict, Scheme.IdealSheafData.ker_subschemeι])

@[reassoc (attr := simp)]
lemma imageRestrictLift_fac [IsClosedImmersion (f ∣_ W)] :
    imageRestrictLift f W ≫ (f ∣_ W) = f.imageι ∣_ W :=
  IsClosedImmersion.lift_fac _ _ _

instance isIso_imageRestrictLift [IsClosedImmersion (f ∣_ W)] :
    IsIso (imageRestrictLift f W) :=
  IsClosedImmersion.isIso_lift _ _ (by
    rw [ker_morphismRestrict, ker_morphismRestrict, Scheme.IdealSheafData.ker_subschemeι])

omit [QuasiCompact f] in

def imageLift {C : Scheme.{u}} (c : C ⟶ Z) [IsClosedImmersion c] (g : Y ⟶ C) (hg : g ≫ c = f) :
    f.image ⟶ C :=
  IsClosedImmersion.lift c f.imageι (by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← hg]
    exact Scheme.Hom.le_ker_comp g c)

omit [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma imageLift_fac {C : Scheme.{u}} (c : C ⟶ Z) [IsClosedImmersion c] (g : Y ⟶ C)
    (hg : g ≫ c = f) : imageLift f c g hg ≫ c = f.imageι :=
  IsClosedImmersion.lift_fac _ _ _

end SchemeImage

section EqLocus

variable {T S B : Scheme.{u}} (p : S ⟶ B) [IsSeparated p] (g h : T ⟶ S) (hgh : g ≫ p = h ≫ p)

abbrev eqLocus : Scheme.{u} :=
  pullback (pullback.diagonal p) (pullback.lift g h hgh)

abbrev eqLocusι : eqLocus p g h hgh ⟶ T := pullback.snd _ _

instance : IsClosedImmersion (eqLocusι p g h hgh) := by
  dsimp only [eqLocusι, eqLocus]
  infer_instance

omit [IsSeparated p] in

@[reassoc]
lemma eqLocusι_comp_eq : eqLocusι p g h hgh ≫ g = eqLocusι p g h hgh ≫ h := by
  have h₁ := congrArg (· ≫ pullback.fst p p) (pullback.condition (f := pullback.diagonal p)
    (g := pullback.lift g h hgh))
  have h₂ := congrArg (· ≫ pullback.snd p p) (pullback.condition (f := pullback.diagonal p)
    (g := pullback.lift g h hgh))
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    pullback.lift_fst, pullback.lift_snd] at h₁ h₂
  rw [← h₁, h₂]

def eqLocusLift {V : Scheme.{u}} (t : V ⟶ T) (ht : t ≫ g = t ≫ h) : V ⟶ eqLocus p g h hgh :=
  pullback.lift (t ≫ g) t (by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
        pullback.diagonal_snd, Category.comp_id, ht])

omit [IsSeparated p] in
@[reassoc (attr := simp)]
lemma eqLocusLift_ι {V : Scheme.{u}} (t : V ⟶ T) (ht : t ≫ g = t ≫ h) :
    eqLocusLift p g h hgh t ht ≫ eqLocusι p g h hgh = t :=
  pullback.lift_snd _ _ _

end EqLocus

end

end GroundTheory.Arith.SchemeCoh
