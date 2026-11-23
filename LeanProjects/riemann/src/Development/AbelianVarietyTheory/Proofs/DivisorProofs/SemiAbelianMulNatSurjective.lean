import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsClosedImageOfIsClosedSubgroup
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionLiftAbelianPartFiniteExtension
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SemiAbSurj

theorem surjective_of_rationalPoints {k : Type} [Field k] [IsAlgClosed k] {X Y : Over (Sp k)}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [Flat f.left]
    [LocallyOfFinitePresentation f.left]
    (h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ Y, ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = y) : Surjective f.left := by
  refine ⟨Set.range_eq_univ.1 ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ := RationalPoint.exists_pt_mem (f.left.isOpenMap.isOpen_range).isClosed_compl
    (Set.nonempty_compl.2 hne)
  obtain ⟨x, rfl⟩ := h y
  exact hy ⟨RationalPoint.pt x, rfl⟩

end GlobalTheory.SemiAbSurj

namespace GlobalTheory.SemiAbSurj

theorem exists_root_unit {k : Type} [Field k] [IsAlgClosed k] (m : ℕ) (hm : m ≠ 0)
    (u : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ) : ∃ v : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ, v ^ m = u := by
  let e : Γ((𝟙_ (Over (Sp k))).left, ⊤) ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e u.val) (Nat.pos_of_ne_zero hm)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at hz
    exact (u.isUnit.map e).ne_zero hz.symm
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom (Units.mk0 z hz0), Units.ext ?_⟩
  rw [← map_pow, Units.coe_map, Units.val_pow_eq_pow_val, Units.val_mk0, hz]
  exact e.symm_apply_apply u.val

theorem exists_pow_eq_of_torusExtension {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] (E : TorusExtension G) (m : ℕ) (hm : m ≠ 0)
    (x : 𝟙_ (Over (Sp k)) ⟶ G) : ∃ y : 𝟙_ (Over (Sp k)) ⟶ G, y ^ m = x := by
  classical
  letI := E.addCommGroup
  letI := E.free
  letI := E.grpB
  haveI := E.q_hom
  haveI := E.i_hom
  have hB := E.isAbelian
  haveI := hB.smooth
  haveI := hB.comm

  have hsB := GlobalTheory.AbelianLimit.surjective_pow E.B hB m (Nat.one_le_iff_ne_zero.2 hm)
  haveI : LocallyOfFiniteType (((𝟙 E.B) ^ m : E.B ⟶ E.B).left ≫ E.B.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType ((𝟙 E.B) ^ m : E.B ⟶ E.B).left := locallyOfFiniteType_of_comp _ E.B.hom
  obtain ⟨p, hp⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ((𝟙 E.B) ^ m : E.B ⟶ E.B).left (x ≫ E.q).left
  let b' : 𝟙_ (Over (Sp k)) ⟶ E.B := Over.homMk p (by
    have := Over.w (x ≫ E.q)
    rw [hp, Category.assoc, Over.w] at this
    exact this)
  have hb' : b' ^ m = x ≫ E.q := by
    rw [← Category.comp_id b', ← MonObj.comp_pow]
    exact Over.OverMorphism.ext hp.symm

  haveI : LocallyOfFiniteType (E.q.left ≫ E.B.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType E.q.left := locallyOfFiniteType_of_comp _ E.B.hom
  haveI := E.q_surjective
  obtain ⟨p', hp'⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective E.q.left b'.left
  let g' : 𝟙_ (Over (Sp k)) ⟶ G := Over.homMk p' (by
    have := Over.w b'
    rw [hp', Category.assoc, Over.w] at this
    exact this)
  have hg' : g' ≫ E.q = b' := Over.OverMorphism.ext hp'.symm

  let qh := IsMonHom.monoidHom E.q (𝟙_ (Over (Sp k)))
  let ih := IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))
  have hq : ∀ z, qh z = z ≫ E.q := fun _ => rfl
  have hi : ∀ z, ih z = z ≫ E.i := fun _ => rfl
  let h := x * (g' ^ m)⁻¹
  have hh : h ≫ E.q = 1 := by
    rw [← hq, map_mul, map_inv, map_pow, hq, hq, hg', hb', mul_inv_cancel]
  let s := E.isKernel.lift h (toUnit _) (by rw [hh, Hom.one_def])
  have hs : s ≫ E.i = h := E.isKernel.lift_fst _ _ _
  let e := splitTorusPointsEquiv (Sp k) E.X (𝟙_ (Over (Sp k)))
  obtain ⟨d, hd⟩ := GlobalTheory.TorsionLift.exists_char_root (Module.Free.chooseBasis ℤ E.X) m (e s)
    fun i => exists_root_unit m hm _
  refine ⟨e.symm d ≫ E.i * g', ?_⟩
  rw [mul_pow, ← hi, ← map_pow, ← map_pow, hd, MulEquiv.symm_apply_apply, hi, hs]
  exact inv_mul_cancel_right x (g' ^ m)

end GlobalTheory.SemiAbSurj

namespace GlobalTheory.SemiAbSurj

theorem surjective_pow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ m : ℕ, m ≠ 0 → Surjective ((𝟙 G) ^ m : G ⟶ G).left := by
  intro S G _ _ hG m hm
  have hfl := (GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow S G hG m hm).1
  haveI := hG.smooth
  refine ⟨fun x => ?_⟩
  let K := AlgebraicClosure (S.residueField (G.hom x))
  let t : Sp K ⟶ S := spMap (algebraMap (S.residueField (G.hom x)) K) ≫ S.fromSpecResidueField (G.hom x)
  have ht : G.hom x = t (IsLocalRing.closedPoint K) := (Scheme.fromSpecResidueField_apply _ _).symm
  let B := (Over.pullback t).obj G
  have hP := GlobalTheory.AbelianLimit.isPullback_pow (isGrpPullback_pullback G t) m
  haveI : LocallyOfFiniteType B.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom t))
  haveI : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  haveI : Flat ((𝟙 B) ^ m : B ⟶ B).left := MorphismProperty.of_isPullback hP hfl
  haveI : LocallyOfFiniteType (((𝟙 B) ^ m : B ⟶ B).left ≫ B.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType ((𝟙 B) ^ m : B ⟶ B).left := locallyOfFiniteType_of_comp _ B.hom
  haveI : LocallyOfFinitePresentation ((𝟙 B) ^ m : B ⟶ B).left := inferInstance
  obtain ⟨E⟩ := hG.fibres K t
  have hs : Surjective ((𝟙 B) ^ m : B ⟶ B).left := by
    refine surjective_of_rationalPoints _ fun y => ?_
    obtain ⟨z, hz⟩ := exists_pow_eq_of_torusExtension B E m hm y
    exact ⟨z, by rw [MonObj.comp_pow, Category.comp_id, hz]⟩
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback G.hom t) x _ ht
  obtain ⟨z, rfl⟩ := ((𝟙 B) ^ m : B ⟶ B).left.surjective y
  exact ⟨pullback.fst G.hom t z,
    (congrArg (fun g => g z) (GlobalTheory.AbelianLimit.pow_comm (isGrpPullback_pullback G t) m)).symm.trans hy⟩

end GlobalTheory.SemiAbSurj
