import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TanSRestrict

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Dual

variable {S : Type} [CommRing S] (s : S)

abbrev dAway : DualNumber S →+* DualNumber (Localization.Away s) := dualMapR (algebraMap S (Localization.Away s))

theorem eq_inl_add_inr {R : Type} [CommRing R] (x : DualNumber R) :
    x = TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inl x.snd * TrivSqZeroExt.inr 1 := by
  ext <;> simp

theorem dAway_eps : dAway s (TrivSqZeroExt.inr 1) = TrivSqZeroExt.inr 1 := by
  ext <;> simp [dAway, dualMapR]

theorem dAway_inl (a : S) : dAway s (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (algebraMap S _ a) := by
  ext <;> simp [dAway, dualMapR]

theorem dAway_ext {T : Type} [CommRing T] {χ₁ χ₂ : DualNumber (Localization.Away s) →+* T}
    (h : χ₁.comp (dAway s) = χ₂.comp (dAway s)) : χ₁ = χ₂ := by
  have hinl : χ₁.comp (TrivSqZeroExt.inlHom _ _) = χ₂.comp (TrivSqZeroExt.inlHom _ _) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    refine RingHom.ext fun a => ?_
    have h1 := RingHom.congr_fun h (TrivSqZeroExt.inl a)
    simp only [RingHom.comp_apply, dAway_inl] at h1
    simpa using h1
  have heps : χ₁ (TrivSqZeroExt.inr 1) = χ₂ (TrivSqZeroExt.inr 1) := by
    have h1 := RingHom.congr_fun h (TrivSqZeroExt.inr 1)
    simp only [RingHom.comp_apply, dAway_eps] at h1
    exact h1
  refine RingHom.ext fun x => ?_
  have h1 := RingHom.congr_fun hinl x.fst
  have h2 := RingHom.congr_fun hinl x.snd
  simp only [RingHom.comp_apply, TrivSqZeroExt.inlHom_apply] at h1 h2
  rw [eq_inl_add_inr x, map_add, map_add, map_mul, map_mul, heps, h1, h2]

theorem dAway_lift {T : Type} [CommRing T] (gg : DualNumber S →+* T) (hu : IsUnit (gg (TrivSqZeroExt.inl s))) :
    ∃ χ : DualNumber (Localization.Away s) →+* T, χ.comp (dAway s) = gg := by
  let g0 : S →+* T := gg.comp (TrivSqZeroExt.inlHom S S)
  have hu0 : IsUnit (g0 s) := hu
  let φ : Localization.Away s →+* T := IsLocalization.Away.lift s hu0
  have hφ : ∀ a : S, φ (algebraMap S _ a) = gg (TrivSqZeroExt.inl a) := fun a =>
    IsLocalization.lift_eq _ a
  let e := gg (TrivSqZeroExt.inr 1)
  have he : e * e = 0 := by
    simp only [e, ← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]
  refine ⟨{ toFun := fun x => φ x.fst + φ x.snd * e
            map_one' := by simp
            map_mul' := fun x y => by
              simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul,
                MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, map_add, map_mul]
              linear_combination (-(φ x.snd * φ y.snd)) * he
            map_zero' := by simp
            map_add' := fun x y => by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add]; ring }, ?_⟩
  refine RingHom.ext fun x => ?_
  conv_rhs => rw [eq_inl_add_inr x]
  simp only [RingHom.comp_apply, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, dAway, dualMapR,
    TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, map_zero, add_zero, zero_add, map_add, map_mul, hφ]
  simp only [zero_mul, add_zero, e]

end Dual

section Iso

variable {S : Type} [CommRing S] (s : S)

abbrev Ld : Type := Localization.Away (TrivSqZeroExt.inl s : DualNumber S)

theorem isUnit_dAway : IsUnit (dAway s (TrivSqZeroExt.inl s)) := by
  rw [dAway_inl]
  exact (IsLocalization.Away.algebraMap_isUnit s).map (TrivSqZeroExt.inlHom _ _)

def toL : DualNumber (Localization.Away s) →+* Ld s :=
  (dAway_lift s (algebraMap (DualNumber S) (Ld s)) (IsLocalization.Away.algebraMap_isUnit _)).choose

theorem toL_comp : (toL s).comp (dAway s) = algebraMap (DualNumber S) (Ld s) :=
  (dAway_lift s (algebraMap (DualNumber S) (Ld s)) (IsLocalization.Away.algebraMap_isUnit _)).choose_spec

def fromL : Ld s →+* DualNumber (Localization.Away s) :=
  IsLocalization.Away.lift (TrivSqZeroExt.inl s) (isUnit_dAway s)

theorem fromL_comp : (fromL s).comp (algebraMap (DualNumber S) (Ld s)) = dAway s :=
  IsLocalization.lift_comp _

theorem fromL_toL : (fromL s).comp (toL s) = RingHom.id _ := by
  apply dAway_ext s
  rw [RingHom.comp_assoc, toL_comp, fromL_comp, RingHom.id_comp]

theorem toL_fromL : (toL s).comp (fromL s) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (TrivSqZeroExt.inl s : DualNumber S))
  rw [RingHom.comp_assoc, fromL_comp, toL_comp, RingHom.id_comp]

end Iso

section Glue

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem dualMapS_ofId_toRingHom (s : S) :
    (dualMapS (Algebra.ofId S (Localization.Away s)) : DualNumber S →+* DualNumber (Localization.Away s)) = dAway s := rfl

set_option backward.isDefEq.respectTransparency false in

theorem glue_tan {n : ℕ} (s : Fin n → S) (hs : Ideal.span (Set.range s) = ⊤)
    (w : ∀ k, sp (R₀ := S) (DualNumber (Localization.Away (s k))) ⟶ G) (hw : ∀ k, TanS (w k))
    (hc : ∀ k l (T : CommRingCat.{0}) (α : DualNumber (Localization.Away (s k)) →+* T)
      (β : DualNumber (Localization.Away (s l)) →+* T), α.comp (dAway (s k)) = β.comp (dAway (s l)) →
      Spec.map (CommRingCat.ofHom α) ≫ (w k).left = Spec.map (CommRingCat.ofHom β) ≫ (w l).left) :
    ∃ v : sp (R₀ := S) (DualNumber S) ⟶ G, TanS v ∧
      ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v = w k := by
  have hs' : Ideal.span (Set.range (fun k => (TrivSqZeroExt.inl (s k) : DualNumber S))) = ⊤ := by
    have := congrArg (Ideal.map (TrivSqZeroExt.inlHom S S)) hs
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
    exact this
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber S)) _ hs').openCover
  let f : ∀ k, 𝒰.X k ⟶ G.left := fun k => Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left
  have hf : ∀ k l, pullback.fst (𝒰.f k) (𝒰.f l) ≫ f k = pullback.snd (𝒰.f k) (𝒰.f l) ≫ f l := by
    refine fun (k : Fin n) (l : Fin n) => Scheme.Cover.hom_ext (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.openCover _ _
      fun (i : (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.I₀) => ?_
    let a : Spec ((pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i) ⟶ pullback (𝒰.f k) (𝒰.f l) :=
      (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.f i
    let A : CommRingCat.of (Ld (s k)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.fst (𝒰.f k) (𝒰.f l))
    let B : CommRingCat.of (Ld (s l)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.snd (𝒰.f k) (𝒰.f l))
    have ea : Spec.map A = a ≫ pullback.fst (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have eb : Spec.map B = a ≫ pullback.snd (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k))) ≫ A) =
        Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s l))) ≫ B) := by
      rw [Spec.map_comp, Spec.map_comp, ea, eb, Category.assoc, Category.assoc]
      exact congrArg (a ≫ ·) pullback.condition
    have key : A.hom.comp (algebraMap (DualNumber S) (Ld (s k))) = B.hom.comp (algebraMap (DualNumber S) (Ld (s l))) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    have hkey : (A.hom.comp (toL (s k))).comp (dAway (s k)) = (B.hom.comp (toL (s l))).comp (dAway (s l)) := by
      rw [RingHom.comp_assoc, RingHom.comp_assoc, toL_comp, toL_comp]
      exact key
    have h := hc k l _ (A.hom.comp (toL (s k))) (B.hom.comp (toL (s l))) hkey
    show a ≫ pullback.fst (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left =
      a ≫ pullback.snd (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (toL (s l))) ≫ (w l).left
    rw [← Category.assoc a, ← Category.assoc a, ← ea, ← eb, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp]
    exact h
  let g := 𝒰.glueMorphisms f hf
  have hι : ∀ k : Fin n, 𝒰.f k ≫ g = f k := fun k => Scheme.Cover.ι_glueMorphisms 𝒰 f hf k
  have hg : ∀ k : Fin n, Spec.map (CommRingCat.ofHom (dAway (s k))) ≫ g = (w k).left := by
    intro k
    have e : Spec.map (CommRingCat.ofHom (dAway (s k))) = Spec.map (CommRingCat.ofHom (fromL (s k))) ≫ 𝒰.f k := by
      show _ = _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k))))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fromL_comp]
    rw [e, Category.assoc, hι k]
    show Spec.map (CommRingCat.ofHom (fromL (s k))) ≫ Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left = _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fromL_toL, CommRingCat.ofHom_id, Spec.map_id,
      Category.id_comp]
  have hover : g ≫ G.hom = (sp (R₀ := S) (DualNumber S)).hom := by
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun (k : Fin n) => ?_
    rw [← Category.assoc, hι k]
    show (Spec.map (CommRingCat.ofHom (toL (s k))) ≫ (w k).left) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (DualNumber S) (Ld (s k)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (DualNumber S)))
    rw [Category.assoc, Over.w (w k)]
    show Spec.map (CommRingCat.ofHom (toL (s k))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S (DualNumber (Localization.Away (s k))))) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    rw [← toL_comp, RingHom.comp_assoc]
    congr 1
    refine RingHom.ext fun r => ?_
    simp [TrivSqZeroExt.algebraMap_eq_inl', dAway_inl]
  let v : sp (R₀ := S) (DualNumber S) ⟶ G := Over.homMk g hover
  have hres : ∀ k, spMap (dualMapS (Algebra.ofId S (Localization.Away (s k)))) ≫ v = w k := fun k =>
    Over.OverMorphism.ext (hg k)
  refine ⟨v, ?_, hres⟩
  apply Over.OverMorphism.ext
  let 𝒱 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) _ hs).openCover
  refine Scheme.Cover.hom_ext 𝒱 _ _ fun (k : Fin n) => ?_
  have e1 : Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫
        (spMap (TrivSqZeroExt.fstHom S S S)).left =
      (spMap (TrivSqZeroExt.fstHom S (Localization.Away (s k)) (Localization.Away (s k)))).left ≫
        (spMap (dualMapS (Algebra.ofId S (Localization.Away (s k))))).left := by
    rw [spMap_left, spMap_left, spMap_left, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => (dualMapS_fst (Algebra.ofId S (Localization.Away (s k))) x).symm
  have h1 := congrArg (fun q => Over.Hom.left q) (hw k)
  simp only [Over.comp_left] at h1
  show Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫
      ((spMap (TrivSqZeroExt.fstHom S S S)).left ≫ v.left) =
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫ (1 : sp (R₀ := S) S ⟶ G).left
  rw [← Category.assoc, e1, Category.assoc]
  have h2 : (spMap (dualMapS (Algebra.ofId S (Localization.Away (s k))))).left ≫ v.left = (w k).left :=
    congrArg (fun q => Over.Hom.left q) (hres k)
  rw [h2, h1, one_left', one_left']
  show (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k))))) ≫ _ =
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (s k)))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap S S)) ≫ _)
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Algebra.algebraMap_self, RingHom.comp_id]

end Glue

end ReciprocityTheory.ChartRestriction.G.Chart
