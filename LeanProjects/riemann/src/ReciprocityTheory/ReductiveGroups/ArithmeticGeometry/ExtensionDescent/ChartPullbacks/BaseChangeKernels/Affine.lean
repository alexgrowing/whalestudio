import Mathlib

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

universe u

section Square

variable {G B G' B' : Scheme.{u}} {g : G' ⟶ G} {q' : G' ⟶ B'} {q : G ⟶ B} {b : B' ⟶ B}

theorem isPullback_resLE (sq : IsPullback g q' q b) (V : B.Opens) (V' : B'.Opens)
    (hle : V' ≤ b ⁻¹ᵁ V) (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V)) :
    IsPullback (g.resLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG) (q'.resLE V' (q' ⁻¹ᵁ V') le_rfl)
      (q.resLE V (q ⁻¹ᵁ V) le_rfl) (b.resLE V V' hle) := by
  have outer : IsPullback ((q' ⁻¹ᵁ V').ι ≫ g) (q' ∣_ V') q (V'.ι ≫ b) :=
    (isPullback_morphismRestrict q' V').flip.paste_horiz sq
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_eq_morphismRestrict]
  refine IsPullback.of_right (h₁₂ := (q ⁻¹ᵁ V).ι) (h₂₂ := V.ι) (v₁₃ := q) ?_ ?_
    (isPullback_morphismRestrict q V).flip
  · rw [Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι]
    exact outer
  · rw [← cancel_mono V.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, sq.w, ← Category.assoc,
      ← morphismRestrict_ι, Category.assoc]

theorem isPushout_appLE (sq : IsPullback g q' q b) (hq : IsAffineHom q) {V : B.Opens}
    (hV : IsAffineOpen V) {V' : B'.Opens} (hV' : IsAffineOpen V')
    (hle : V' ≤ b ⁻¹ᵁ V) (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V)) :
    IsPushout (q.app V) (b.appLE V V' hle) (g.appLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG) (q'.app V') := by
  have : IsAffine V.toScheme := hV
  have : IsAffine V'.toScheme := hV'
  have : IsAffine (q ⁻¹ᵁ V).toScheme := hV.preimage q
  have P := isPushout_appTop_of_isPullback (isPullback_resLE sq V V' hle hleG)
  rw [← Scheme.Hom.appLE_eq_app, ← Scheme.Hom.appLE_eq_app]
  refine P.of_iso V.topIso (q ⁻¹ᵁ V).topIso V'.topIso (q' ⁻¹ᵁ V').topIso ?_ ?_ ?_ ?_ <;>
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]

end Square

section Algebra

variable {R A R' A' : CommRingCat.{u}} {qa : R ⟶ A} {ba : R ⟶ R'} {ga : A ⟶ A'} {qa' : R' ⟶ A'}
  {X : Type u} [AddCommMonoid X]

theorem bijective_liftNC_of_isPushout (hP : IsPushout qa ba ga qa')
    (φ : Multiplicative X →* A) (φ' : Multiplicative X →* A') (hφ' : ∀ x, φ' x = ga (φ x))
    (hφ : Function.Bijective (AddMonoidAlgebra.liftNCRingHom qa.hom φ (fun _ _ => Commute.all _ _))) :
    Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom qa'.hom φ' (fun _ _ => Commute.all _ _)) := by
  classical
  let F : AddMonoidAlgebra R' X →+* A' := AddMonoidAlgebra.liftNCRingHom qa'.hom φ' (fun _ _ => Commute.all _ _)
  let e : AddMonoidAlgebra R X ≃+* A := RingEquiv.ofBijective _ hφ
  let Mp : AddMonoidAlgebra R X →+* AddMonoidAlgebra R' X := AddMonoidAlgebra.mapRingHom X ba.hom
  have he : ∀ (x : X) (r : R), e (AddMonoidAlgebra.single x r) = qa.hom r * φ (Multiplicative.ofAdd x) := by
    intro x r
    simp [e, AddMonoidAlgebra.liftNC_single]
  have hF : ∀ (x : X) (r : R'), F (AddMonoidAlgebra.single x r) = qa'.hom r * φ' (Multiplicative.ofAdd x) := by
    intro x r
    simp [F, AddMonoidAlgebra.liftNC_single]
  have hM : ∀ (x : X) (r : R), Mp (AddMonoidAlgebra.single x r) = AddMonoidAlgebra.single x (ba.hom r) := by
    intro x r
    simp [Mp]
  have hw : ∀ r : R, ga.hom (qa.hom r) = qa'.hom (ba.hom r) := fun r => congrArg (fun f => f.hom r) hP.w
  have hes0 : ∀ r : R, e.symm (qa.hom r) = AddMonoidAlgebra.single 0 r := by
    intro r
    rw [RingEquiv.symm_apply_eq, he]
    simp
  have hes1 : ∀ x : X, e.symm (φ (Multiplicative.ofAdd x)) = AddMonoidAlgebra.single x 1 := by
    intro x
    rw [RingEquiv.symm_apply_eq, he]
    simp
  let u : A ⟶ CommRingCat.of (AddMonoidAlgebra R' X) := CommRingCat.ofHom (Mp.comp (e.symm : A →+* AddMonoidAlgebra R X))
  let v : R' ⟶ CommRingCat.of (AddMonoidAlgebra R' X) := CommRingCat.ofHom (algebraMap R' (AddMonoidAlgebra R' X))
  have hcond : qa ≫ u = ba ≫ v := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    show Mp (e.symm (qa.hom r)) = algebraMap R' (AddMonoidAlgebra R' X) (ba.hom r)
    rw [hes0, hM]
    rfl
  let G := hP.desc u v hcond
  have hG1 : ∀ a : A, G.hom (ga.hom a) = Mp (e.symm a) := fun a => congrArg (fun f => f.hom a) (hP.inl_desc u v hcond)
  have hG2 : ∀ r : R', G.hom (qa'.hom r) = AddMonoidAlgebra.single 0 r := fun r => congrArg (fun f => f.hom r) (hP.inr_desc u v hcond)
  have hleft : (G.hom).comp F = RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      rw [RingHom.comp_apply, hF]
      simp [hG2]
    · intro x
      rw [RingHom.comp_apply, hF, map_one, one_mul, hφ', hG1, hes1, hM, map_one]
      rfl
  have hright : ∀ a : A', F (G.hom a) = a := by
    have h3 : G ≫ CommRingCat.ofHom F = 𝟙 A' := by
      apply hP.hom_ext
      · ext a
        show F (G.hom (ga.hom a)) = ga.hom a
        rw [hG1]
        obtain ⟨p, rfl⟩ := e.surjective a
        rw [RingEquiv.symm_apply_apply]
        have h4 : F.comp Mp = ga.hom.comp (e : AddMonoidAlgebra R X →+* A) := by
          apply AddMonoidAlgebra.ringHom_ext
          · intro r
            rw [RingHom.comp_apply, RingHom.comp_apply, hM, hF]
            simp [he, hw]
          · intro x
            rw [RingHom.comp_apply, RingHom.comp_apply, hM, hF, map_one, map_one, one_mul, hφ']
            simp [he]
        exact congrArg (fun f => f p) h4
      · ext r
        show F (G.hom (qa'.hom r)) = qa'.hom r
        rw [hG2, hF]
        simp
    intro a
    exact congrArg (fun f => f.hom a) h3
  exact Function.bijective_iff_has_inverse.mpr ⟨G.hom, fun p => congrArg (fun f => f p) hleft, hright⟩

end Algebra

theorem coord_affineBC {G B G' B' : Scheme.{u}} {g : G' ⟶ G} {q' : G' ⟶ B'} {q : G ⟶ B}
    {b : B' ⟶ B}
    (sq : IsPullback g q' q b) (hq : IsAffineHom q) {X : Type u} [AddCommMonoid X]
    {V : B.Opens} (hV : IsAffineOpen V) {V' : B'.Opens} (hV' : IsAffineOpen V')
    (hle : V' ≤ b ⁻¹ᵁ V) (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V))
    (φ : Multiplicative X →* Γ(G, q ⁻¹ᵁ V)) (φ' : Multiplicative X →* Γ(G', q' ⁻¹ᵁ V'))
    (hφ' : ∀ x, φ' x = g.appLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG (φ x))
    (hφ : Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom (q.app V).hom φ (fun _ _ => Commute.all _ _))) :
    Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom (q'.app V').hom φ' (fun _ _ => Commute.all _ _)) := bijective_liftNC_of_isPushout (isPushout_appLE sq hq hV hV' hle hleG) φ φ' hφ' hφ

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
