import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ThetaInvolution

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem entIn_sub_iff {C : Type} [CommRing C] (I : Ideal C) (X Y : Matrix (Fin 3) (Fin 3) C) :
    EntIn I (X - Y) ↔ X.map (Ideal.Quotient.mk I) = Y.map (Ideal.Quotient.mk I) := by
  constructor
  · intro h
    ext a b
    exact Ideal.Quotient.eq.2 (h a b)
  · intro h a b
    exact Ideal.Quotient.eq.1 (congrFun (congrFun h a) b)

private theorem congOne_iff {C : Type} [CommRing C] (I : Ideal C) (h : GL (Fin 3) C) :
    CongOne I h ↔ GeneralLinearGroup.map (Ideal.Quotient.mk I) h = 1 := by
  unfold CongOne
  rw [entIn_sub_iff, Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro e
    exact Units.ext e
  · intro e
    exact congrArg Units.val e

private theorem conjBy_app {C D : Type} [CommRing C] [Group D] (h : GL (Fin 3) C) (r : D →* GG 3 C) (g : D) :
    conjBy h r g = GG.ofGL h * r g * (GG.ofGL h)⁻¹ := rfl

private theorem conjBy_comp {C D E : Type} [CommRing C] [Group D] [Group E] (h : GL (Fin 3) C) (r : D →* GG 3 C)
    (f : E →* D) : (conjBy h r).comp f = conjBy h (r.comp f) := rfl

private theorem conjBy_conjBy {C D : Type} [CommRing C] [Group D] (h h' : GL (Fin 3) C) (r : D →* GG 3 C) :
    conjBy (h * h')⁻¹ (conjBy h r) = conjBy h'⁻¹ r :=
  _root_.UpperTheory.Reformulated.B.ThetaInvolution.conjBy_conjBy h h' r

private theorem map_conjBy {C D : Type} [CommRing C] [Group D] (I : Ideal C) (h : GL (Fin 3) C)
    (hh : CongOne I h) (r : D →* GG 3 C) (g : D) :
    GG.map (Ideal.Quotient.mk I) (conjBy h r g) = GG.map (Ideal.Quotient.mk I) (r g) := by
  have e : GG.map (Ideal.Quotient.mk I) (GG.ofGL h) = 1 := by
    unfold GG.map
    rw [SemidirectProduct.map_inl, (congOne_iff I h).1 hh, map_one]
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e,
    one_mul, inv_one, mul_one]

theorem UpperTheory.V.UnitaryThreeInertia.cond_conj :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] (F : Frame O G Γ ι) {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R] (h : GL (Fin 3) R), InHat h →
      (∀ v (r : F.D v →* GG 3 R), F.LocAt v r → F.LocAt v (conjBy h r)) ∧ ∀ r : Γ →* GG 3 R, F.Cond r → F.Cond (conjBy h r) := by
  intro O _ _ G Γ ι _ _ F R _ _ _ h hh
  have hmul : ∀ h' : GL (Fin 3) R, InHat h' → InHat (h * h') := fun h' hh' => by
    refine (congOne_iff _ _).2 ?_
    rw [map_mul, (congOne_iff _ _).1 hh, (congOne_iff _ _).1 hh', mul_one]
  have hloc : ∀ v (r : F.D v →* GG 3 R), F.LocAt v r → F.LocAt v (conjBy h r) := by
    intro v r ⟨ht, hd, hu⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e s hs => ?_⟩
    · obtain ⟨h', h1, h2, h3⟩ := ht e
      refine ⟨h * h', hmul h' h1, ?_, ?_⟩
      · rw [conjBy_conjBy]; exact h2
      · rw [conjBy_conjBy]; exact h3
    · obtain ⟨h', h1, ⟨h2, h3⟩, h4⟩ := hd e
      refine ⟨h * h', hmul h' h1, ⟨?_, ?_⟩, ?_⟩
      · rw [conjBy_conjBy]; exact h2
      · rw [conjBy_conjBy]; exact h3
      · rw [conjBy_conjBy]; exact h4
    · rw [conjBy_app, hu e s hs, mul_one, mul_inv_cancel]
  refine ⟨hloc, fun r hr => ⟨⟨fun g => ?_, fun g => ?_⟩, fun v => ?_⟩⟩
  · have e := congrArg SemidirectProduct.right (map_conjBy _ h hh r g)
    rw [GG.map_right, GG.map_right] at e
    exact e.trans (hr.mult g)
  · have e := congrArg GG.mat (map_conjBy _ h hh r g)
    rw [GG.map_mat, GG.map_mat] at e
    rw [entIn_sub_iff, e, ← entIn_sub_iff]
    exact hr.red g
  · rw [conjBy_comp]
    exact hloc v _ (hr.loc v)
