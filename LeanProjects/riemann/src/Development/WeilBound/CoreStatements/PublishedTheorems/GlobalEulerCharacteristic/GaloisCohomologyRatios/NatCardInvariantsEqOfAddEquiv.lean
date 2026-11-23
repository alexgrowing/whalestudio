import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.IsDiscreteRepIntRep

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.GEN.X

attribute [local instance 2000] Rep.hV2

theorem natCard_invariants_eq_of_addEquiv {k k' H V W : Type*} [CommRing k] [CommRing k'] [Group H]
    [AddCommGroup V] {_mV : Module k V} [AddCommGroup W] {_mW : Module k' W}
    (ρ : Representation k H V) (σ : Representation k' H W) (e : V ≃+ W)
    (he : ∀ (h : H) (v : V), e (ρ h v) = σ h (e v)) :
    Nat.card ρ.invariants = Nat.card σ.invariants := by
  refine Nat.card_congr (e.toEquiv.subtypeEquiv fun v => ?_)
  simp only [Representation.mem_invariants, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  constructor
  · intro hv h
    rw [← he, hv]
  · intro hv h
    apply e.injective
    rw [he, hv]

variable {G : Type} [Group G] {ℓ : ℕ}

theorem uliftInt_smul {X : Type*} [AddCommGroup X] [Module (ULift.{0} ℤ) X] (r : ℤ) (x : X) :
    (Module.toDistribMulAction.toDistribSMul.toSMul : SMul (ULift.{0} ℤ) X).smul ⟨r⟩ x = r • x := by
  have h : ((r : ULift.{0} ℤ)) = ⟨r⟩ := by ext; simp
  have := Int.cast_smul_eq_zsmul (ULift.{0} ℤ) r x
  rw [h] at this
  exact this

theorem zmod_smul_eq {X : Type*} [AddCommGroup X] [Module (ZMod ℓ) X] (n : ℤ) (x : X) :
    ((n : ZMod ℓ)) • x = n • x := Int.cast_smul_eq_zsmul _ _ _

noncomputable def toZLin (D : Rep.{0} (ULift.{0} ℤ) G) (hD : ∀ d : D, ℓ • d = 0) (M : Rep.{0} (ZMod ℓ) G)
    (f : intRep M →ₗ[ULift.{0} ℤ] D) : M →ₗ[ZMod ℓ] (zmodRepOfTorsion ℓ D hD) where
  toFun m := f m
  map_add' a b := map_add f a b
  map_smul' r m := by
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective r
    rw [RingHom.id_apply]
    exact (congrArg f (zmod_smul_eq n m)).trans ((map_zsmul f.toAddMonoidHom n m).trans
      (zmod_smul_eq (X := zmodRepOfTorsion ℓ D hD) n (f m)).symm)

noncomputable def ofZLin (D : Rep.{0} (ULift.{0} ℤ) G) (hD : ∀ d : D, ℓ • d = 0) (M : Rep.{0} (ZMod ℓ) G)
    (g : M →ₗ[ZMod ℓ] (zmodRepOfTorsion ℓ D hD)) : intRep M →ₗ[ULift.{0} ℤ] D where
  toFun m := g m
  map_add' a b := map_add g a b
  map_smul' r m := by
    obtain ⟨r⟩ := r
    rw [RingHom.id_apply]
    exact (congrArg g (uliftInt_smul (X := intRep M) r m)).trans ((map_zsmul g.toAddMonoidHom r m).trans
      (uliftInt_smul (X := D) r (g m)).symm)

noncomputable def dualIntEquiv (D : Rep.{0} (ULift.{0} ℤ) G) (hD : ∀ d : D, ℓ • d = 0)
    (M : Rep.{0} (ZMod ℓ) G) :
    dualRep D (intRep M) ≃+ dualRep (zmodRepOfTorsion ℓ D hD) M where
  toFun f := toZLin D hD M f
  invFun g := ofZLin D hD M g
  left_inv f := rfl
  right_inv g := rfl
  map_add' f g := rfl

theorem dualIntEquiv_comm (D : Rep.{0} (ULift.{0} ℤ) G) (hD : ∀ d : D, ℓ • d = 0)
    (M : Rep.{0} (ZMod ℓ) G) (g : G) (f : dualRep D (intRep M)) :
    dualIntEquiv D hD M ((dualRep D (intRep M)).ρ g f) =
      (dualRep (zmodRepOfTorsion ℓ D hD) M).ρ g (dualIntEquiv D hD M f) := rfl

end PositivityTheory.Lit1.GEN.X
