import Development.EtaleCohomology.KummerTheory.ContCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.KummerTheory.AffRingPf

variable {X : Scheme.{0}} [IsAffine X] {R : CommRingCat.{0}} (p : X ⟶ Spec R)

def phi : R ⟶ Γ(X, ⊤) := Spec.preimage (X.isoSpec.inv ≫ p)

def Tf : Under R ⥤ CommRingCat.{0} := Under.pushout (phi p) ⋙ Under.forget _

theorem isPb (A : Under R) :
    IsPullback (Spec.map (pushout.inr A.hom (phi p)) ≫ X.isoSpec.inv) (Spec.map (pushout.inl A.hom (phi p)))
      p (Spec.map A.hom) := by
  have h := (isPullback_SpecMap_pushout A.hom (phi p)).flip
  refine IsPullback.of_iso h (Iso.refl _) X.isoSpec.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp [phi]
  · simp

def eIso (A : Under R) : Spec (pushout A.hom (phi p)) ≅ pullback p (Spec.map A.hom) := (isPb p A).isoPullback

theorem eIso_fst (A : Under R) : (eIso p A).hom ≫ pullback.fst _ _ =
    Spec.map (pushout.inr A.hom (phi p)) ≫ X.isoSpec.inv :=
  (isPb p A).isoPullback_hom_fst

theorem eIso_snd (A : Under R) : (eIso p A).hom ≫ pullback.snd _ _ =
    Spec.map (pushout.inl A.hom (phi p)) :=
  (isPb p A).isoPullback_hom_snd

def tmap {A B : Under R} (h : A ⟶ B) : pushout A.hom (phi p) ⟶ pushout B.hom (phi p) :=
  pushout.desc (h.right ≫ pushout.inl B.hom (phi p)) (pushout.inr B.hom (phi p))
    (by rw [← Category.assoc, Under.w h, pushout.condition])

theorem nat {A B : Under R} (h : A ⟶ B) :
    (eIso p B).hom ≫ bcMap p A.hom B.hom h.right (Under.w h) = Spec.map (tmap p h) ≫ (eIso p A).hom := by
  have e1 : pushout.inr A.hom (phi p) ≫ tmap p h = pushout.inr B.hom (phi p) := pushout.inr_desc _ _ _
  have e2 : pushout.inl A.hom (phi p) ≫ tmap p h = h.right ≫ pushout.inl B.hom (phi p) := pushout.inl_desc _ _ _
  apply pullback.hom_ext
  · simp only [bcMap, pullback.map, Category.assoc, pullback.lift_fst, Category.comp_id, eIso_fst]
    rw [← e1, Spec.map_comp, Category.assoc]
  · simp only [bcMap, pullback.map, Category.assoc, pullback.lift_snd, eIso_snd]
    rw [← Category.assoc, eIso_snd, ← Spec.map_comp, ← e2, Spec.map_comp]

theorem AffRing_of : LateralTheory.KummerTheory.ContCut.AffRing := by
  intro X _ R p
  refine ⟨Tf p, ⟨NatIso.ofComponents (fun A => (eIso p A).op) ?_⟩, fun A => ⟨A.hom ≫ pushout.inl A.hom (phi p)⟩, ?_⟩
  · intro A B h
    exact Quiver.Hom.unop_inj (nat p h)
  · intro J _ _ D c hc
    have : IsConnected J := IsFiltered.isConnected J
    have hc' : IsColimit c := isColimitOfReflects (Under.forget R) hc
    let _ : PreservesColimitsOfSize.{0, 0} (Under.pushout (phi p)) :=
      (Under.mapPushoutAdj (phi p)).leftAdjoint_preservesColimits
    have : PreservesColimit D (Tf p) :=
      inferInstanceAs (PreservesColimit D (Under.pushout (phi p) ⋙ Under.forget _))
    exact ⟨isColimitOfPreserves (Tf p) hc'⟩

end LateralTheory.KummerTheory.AffRingPf
