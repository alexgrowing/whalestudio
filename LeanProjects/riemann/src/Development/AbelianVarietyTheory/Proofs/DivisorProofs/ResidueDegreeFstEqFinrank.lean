import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoEmbeddingsOfTranscendental
open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.FieldTensorDegree

theorem residueDegree_fst_eq_finrank {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S)
    (t : ↑(Limits.pullback f g)) (hF : IsField (Scheme.Pullback.Triplet.ofPoint t).tensor) :
    (Limits.pullback.fst f g).residueDegree t =
      @Module.finrank (X.residueField (Scheme.Pullback.Triplet.ofPoint t).x)
        (Scheme.Pullback.Triplet.ofPoint t).tensor _ _
        (Scheme.Pullback.Triplet.ofPoint t).tensorInl.hom.toModule := by
  set T := Scheme.Pullback.Triplet.ofPoint t with hT
  letI : Field T.tensor := hF.toField
  have e1 : (pullback.fst f g).residueFieldMap t = T.tensorInl ≫ Scheme.Pullback.ofPointTensor t := by
    exact (pushout.inl_desc _ _ (Scheme.Pullback.residueFieldCongr_inv_residueFieldMap_ofPoint t)).symm
  have h1 : (pullback.fst f g).residueDegree t =
      ProjDrop.deg T.tensorInl.hom * ProjDrop.deg (Scheme.Pullback.ofPointTensor t).hom := by
    rw [← ProjDrop.deg_comp]
    show ProjDrop.deg ((pullback.fst f g).residueFieldMap t).hom = _
    rw [e1]; rfl
  let m : Spec (CommRingCat.of T.tensor) ⟶ pullback f g := T.SpecTensorTo
  let P := Scheme.SpecToEquivOfField T.tensor (pullback f g) m
  have hm : Spec.map P.2 ≫ (pullback f g).fromSpecResidueField P.1 = m :=
    (Scheme.SpecToEquivOfField T.tensor (pullback f g)).symm_apply_apply m
  have h : (Spec.map P.2 ≫ (pullback f g).fromSpecResidueField P.1) ≫ pullback.fst f g =
      Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x := by
    rw [hm]; exact T.specTensorTo_fst
  obtain ⟨-, h2⟩ := ProjDrop.deg_eq_of_fieldPoint (pullback.fst f g) P.1 T.x P.2 T.tensorInl h
  have hP : P.1 = t := by
    have : P.1 = m (IsLocalRing.closedPoint T.tensor) := rfl
    rw [this, Subsingleton.elim (IsLocalRing.closedPoint T.tensor) (Scheme.Pullback.SpecOfPoint t)]
    exact Scheme.Pullback.SpecTensorTo_SpecOfPoint t
  rw [show (pullback.fst f g).residueDegree P.1 = (pullback.fst f g).residueDegree t from
    congrArg _ hP] at h2
  show _ = ProjDrop.deg T.tensorInl.hom
  rw [h1] at h2 ⊢
  rcases Nat.eq_zero_or_pos (ProjDrop.deg T.tensorInl.hom) with h0 | hpos
  · rw [h0, zero_mul]
  · rw [mul_assoc] at h2
    have hbc : ProjDrop.deg (Scheme.Pullback.ofPointTensor t).hom * ProjDrop.deg P.2.hom = 1 :=
      (Nat.mul_eq_left hpos.ne').mp h2.symm
    rw [Nat.eq_one_of_mul_eq_one_right hbc, mul_one]

end GlobalTheory.FieldTensorDegree
