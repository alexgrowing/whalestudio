import Development.EtaleCohomology.EtaleSheaves.LeafExcRingPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
namespace LateralTheory.E.LeafExcRingPf2
open LateralTheory.E.t_E6Cut LateralTheory.E.LeafExcRingPf

theorem schPb {X Y : Scheme.{0}} (g : Y ⟶ X) (U : X.Opens) :
    IsPullback (sch.map (g ∣_ U)) (sch.map (g ⁻¹ᵁ U).ι) (sch.map U.ι) (sch.map g) := by
  haveI : PreservesLimit (cospan U.ι g) (yoneda ⋙ SimplicialObject.const PSh) := inferInstance
  exact (isPullback_morphismRestrict g U).map (yoneda ⋙ SimplicialObject.const PSh)

theorem conn_iso (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {P Q E : Spc} (e : P ≅ Q) (p : P ⟶ E) (q : Q ⟶ E)
    (h : e.hom ≫ q = p) : Conn R F c p ↔ Conn R F c q := by
  have hb : ∀ n, Function.Bijective (pull R e.hom F n) := fun n => by
    refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
    · rw [← pull_comp, e.inv_hom_id, pull_id]
    · rw [← pull_comp, e.hom_inv_id, pull_id]
  have hp : ∀ n x, pull R p F n x = pull R e.hom F n (pull R q F n x) := fun n x => by rw [← h, pull_comp]
  unfold Conn ConnK
  refine forall_congr' fun n => and_congr (imp_congr_right fun _ => ?_) (imp_congr_right fun _ => ?_)
  · change Function.Bijective (pull R p F n) ↔ Function.Bijective (pull R q F n)
    rw [show (pull R p F n : _ → _) = pull R e.hom F n ∘ pull R q F n from funext (hp n)]
    exact ⟨fun hh => (Function.Bijective.of_comp_iff' (hb n) _).1 hh, fun hh => (hb n).comp hh⟩
  · change Function.Injective (pull R p F n) ↔ Function.Injective (pull R q F n)
    rw [show (pull R p F n : _ → _) = pull R e.hom F n ∘ pull R q F n from funext (hp n)]
    exact ⟨fun hh => (Function.Injective.of_comp_iff (hb n).1 _).1 hh, fun hh => (hb n).1.comp hh⟩

theorem leafPb : LeafPb := by
  intro R _ F c X Y g U
  exact (conn_iso R F c (schPb g U).isoPullback _ _ (schPb g U).isoPullback_hom_snd).symm

theorem LeafExcRing_of' (hE : LeafExc) (hC1 : LeafCov1) (hC2 : LeafCov2) : LeafExcRing :=
  LeafExcRing_of hE hC1 hC2 leafPb
end LateralTheory.E.LeafExcRingPf2
