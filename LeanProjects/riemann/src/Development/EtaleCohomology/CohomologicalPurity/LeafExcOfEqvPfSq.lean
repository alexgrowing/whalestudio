import Development.EtaleCohomology.CohomologicalPurity.LeafExcOfEqvPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut
variable {P' P : Arrow Spc} (φ : P' ⟶ P)

theorem etale_double_inl_sigma_inl_eq_inl : dbl.inl (QQ φ) ≫ sig φ ≫ dbl.inl (QQ φ) = dbl.inl (QQ φ) :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ dbl.inl (QQ φ)) (inl_sig φ)).trans (Category.id_comp _))

theorem etale_double_inr_sigma_inl_eq_retraction_jj_inr : dbl.inr (QQ φ) ≫ sig φ ≫ dbl.inl (QQ φ) = (rr φ ≫ jj φ) ≫ dbl.inr (QQ φ) :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ dbl.inl (QQ φ)) (inr_sig φ)).trans
    ((Category.assoc (rr φ) (jj φ) (dbl.inl (QQ φ))).trans ((congrArg (rr φ ≫ ·) (jj_inl φ)).trans
      (Category.assoc (rr φ) (jj φ) (dbl.inr (QQ φ))).symm)))

theorem fix_key (q : ℕ) :
    (chains (ZMod q)).map (sig φ ≫ dbl.inl (QQ φ)) ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))) =
      cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))) := by
  have h := (chains (ZMod q)).map_isPushout (IsPushout.of_hasPushout (QQ φ).hom (QQ φ).hom)
  apply h.hom_ext
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))))
      ((chains (ZMod q)).map_comp (dbl.inl (QQ φ)) (sig φ ≫ dbl.inl (QQ φ))).symm).trans
      (congrArg (fun f => (chains (ZMod q)).map f ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ)))) (etale_double_inl_sigma_inl_eq_inl φ)))
  · have c0 : (chains (ZMod q)).map (dbl.inr (QQ φ)) ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))) = 0 :=
      cokernel.condition _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ))))
      ((chains (ZMod q)).map_comp (dbl.inr (QQ φ)) (sig φ ≫ dbl.inl (QQ φ))).symm).trans
      ((congrArg (fun f => (chains (ZMod q)).map f ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ)))) (etale_double_inr_sigma_inl_eq_retraction_jj_inr φ)).trans
      ((congrArg (· ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ)))) ((chains (ZMod q)).map_comp (rr φ ≫ jj φ) (dbl.inr (QQ φ)))).trans
      ((Category.assoc _ _ _).trans ((congrArg ((chains (ZMod q)).map (rr φ ≫ jj φ) ≫ ·) c0).trans
      (Limits.comp_zero.trans c0.symm))))))

theorem LeafFix_of : LeafFix := by
  intro q n i P' P φ z hz
  have hr := (LateralTheory.CohomologicalPurity.eEquiv q n i (QQ φ)).right_inv ⟨z, hz⟩
  have hz1 : HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr (QQ φ)))) (tw q i) n
      (HK.pull (ZMod q) (LateralTheory.CohomologicalPurity.secC q (QQ φ)) (tw q i) n z) = z := congrArg Subtype.val hr
  change HK.pull (ZMod q) ((chains (ZMod q)).map (sig φ ≫ dbl.inl (QQ φ))) (tw q i) n z = z
  conv_lhs => rw [← hz1]
  rw [← LateralTheory.CohomologicalPurity.HK.pull_comp', fix_key, hz1]

end LateralTheory.CohomologicalPurity.TubeCut

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafChiSq : Prop := ∀ {P' P : Arrow Spc} (φ : P' ⟶ P),
  IsPushout (dbl.inr P') (chi φ).right (dbl.map (chi φ)) (dbl.inr (QQ φ))

def LeafCokPush : Prop := ∀ (q : ℕ) {A B C D : Cx (ZMod q)} (f : A ⟶ B) (g : A ⟶ C) (a : B ⟶ D) (b : C ⟶ D)
  (h : IsPushout f g a b), IsIso (cokernel.map f b g a h.w)

theorem LeafCokPush_of : LeafCokPush := by
  intro q A B C D f g a b h
  refine ⟨⟨cokernel.desc b (h.desc (cokernel.π f) 0 (by simp)) (by simp), ?_, ?_⟩⟩
  · refine coequalizer.hom_ext ?_
    simp
  · refine coequalizer.hom_ext ?_
    simp only [cokernel.π_desc_assoc, Category.comp_id]
    apply h.hom_ext <;> simp

theorem LeafChiExc_of (hS : LeafChiSq) : LeafChiExc := by
  intro q P' P φ
  exact LateralTheory.CohomologicalPurity.LeafExcCx_of LateralTheory.CohomologicalPurity.EtaleExcIdent q (chi φ)
    (LeafCokPush_of q _ _ _ _ ((chains (ZMod q)).map_isPushout (hS φ)))

theorem LeafExcOfEqv_of_sq (hS : LeafChiSq) : LeafExcOfEqv := LeafExcOfEqv_of LeafFix_of (LeafChiExc_of hS)

end LateralTheory.CohomologicalPurity.TubeCut
