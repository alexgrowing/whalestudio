import Development.EtaleCohomology.EtaleSheaves.LeafMapFPPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafPairFPPf LateralTheory.E.LeafMapFPPf

namespace LateralTheory.E.LeafLimFPPf

theorem isLimit_pullback_finitelyGenerated : LeafLimFP := by
  intro k _ Ω _ _ R hR C1 D1 c1 q1 v1 hs _
  refine ⟨IsLimit.ofExistsUnique fun s => ?_⟩
  let o : GlobalTheory.FGAbove R := ⟨R, hR, le_rfl⟩
  let a : ∀ S : GlobalTheory.FGAbove R, s.pt ⟶ pullback q1 (incl S.2.2) := fun S => s.π.app (op S)
  have ha : ∀ (S T : GlobalTheory.FGAbove R) (h : S.1 ≤ T.1), a T ≫ dgMap q1 S.2.2 T.2.2 h = a S :=
    fun S T h => s.w (homOfLE (show S ≤ T from h)).op
  have hsnd : ∀ (S T : GlobalTheory.FGAbove R) (h : S.1 ≤ T.1),
      (a T ≫ pullback.snd _ _) ≫ incl h = a S ≫ pullback.snd _ _ := fun S T h => by
    rw [← ha S T h, Category.assoc, Category.assoc, dgMap_snd]
  obtain ⟨ψ, hψ⟩ := GlobalTheory.FGAbove.exists_ringHom hR
    (fun S => ((Scheme.ΓSpecIso (.of S.1)).inv ≫ (a S ≫ pullback.snd _ _).appTop).hom) (by
      intro S T h x
      rw [← hsnd S T h]
      exact (GlobalTheory.appTop_comp_spMap (Subalgebra.inclusion h).toRingHom _ x).symm)
  obtain ⟨b, hb⟩ : ∃ b : s.pt ⟶ Sp Ω, (Scheme.ΓSpecIso (.of Ω)).inv ≫ b.appTop = CommRingCat.ofHom ψ := by
    refine ⟨s.pt.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.toSpecΓ_appTop]
    simp
  have hb' : ∀ S : GlobalTheory.FGAbove R, b ≫ toR S.1 = a S ≫ pullback.snd _ _ := fun S =>
    GlobalTheory.hom_spec_ext (CommRingCat.hom_ext (RingHom.ext fun x => by
      refine (GlobalTheory.appTop_comp_spMap (algebraMap S.1 Ω) b x).trans ?_
      rw [hb]
      exact hψ S x))
  have hf : ∀ S : GlobalTheory.FGAbove R, a S ≫ pullback.fst _ _ = a o ≫ pullback.fst _ _ := fun S => by
    rw [← ha o S S.2.2, Category.assoc, dgMap_fst]
  have hw : (a o ≫ pullback.fst _ _) ≫ q1 = b ≫ toR R := by
    conv_rhs => rw [← toR_incl o.2.2]
    rw [← Category.assoc, hb' o, Category.assoc, Category.assoc, pullback.condition]
  refine ⟨hs.lift (a o ≫ pullback.fst _ _) b hw, fun S => ?_, fun m hm => ?_⟩
  · show _ ≫ pullback.lift v1 (c1 ≫ toR S.unop.1) _ = a S.unop
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hs.lift_fst, hf S.unop]
    · rw [Category.assoc, pullback.lift_snd, hs.lift_snd_assoc, hb']
  · change s.pt ⟶ C1 at m
    have hm' : ∀ S : GlobalTheory.FGAbove R, m ≫ pullback.lift v1 (c1 ≫ toR S.1)
        (by rw [Category.assoc, toR_incl, hs.w]) = a S := fun S => hm (op S)
    apply hs.hom_ext
    · rw [hs.lift_fst, ← hm' o, Category.assoc, pullback.lift_fst]
    · rw [hs.lift_snd]
      refine GlobalTheory.hom_spec_ext (CommRingCat.hom_ext (RingHom.ext fun x => ?_))
      obtain ⟨S, hx⟩ := GlobalTheory.FGAbove.exists_mem hR x
      have e : (m ≫ c1) ≫ toR S.1 = b ≫ toR S.1 := by
        rw [hb', ← hm' S, Category.assoc, Category.assoc, pullback.lift_snd]
      exact (GlobalTheory.appTop_comp_spMap (algebraMap S.1 Ω) _ ⟨x, hx⟩).symm.trans
        (e ▸ GlobalTheory.appTop_comp_spMap (algebraMap S.1 Ω) b ⟨x, hx⟩)

end LateralTheory.E.LeafLimFPPf

end
