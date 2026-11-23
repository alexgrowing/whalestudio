import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatTorsionIsomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

theorem exists_gen_of_eq {X Y : Scheme.{0}} (L : LB X) {p q : Y ⟶ X} (h : q = p) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) :
    ∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => q) (fun _ => n)),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : PUnit → L.ι),
        gm r z (LB.wchart L (fun _ => q) j) (b.s j) = gm r z (LB.wchart L (fun _ => p) j) (a.s j)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val b r z J = val a r z J := by
  subst h
  exact ⟨a, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem exists_mapsAt_id {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X) (p : Y ⟶ X) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) (ha : a.IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p ≫ F) (fun _ => n)),
      GeneratorPullback.MapsAt L L (J := PUnit) (fun _ => F) (isoPullId (idIso L) hF) p n a b ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val b r z J = val a r z J := by
  obtain ⟨b, hb, hv⟩ := exists_gen_of_eq L (q := p ≫ F) (p := p) (by rw [hF, Category.comp_id]) n a
  refine ⟨b, fun jN jL => unit_ext fun y hy => ?_, hv⟩
  have hL : p y ∈ L.U jL := hy.2
  have hN : p y ∈ L.U (jN PUnit.unit) := by
    have := mem_pull.1 hy.1
    rw [hF] at this
    exact this
  have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : PUnit => p) jN := Set.mem_iInter.2 fun _ => hN
  have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : PUnit => p) (fun _ => jL) := Set.mem_iInter.2 fun _ => hL
  refine (gm_res _ y _ hy _).trans ((hb _ _ y jN).trans ((gen_trans ha (𝟙 Y) y m₁ m₂).trans ?_))
  refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (gm_res _ y _ hy _)))
  rw [trF, Fintype.prod_unique]
  refine congrArg (· ^ n) ((gm_pull (𝟙 Y) p y _ hy _).trans ?_)
  exact gw_isoPullId (idIso L) hF (𝟙 Y ≫ p) y (jN PUnit.unit) jL hN hL

theorem exists_isIdPull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens), genericPoint (Sp R) ∈ W → Nonempty (PsiOn D W) → ∃ hD : IsPullDeg (RingHom.id R) D D, IsIdPull hD := by
  rintro R _ _ D W hW ⟨ψ⟩
  have hs := specOf_id R
  have mR : IsMonHom (Iso.refl D.P.A).hom := by show IsMonHom (𝟙 _); infer_instance
  have gp : IsGrpPullback D.P.A D.P.A (specOf (RingHom.id R)) (Iso.refl D.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.P.A)).congr hs.symm rfl
  obtain ⟨e, me, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf (RingHom.id R)))
  have hF : e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := he
  have hz : eSec D.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec D.P.A := by
    rw [hF, hs, Category.comp_id]; exact (Category.id_comp _).symm
  have hgen : ∀ z : Sp (FractionRing R), jK R z ∈ W := by
    intro z
    have : jK R z = genericPoint (Sp R) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap R (FractionRing R)) z.asIdeal = ⊥
      have hz0 : z.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ z.isPrime
      rw [hz0]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)
    rw [this]; exact hW
  have hr : Set.range (𝟙 (Sp (FractionRing R)) : _ ⟶ _) ⊆ Set.range (jK R ⁻¹ᵁ W).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hgen z
  let l := IsOpenImmersion.lift (jK R ⁻¹ᵁ W).ι (𝟙 _) hr
  have hl : l ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨{ e := e, e_hom := me, w := isoPullId (idIso D.P.L) hF
            w_gen := (isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.P.isLB) hF)
            he := hz
            w_rig := isoPullId_maps (idIso_maps (⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ : RigLB D.P.A)) hF hs hz
            xe := AddEquiv.refl _
            c_pr := fun x => by rw [hF, hs, Category.comp_id]; exact (Category.id_comp _).symm
            W := W, psiW := ψ, g := l ≫ jK R ∣_ W
            g_comm := by
              rw [hs, Category.comp_id]
              exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) (morphismRestrict_ι (jK R) W)).trans
                ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hl).trans (Category.id_comp _))))
            psi_pr := fun x => ?_ }, fun _ => rfl, hF, fun Y f y j k hj hk => ?_⟩
  · obtain ⟨b, hb, hv⟩ := exists_mapsAt_id hF (D.xK x) (-1) (D.psi x) (D.psi_gen x)
    refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => ?_⟩
    have c := val_corr hJ (ψ.psi_eq x) l
    have c₁ := val_pull hJ (ψ.psi x) (jK R ∣_ W) l
    have c₂ := val_pull hJ (D.psi x) (jK R ⁻¹ᵁ W).ι l
    have c₃ := val_pull hJ (ψ.psi x) (l ≫ jK R ∣_ W) (𝟙 _)
    refine (hv _ _ y J).trans (Eq.trans ?_ c₃.symm)
    refine (congrArg (fun r => val (D.psi x) r y J) hl).symm.trans (c₂.symm.trans (c.symm.trans (c₁.trans ?_)))
    exact congrArg (fun r => val (ψ.psi x) r y J) (Category.id_comp _).symm
  · exact gw_isoPullId (idIso D.P.L) hF f y j k hj hk

end GlobalTheory.TorsionFormCompare
