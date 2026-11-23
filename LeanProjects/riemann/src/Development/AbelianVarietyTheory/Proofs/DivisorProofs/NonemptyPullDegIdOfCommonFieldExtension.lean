import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoUniqueOfRig
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ

namespace GlobalTheory.FieldDescent

open GlobalTheory.PsiEvenPull (proj)
open GlobalTheory.GenSpread

variable {K Ω : Type} [Field K] [Field Ω] {l : K →+* Ω} {D₁ D₂ : DegPre K} {D : DegPre Ω}

theorem lbIso_of_common_pull (h₁ : IsPullDeg l D₁ D) (h₂ : IsPullDeg l D₂ D) {Φ : D₂.P.A.left ⟶ D₁.P.A.left}
    (hΦ : proj h₂ ≫ Φ = proj h₁) : LBIso D₂.P.L (D₁.P.L.pull Φ) := by
  have e : pullback.fst D₂.P.A.hom (specOf l) = h₂.e.inv.left ≫ proj h₂ := by
    rw [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    exact (Category.id_comp _).symm
  have e' : pullback.fst D₂.P.A.hom (specOf l) ≫ Φ = h₂.e.inv.left ≫ proj h₁ :=
    (congrArg (· ≫ Φ) e).trans ((Category.assoc _ _ _).trans (congrArg (h₂.e.inv.left ≫ ·) hΦ))
  exact PolIsoDescent.lbIso_descend globalFns_holds (specOf l) D₂.P.A D₂.P.isAb D₂.P.isLB (pull_isLB D₁.P.isLB Φ)
    (LBIso.trans (pull_isLB D₂.P.isLB _) (pull_isLB D.P.isLB _) (pull_isLB (pull_isLB D₁.P.isLB _) _)
      (lbIso_pull_of_lbIso ⟨h₂.w, h₂.w_gen⟩ h₂.e.inv.left e).symm
      (LBIso.trans (pull_isLB D.P.isLB _) (pull_isLB D₁.P.isLB _) (pull_isLB (pull_isLB D₁.P.isLB _) _)
        (lbIso_pull_of_lbIso ⟨h₁.w, h₁.w_gen⟩ h₂.e.inv.left e') (lbIso_pull_pull D₁.P.isLB _ rfl)))

theorem om_eq (h₁ : IsPullDeg l D₁ D) {ψ : D.P.A.left ⟶ D₁.P.A.left} (v : LB.Iso D.P.L (D₁.P.L.pull ψ))
    (hψ : ψ = proj h₁) (gv : PGen v)
    (pv : PMaps v (K := PUnit) (fun _ => eSec D.P.A) (fun _ => eSec D₁.P.A) (fun _ => 1) D.rig D₁.rig (spMap l))
    {Z : Scheme.{0}} (z : Z) (J J') (q : Z ⟶ D.P.A.left) : om v z J J' q = om h₁.w z J J' q := by
  subst hψ
  rw [iso_unique_of_rig globalFns_holds D.P.A D.P.isAb D.P.isLB D₁.P.isLB ((isGen_iff v).2 gv) h₁.w_gen
    ((maps_iff v _ (fun _ => eSec D₁.P.A) _ D.rig D₁.rig (specOf l) _
      (rigPull_le (proj h₁) (specOf l) h₁.he D₁.P.L) (fun _ => rfl)).2 pv) h₁.w_rig]

end GlobalTheory.FieldDescent

open GlobalTheory.PsiEvenPull (proj) in

theorem GlobalTheory.nonempty_isPullDeg_id_of_common_pull : ∀ (K Ω : Type) [Field K] [Field Ω] (l : K →+* Ω) (D₁ D₂ : DegPre K) (D : DegPre Ω) (h₁ : IsPullDeg l D₁ D) (h₂ : IsPullDeg l D₂ D) (φ : D₂.P.A ≅ D₁.P.A), IsMonHom φ.hom → h₂.e.hom.left ≫ pullback.fst D₂.P.A.hom (specOf l) ≫ φ.hom.left = h₁.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf l) → Nonempty (IsPullDeg (RingHom.id K) D₁ D₂) := by
  intro K Ω _ _ l D₁ D₂ D h₁ h₂ φ hm hφ
  have hΦ : proj h₂ ≫ φ.hom.left = proj h₁ := (Category.assoc _ _ _).trans hφ
  have hs : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id (CommRingCat.of K)
  have gp : IsGrpPullback D₂.P.A D₁.P.A (spMap (RingHom.id K)) φ.hom.left :=
    (Geo.Tor.isGrpPullback_of_iso φ).congr hs.symm rfl
  have he : eSec D₂.P.A ≫ φ.hom.left = spMap (RingHom.id K) ≫ eSec D₁.P.A := (cubeMapOf gp).e_comm
  obtain ⟨w, gw', rw'⟩ := Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap (RingHom.id K)) D₁.P.A D₂.P.A φ.hom.left he
    ⟨D₁.P.L, D₁.rig, D₁.P.isLB, D₁.rig_gen⟩ ⟨D₂.P.L, D₂.rig, D₂.P.isLB, D₂.rig_gen⟩
    (FieldDescent.lbIso_of_common_pull h₁ h₂ hΦ)
  have pw' := (isGen_iff w).1 gw'
  have p₂ := (isGen_iff h₂.w).1 h₂.w_gen
  have r₀ := (maps_iff w _ (fun _ => eSec D₁.P.A) _ D₂.rig D₁.rig (spMap (RingHom.id K)) _
    (rigPull_le φ.hom.left (spMap (RingHom.id K)) he D₁.P.L) (fun _ => rfl)).1 rw'
  obtain ⟨v, T⟩ := exists_comp D₂.P.isLB w h₂.w pw' p₂ D₁.P.isLB D.P.isLB
  have r₂ := T.pmaps_comp D₂.P.isLB (fun _ => h₂.he) r₀ (FieldPull.pmaps_rig h₂)
  rw [← spMap_comp] at r₂
  have hom := fun {Z : Scheme.{0}} (z : Z) J J' q =>
    FieldDescent.om_eq h₁ v hΦ (T.pgen_comp D₂.P.isLB pw' p₂) r₂ z J J' q
  obtain ⟨f₁, f₂⟩ := PolIsoDescent.flat_surjective (spMap l)
  have : Epi (spMap l) := Flat.epi_of_flat_of_surjective _
  let xe : D₂.X ≃+ D₁.X := h₂.xe.symm.trans h₁.xe
  have hxe : ∀ y, xe (h₂.xe y) = h₁.xe y := fun y => congrArg h₁.xe (h₂.xe.symm_apply_apply y)
  have hc : ∀ x, (D₂.c x).left ≫ φ.hom.left = spMap (RingHom.id K) ≫ (D₁.c (xe x)).left := fun x => by
    obtain ⟨y, rfl⟩ := h₂.xe.surjective x
    rw [hxe, hs]
    refine Eq.trans ?_ (Category.id_comp _).symm
    refine (cancel_epi (spMap l)).1 ((Category.assoc _ _ _).symm.trans ?_)
    exact (congrArg (· ≫ φ.hom.left) (h₂.c_pr y).symm).trans ((Category.assoc _ _ _).trans
      ((congrArg ((D.c y).left ≫ ·) hΦ).trans (h₁.c_pr y)))
  have si : jK K ≫ spMap (RingHom.id K) = genMap (RingHom.id K).injective ≫ jK K :=
    (Category.id_comp _).symm.trans (fracMap_sq (RingHom.id K).injective)
  have si' : genMap (RingHom.id K).injective ≫ jK K = jK K :=
    si.symm.trans ((congrArg (jK K ≫ ·) hs).trans (Category.comp_id _))
  have sl := fracMap_sq l.injective
  obtain ⟨hD, -⟩ := FieldPull.exists_isPullDeg_of_val (RingHom.id K) D₁ D₂ gp w pw' r₀ xe hc
    (fun x z J₁ J₂ hJ₁ hJ₂ => by
      obtain ⟨y, rfl⟩ := h₂.xe.surjective x
      have hx : D₂.xK (h₂.xe y) ≫ φ.hom.left = genMap (RingHom.id K).injective ≫ D₁.xK (xe (h₂.xe y)) := by
        show (jK K ≫ (D₂.c _).left) ≫ _ = _ ≫ jK K ≫ (D₁.c _).left
        rw [Category.assoc, hc, ← Category.assoc, si, Category.assoc]
      obtain ⟨a, ha, va⟩ := exists_down_om gw' D₁.P.isLB D₂.P.isLB (K := PUnit) (φ' := fun _ => D₂.xK (h₂.xe y))
        (genMap (RingHom.id K).injective) (fun _ => hx) (D₁.psi (xe (h₂.xe y))) (D₁.psi_gen _)
      obtain ⟨k₁, k₂⟩ := PolIsoDescent.flat_surjective (F := FractionRing Ω) (C := FractionRing K) (genMap l.injective)
      have ea := PsiEvenPull.val_eq_of_app_injective D₂.P.isLB (fun _ _ _ => rfl) (genMap l.injective)
        (fun U => FunDescent.app_injective (genMap l.injective) U) ha (D₂.psi_gen (h₂.xe y)) (fun u I₂ hI₂ => by
          obtain ⟨I₁, hI₁⟩ := DegPull.exists_good' D₁.P.isLB u
          obtain ⟨I, hI⟩ := DegPull.exists_good' D.P.isLB u
          have v₂ := psi_val h₂ _ _ sl hI₂ hI y
          have v₁ := psi_val h₁ (genMap l.injective ≫ genMap (RingHom.id K).injective) _
            (sl.trans ((congrArg (_ ≫ ·) si'.symm).trans (Category.assoc _ _ _).symm)) hI₁ hI y
          have v₀ := va _ (genMap l.injective) u I₁ I₂ hI₁ hI₂
          have hq : genMap l.injective ≫ D₂.xK (h₂.xe y) = (𝟙 _ ≫ D.xK y) ≫ proj h₂ := by
            show _ ≫ jK K ≫ (D₂.c _).left = (𝟙 _ ≫ jK Ω ≫ (D.c y).left) ≫ _
            rw [← Category.assoc, ← sl]
            simp only [Category.assoc]
            exact congrArg (fun q => 𝟙 _ ≫ jK Ω ≫ q) (h₂.c_pr y).symm
          have t : om v u I₁ I (𝟙 _ ≫ D.xK y) =
              om w u I₁ I₂ ((𝟙 _ ≫ D.xK y) ≫ proj h₂) * om h₂.w u I₂ I (𝟙 _ ≫ D.xK y) := by
            rw [om, om, om, Category.assoc (𝟙 _ ≫ D.xK y)]
            exact T _ _ u _ _ _ (hI₁ ((𝟙 _ ≫ D.xK y) ≫ proj h₂ ≫ φ.hom.left)) (hI₂ ((𝟙 _ ≫ D.xK y) ≫ proj h₂)) (hI _)
          rw [Fintype.prod_unique, zpow_neg_one, hq, hxe, v₁, ← hom, t, mul_inv, _root_.mul_assoc] at v₀
          exact (mul_left_cancel v₀).symm.trans v₂.symm) _ (𝟙 _) z J₂ hJ₂
      have v₀ := va _ (𝟙 _) z J₁ J₂ hJ₁ hJ₂
      rw [Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp, ea] at v₀
      exact v₀)
  exact ⟨hD⟩
