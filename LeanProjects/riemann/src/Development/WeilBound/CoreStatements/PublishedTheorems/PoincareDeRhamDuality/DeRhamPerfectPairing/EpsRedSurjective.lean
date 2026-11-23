import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

theorem rigid {S : Scheme.{0}} {G : Over S} [GrpObj G] (hG : IsAbelianScheme G) {Z : Scheme.{0}} (e : S ⟶ G.left)
    (he : e ≫ G.hom = 𝟙 S) (f : G.left ⟶ Z) (k : S ⟶ Z) (hk : ∀ y, f y = k (G.hom y)) : f = G.hom ≫ e ≫ f := by
  have := hG.proper
  refine Scheme.hom_ext_of_forall _ _ fun y ↦ ?_
  obtain ⟨V, hV, h⟩ := GlobalTheory.local_rigidity _ _ _ G.hom e f he inferInstance
    (GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.globalFns_holds G hG) (G.hom y) (k (G.hom y))
    (fun x hx ↦ by rw [hk, hx])
  exact ⟨G.hom ⁻¹ᵁ V, hV, h⟩

theorem epsRed_surjective (R : Type) [CommRing R] : Surjective (GlobalTheory.DeRham.epsRed R) := by
  refine ⟨fun q ↦ ⟨spMap (algebraMap R (DualNumber R)) q, ?_⟩⟩
  refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
  change algebraMap R (DualNumber R) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
  have hn : c - algebraMap R (DualNumber R) c.fst ∈ q.asIdeal := by
    refine q.isPrime.mem_of_pow_mem 2 ?_
    have : (c - algebraMap R (DualNumber R) c.fst) ^ 2 = 0 := by
      ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; exact zero_mem _
  exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩

theorem epsRed_hom (R : Type) [CommRing R] : GlobalTheory.DeRham.epsRed R ≫ (epsR R).hom = 𝟙 _ := by
  change spMap _ ≫ spMap _ = _
  rw [← GlobalTheory.Cris.spMap_comp]
  exact GlobalTheory.Cris.spMap_id R

theorem cube_family (hC : CubeTheorem) {S : Scheme.{0}} {A T : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {M : LB (A ⊗ T).left} (hM : M.IsLB) {Y : Over S} (a a' b : Y ⟶ A) (t : Y ⟶ T) :
    evc hM (a * a' * b) t - evc hM (a * a') t - evc hM b t + evc hM 1 t =
      (evc hM (a * b) t - evc hM a t - evc hM b t + evc hM 1 t) +
        (evc hM (a' * b) t - evc hM a' t - evc hM b t + evc hM 1 t) := by
  obtain ⟨A', _, φ, hφ⟩ : ∃ (A' : Over T.left) (_ : GrpObj A') (φ : A'.left ⟶ A.left), IsGrpPullback A' A T.hom φ :=
    ⟨_, inferInstance, _, isGrpPullback_pullback A T.hom⟩
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hφ
  let W : Over S := Over.mk (A'.hom ≫ T.hom)
  let j : W ⟶ A ⊗ T := lift (Over.homMk φ hφ.1.w) (Over.homMk A'.hom rfl)
  have j₁ : j.left ≫ (fst A T).left = φ := lift_left_fst _ _
  have j₂ : j.left ≫ (snd A T).left = A'.hom := lift_left_snd _ _
  have hs : t.left ≫ T.hom = Y.hom := Over.w t
  let q : (Y ⟶ A) → (Over.mk t.left ⟶ A') := fun a ↦ liftPt hφ t.left a.left ((Over.w a).trans hs.symm)
  have q₁ : ∀ a, (q a).left ≫ φ = a.left := fun a ↦ liftPt_left _ _ _ _
  have qm : ∀ a b, q a * q b = q (a * b) := fun a b ↦ pt_ext hφ
    ((mul_left_comp hφ hs (x₀ := (a : Over.mk Y.hom ⟶ A)) (y₀ := (b : Over.mk Y.hom ⟶ A)) (q₁ a) (q₁ b)).trans
      (q₁ (a * b)).symm)
  have qo : (1 : Over.mk t.left ⟶ A') = q 1 := pt_ext hφ ((one_left_comp hφ hs).trans (q₁ 1).symm)
  have hM' : (M.pull j.left).IsLB := pull_isLB hM _
  have ev : ∀ a, GlobalTheory.CechPic.pull (q a).left (cls (X := A'.left) _ hM') = evc hM a t := fun a ↦ by
    have e : (q a).left ≫ j.left = (lift a t).left := left_ext
      (((Category.assoc _ _ _).trans (congrArg _ j₁)).trans ((q₁ a).trans (lift_left_fst a t).symm))
      (((Category.assoc _ _ _).trans (congrArg _ j₂)).trans ((Over.w (q a)).trans (lift_left_snd a t).symm))
    exact (pull_comp _ _ _).symm.trans (congrArg (fun u ↦ GlobalTheory.CechPic.pull u (cls M hM)) e)
  have e := GlobalTheory.CubeDual.lam_mul_left hC hA' (L := M.pull j.left) hM' (q a) (q a') (q b)
  simp only [lam, qm, qo, ev] at e
  exact e

theorem additive_eps (hC : CubeTheorem) {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hP : IsDual A B P) {M : LB (A ⊗ epsR R).left} (hM : M.IsLB) (h₀ : ∀ (Y : Over (Sp R)) (t : Y ⟶ epsR R), evc hM (1 : Y ⟶ A) t = 0) (h₁ : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ epsR R), t.left = Y.hom ≫ GlobalTheory.DeRham.epsRed R → evc hM a t = 0) : IsAdditive M := by
  let Λ : ∀ {Y : Over (Sp R)}, (Y ⟶ A) → (Y ⟶ A ⊗ epsR R) → Pic Y.left := fun a y ↦
    evc hM (a * (y ≫ fst _ _)) (y ≫ snd _ _) - evc hM a (y ≫ snd _ _) - evc hM (y ≫ fst _ _) (y ≫ snd _ _) +
      evc hM 1 (y ≫ snd _ _)
  obtain ⟨N, hN, eN⟩ := cls_surj (Λ (fst A (A ⊗ epsR R)) (snd A (A ⊗ epsR R)))
  have vN : ∀ {Y : Over (Sp R)} (a : Y ⟶ A) (y : Y ⟶ A ⊗ epsR R), evc hN a y = Λ a y := fun a y ↦ by
    rw [evc, eN]
    simp only [Λ, map_add, map_sub, pull_evc, MonObj.comp_mul, MonObj.comp_one, lift_fst, lift_snd_assoc]
  have aN : IsAdditive N := (isAdditive_iff hN).2 fun Y a a' y ↦ by
    rw [vN, vN, vN]
    exact cube_family hC hA hM a a' _ _
  obtain ⟨x, hx, -⟩ := hP.univ _ N hN aN
  have ex : cls N hN = evc hP.isLB (fst _ _) (snd _ _ ≫ x) := (cls_eq_iff hN (pull_isLB hP.isLB _)).2 hx
  have one : ∀ {Y : Over (Sp R)} (y : Y ⟶ A ⊗ epsR R), Λ (fst A Y) (snd A Y ≫ y) = 0 → y ≫ x = 1 := fun y h ↦
    hP.eq_one _ ((triv_ev_iff hP.isLB _ _).2 (by
      rw [← Category.assoc, ← GlobalTheory.BirigidLift.evc_of_cls hP.isLB hN ex, vN, h]))
  let z : A ⟶ epsR R := Over.homMk (A.hom ≫ GlobalTheory.DeRham.epsRed R) (by
    rw [Category.assoc, epsRed_hom, Category.comp_id])
  have x₁ : lift (𝟙 A) z ≫ x = 1 := one _ (by
    have hz : ((snd A A ≫ lift (𝟙 A) z) ≫ snd _ _).left = (A ⊗ A).hom ≫ GlobalTheory.DeRham.epsRed R := by
      rw [Category.assoc, lift_snd, Over.comp_left, ← Over.w (snd A A), Category.assoc]
      rfl
    simp only [Λ, h₁ _ _ _ hz, sub_zero, add_zero])
  have x₂ : lift 1 (𝟙 (epsR R)) ≫ x = 1 := one _ (by
    simp only [Λ, Category.assoc, lift_fst, lift_snd, MonObj.comp_one, _root_.mul_one, sub_self, h₀, sub_zero,
      add_zero])
  have x0 : x = 1 := by
    obtain ⟨A', _, φ, hφ⟩ : ∃ (A' : Over (epsR R).left) (_ : GrpObj A') (φ : A'.left ⟶ A.left),
        IsGrpPullback A' A (epsR R).hom φ := ⟨_, inferInstance, _, isGrpPullback_pullback A (epsR R).hom⟩
    have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hφ
    let W : Over (Sp R) := Over.mk (A'.hom ≫ (epsR R).hom)
    let j : W ⟶ A ⊗ epsR R := lift (Over.homMk φ hφ.1.w) (Over.homMk A'.hom rfl)
    have j₁ : j.left ≫ (fst A (epsR R)).left = φ := lift_left_fst _ _
    have j₂ : j.left ≫ (snd A (epsR R)).left = A'.hom := lift_left_snd _ _
    have lf : ∀ {Y : Over (Sp R)} (y : Y ⟶ A ⊗ epsR R), ∃ u : Y.left ⟶ A'.left,
        u ≫ φ = (y ≫ fst _ _).left ∧ u ≫ A'.hom = (y ≫ snd _ _).left ∧ u ≫ j.left = y.left := fun y ↦ by
      have w : (y ≫ fst _ _).left ≫ A.hom = (y ≫ snd _ _).left ≫ (epsR R).hom :=
        (Over.w _).trans (Over.w _).symm
      refine ⟨hφ.1.lift _ _ w, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _, left_ext ?_ ?_⟩
      · exact ((Category.assoc _ _ _).trans (congrArg _ j₁)).trans (hφ.1.lift_fst _ _ _)
      · exact ((Category.assoc _ _ _).trans (congrArg _ j₂)).trans (hφ.1.lift_snd _ _ _)
    obtain ⟨i, i₁, i₂, i₃⟩ := lf (lift (𝟙 A) z)
    obtain ⟨e, -, e₂, e₃⟩ := lf (lift 1 (𝟙 (epsR R)))
    obtain ⟨u, -, u₂, u₃⟩ := lf (𝟙 _)
    rw [lift_fst] at i₁
    rw [lift_snd] at i₂ e₂
    have i₂' : i ≫ A'.hom = A.hom ≫ GlobalTheory.DeRham.epsRed R := i₂
    have pb : IsPullback i A.hom A'.hom (GlobalTheory.DeRham.epsRed R) := by
      refine IsPullback.of_right ?_ i₂' hφ.1
      rw [i₁, epsRed_hom]
      haveI : IsIso (Over.Hom.left (𝟙 A)) := by rw [Over.id_left]; infer_instance
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
    have hi : Surjective i := MorphismProperty.of_isPullback (P := @Surjective) pb.flip (epsRed_surjective R)
    let k : (epsR R).left ⟶ B.left := (1 : epsR R ⟶ B).left
    have ik : i ≫ j.left ≫ x.left = i ≫ A'.hom ≫ k := by
      rw [← Category.assoc, i₃, ← Category.assoc, i₂, ← Over.comp_left, x₁, ← Over.comp_left, MonObj.comp_one]
    have rg := rigid hA' e e₂ (j.left ≫ x.left) k fun y ↦ by
      obtain ⟨y, rfl⟩ := hi.surj y
      exact congrArg (fun u ↦ u y) ik
    have ek : e ≫ j.left ≫ x.left = k := by
      rw [← Category.assoc, e₃, ← Over.comp_left, x₂]
    rw [ek] at rg
    apply Over.OverMorphism.ext
    have h := congrArg (u ≫ ·) rg
    simp only [← Category.assoc] at h
    rw [u₃, u₂] at h
    refine ((Category.id_comp _).symm.trans h).trans ?_
    rw [← Over.comp_left, MonObj.comp_one]
  refine (isAdditive_iff hM).2 fun Y a a' t ↦ ?_
  have h := GlobalTheory.BirigidLift.evc_of_cls hP.isLB hN ex a (lift a' t)
  rw [x0, MonObj.comp_one, evc_one_right hP.isLB hP.zero, vN] at h
  simp only [Λ, lift_fst, lift_snd, h₀, add_zero] at h
  rw [← sub_eq_zero, ← h]
  abel

end CrystallinePoints.Pd
