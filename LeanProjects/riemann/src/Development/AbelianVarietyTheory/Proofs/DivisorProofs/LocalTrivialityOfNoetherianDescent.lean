import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFgModel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundleIsoDescendsToSubringOfFinset
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocTrivDescent
open GlobalTheory.CechPic

theorem triv_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) :
    (∃ t : (L.pull f).Gen, t.IsGen) ↔ CechPic.pull f (cls L hL) = 0 := by
  rw [← cls_pull hL f (pull_isLB hL f), cls_eq_zero_iff]

theorem cls_lbPow_eq {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (k : ℕ) (h : (Hecke.lbPow L k).IsLB) :
    cls _ h = k • cls L hL :=
  (cls_linComb hL _ _ h).trans (by simp [pull_id])

theorem one_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (1 : 𝟙_ (Over S') ⟶ G').left ≫ φ = f ≫ (1 : 𝟙_ (Over S) ⟶ G).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  let U : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ 𝟙_ (Over S) := Over.homMk f (by simp)
  have e2 : (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) = U ≫ 1 := (comp_one U).symm
  exact e.trans (by rw [e2]; rfl)

theorem fibre_triv {R R₁ : Type} [CommRing R] [CommRing R₁] (j : R₁ →+* R) {A : Over (Sp R)} {A₁ : Over (Sp R₁)}
    {ψ : A.left ⟶ A₁.left} (hψ : IsPullback ψ A.hom A₁.hom (spMap j)) {K : Type} [Field K] (g₀ : R →+* K)
    (c : Pic A₁.left) (h : CechPic.pull (pullback.fst A.hom (spMap g₀)) (CechPic.pull ψ c) = 0) :
    CechPic.pull (pullback.fst A₁.hom (spMap (g₀.comp j))) c = 0 := by
  have w : pullback.fst A₁.hom (spMap (g₀.comp j)) ≫ A₁.hom =
      (pullback.snd A₁.hom (spMap (g₀.comp j)) ≫ spMap g₀) ≫ spMap j := by
    rw [pullback.condition, Category.assoc, GlobalTheory.spMap_comp_ring]
  let a := hψ.lift _ _ w
  have ha1 : a ≫ ψ = pullback.fst _ _ := hψ.lift_fst _ _ _
  have ha2 : a ≫ A.hom = pullback.snd _ _ ≫ spMap g₀ := hψ.lift_snd _ _ _
  let n := pullback.lift a (pullback.snd _ _) ha2
  have hn : n ≫ pullback.fst A.hom (spMap g₀) = a := pullback.lift_fst _ _ _
  rw [← ha1, ← hn, Category.assoc, pull_comp, pull_comp, h, map_zero]

theorem basicOpen_triv {R R₁ : Type} [CommRing R] [CommRing R₁] (j : R₁ →+* R) {A : Over (Sp R)}
    {A₁ : Over (Sp R₁)} {ψ : A.left ⟶ A₁.left} (w : ψ ≫ A₁.hom = A.hom ≫ spMap j) (c : Pic A₁.left) (r : R₁)
    (h : CechPic.pull (A₁.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι c = 0) :
    CechPic.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (j r)).ι (CechPic.pull ψ c) = 0 := by
  have le : A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (j r) ≤ ψ ⁻¹ᵁ (A₁.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r) := by
    intro x hx
    have e : A₁.hom.base (ψ.base x) = (spMap j).base (A.hom.base x) := by
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
    show A₁.hom.base (ψ.base x) ∈ PrimeSpectrum.basicOpen r
    rw [e]
    exact hx
  rw [← pull_comp, ← Scheme.Hom.resLE_comp_ι ψ le, pull_comp, h, map_zero]

end GlobalTheory.LocTrivDescent

namespace GlobalTheory.LocTrivDescent
open GlobalTheory.CechPic

theorem cls_spread (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀)
    (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] (M : LB X₀) (hM : M.IsLB)
    (hp : IsPullback π f f₀ (spMap R₀.subtype)) (h0 : CechPic.pull π (cls M hM) = 0) :
    ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁)
      (π₁ : X₁ ⟶ X₀), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → CechPic.pull π₁ (cls M hM) = 0 := by
  have hT := LB.isLB_triv X₀
  have z : cls (LB.triv X₀) hT = 0 := rfl
  have key : ∀ {Y : Scheme.{0}} (g : Y ⟶ X₀),
      CechPic.pull g (cls M hM) = 0 ↔ LBIso (M.pull g) ((LB.triv X₀).pull g) := by
    intro Y g
    rw [← cls_eq_iff (pull_isLB hM g) (pull_isLB hT g), cls_pull hM, cls_pull hT, z, map_zero]
  obtain ⟨F, hF⟩ := GlobalTheory.lbIso_descends_to_subring_containing_finset S R₀ X X₀ f f₀ π M (LB.triv X₀) hp hM hT
    ((key π).1 h0)
  exact ⟨F, fun R₁ h hs X₁ f₁ π₁ hp₁ => (key π₁).2 (hF R₁ h hs X₁ f₁ π₁ hp₁)⟩

theorem locTriv_of_noetherian : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  intro H R _ A _ hA M hM h1 k hk h2 K _ g₀ h3
  classical
  obtain ⟨S, G₀, _, φ, L₀, hft, hab, hφ, hL₀, hiso⟩ := GlobalTheory.AmpleFibreMove.exists_fg_model R A hA M hM
  have := hab.proper
  set c₀ := cls L₀ hL₀ with hc₀
  have hc : cls M hM = CechPic.pull φ c₀ := by
    rw [hc₀, ← cls_pull hL₀ φ (pull_isLB hL₀ φ)]
    exact (cls_eq_iff _ _).2 hiso

  let e₀ : Sp S ⟶ G₀.left := (1 : 𝟙_ (Over (Sp S)) ⟶ G₀).left
  have ha : CechPic.pull (spMap S.subtype) (CechPic.pull e₀ c₀) = 0 := by
    rw [← pull_comp, ← one_left_comp hφ, pull_comp, ← hc]
    exact (triv_iff hM _).1 h1
  obtain ⟨F₁, hF₁⟩ := cls_spread R S (Sp R) (Sp S) (𝟙 _) (𝟙 _) (spMap S.subtype) (L₀.pull e₀)
    (pull_isLB hL₀ e₀) (IsPullback.id_vert _) ha

  have hP₀ : (Hecke.lbPow L₀ k).IsLB := LB.isLB_linComb hL₀ _ _
  have hb : CechPic.pull φ (cls _ hP₀) = 0 := by
    obtain ⟨t, ht⟩ := h2
    have hPM : (Hecke.lbPow M k).IsLB := LB.isLB_linComb hM _ _
    have e := (cls_eq_zero_iff hPM).2 ⟨t, ht⟩
    rw [cls_lbPow_eq hM, hc] at e
    rw [cls_lbPow_eq hL₀, map_nsmul]
    exact e
  obtain ⟨F₂, hF₂⟩ := cls_spread R S A.left G₀.left A.hom G₀.hom φ _ hP₀ hφ.1 hb

  obtain ⟨u, hu⟩ : ∃ u : R, (k : R) * u = 1 := ⟨_, hk.mul_val_inv⟩
  obtain ⟨R₁, h, hT, hft₁⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S (F₁ ∪ F₂ ∪ {u}) hft
  have hT₁ : (F₁ : Set R) ⊆ R₁ := fun x hx => hT (by simp [hx])
  have hT₂ : (F₂ : Set R) ⊆ R₁ := fun x hx => hT (by simp [hx])
  have hu₁ : u ∈ R₁ := hT (by simp)
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing ℤ R₁
  let t : Sp R₁ ⟶ Sp S := spMap (Subring.inclusion h)
  have et : spMap R₁.subtype ≫ t = spMap S.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have := hab.comm
  have := hab.smooth
  have := hab.geomConnected
  letI : GrpObj ((Over.pullback t).obj G₀) := Functor.grpObjObj
  let A₁ : Over (Sp R₁) := (Over.pullback t).obj G₀
  have hab₁ : IsAbelianScheme A₁ :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (pullback.snd G₀.hom t))
      proper := inferInstanceAs (IsProper (pullback.snd G₀.hom t))
      geomConnected := inferInstanceAs (GeometricallyConnected (pullback.snd G₀.hom t)) }
  have hpb₁ : IsPullback (pullback.fst G₀.hom t) A₁.hom G₀.hom t := IsPullback.of_hasPullback _ _
  have wφ : φ ≫ G₀.hom = (A.hom ≫ spMap R₁.subtype) ≫ t := by
    rw [Category.assoc, et]; exact hφ.1.w
  let ψ : A.left ⟶ A₁.left := pullback.lift φ (A.hom ≫ spMap R₁.subtype) wφ
  have hψ₁ : ψ ≫ pullback.fst G₀.hom t = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = A.hom ≫ spMap R₁.subtype := pullback.lift_snd _ _ _
  have hψ : IsGrpPullback A A₁ (spMap R₁.subtype) ψ :=
    (isGrpPullback_pullback G₀ t).cancel (hφ.congr et.symm hψ₁.symm) hψ₂
  let M₁ : LB A₁.left := L₀.pull (pullback.fst G₀.hom t)
  have hM₁ : M₁.IsLB := pull_isLB hL₀ _
  have hc₁ : cls M₁ hM₁ = CechPic.pull (pullback.fst G₀.hom t) c₀ := cls_pull hL₀ _ _
  have hcM : cls M hM = CechPic.pull ψ (cls M₁ hM₁) := by
    rw [hc₁, ← pull_comp, hψ₁, hc]
  obtain ⟨r, hr, hgen⟩ := H R₁ A₁ hab₁ M₁ hM₁
    ((triv_iff hM₁ _).2 (by
      rw [hc₁, ← pull_comp, one_left_comp (isGrpPullback_pullback G₀ t), pull_comp]
      exact hF₁ R₁ h hT₁ (Sp R₁) (𝟙 _) t (IsPullback.id_vert _)))
    k (isUnit_iff_exists_inv.2 ⟨⟨u, hu₁⟩, Subtype.ext (by simpa using hu)⟩)
    (by
      have hPM₁ : (Hecke.lbPow M₁ k).IsLB := LB.isLB_linComb hM₁ _ _
      refine (cls_eq_zero_iff hPM₁).1 ?_
      rw [cls_lbPow_eq hM₁, hc₁, ← map_nsmul, ← cls_lbPow_eq hL₀ k hP₀]
      exact hF₂ R₁ h hT₂ A₁.left A₁.hom _ hpb₁)
    K (g₀.comp R₁.subtype)
    ((triv_iff hM₁ _).2 (fibre_triv R₁.subtype hψ.1 g₀ _ (by rw [← hcM]; exact (triv_iff hM _).1 h3)))
  refine ⟨r, hr, (triv_iff hM _).2 ?_⟩
  rw [hcM]
  exact basicOpen_triv R₁.subtype hψ₂ _ r ((triv_iff hM₁ _).1 hgen)

end GlobalTheory.LocTrivDescent
