import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.GoodReductionUnif

theorem exists_baseChange (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : PolAV S) :
    ∃ (A : PolAV S') (eA : (Over.pullback f).obj P.A ≅ A.A), IsMonHom eA.hom ∧
      ∃ w : LB.Iso (A.L.pull eA.hom.left) (P.L.pull (pullback.fst P.A.hom f)), w.IsGen := by
  obtain ⟨A, g, hg, -, mul, t, ht⟩ := hB S S' f P
  let eA : (Over.pullback f).obj P.A ≅ A.A := Over.isoMk hg.isoPullback.symm hg.isoPullback_inv_snd
  have he : eA.hom.left ≫ g = pullback.fst P.A.hom f := hg.isoPullback_inv_fst
  refine ⟨A, eA, isMonHom_of_mul _ fun T x y => Over.OverMorphism.ext (hg.hom_ext ?_ ?_), ?_⟩
  · have tb : ∀ a : T ⟶ (Over.pullback f).obj P.A, toBase hg.w (a ≫ eA.hom) =
        toBase (A := P.A) (A' := (Over.pullback f).obj P.A) (g := pullback.fst P.A.hom f) pullback.condition a :=
      fun a => Over.OverMorphism.ext ((Category.assoc _ _ _).trans (congrArg (a.left ≫ ·) he))
    have e : toBase hg.w ((x * y) ≫ eA.hom) = toBase hg.w ((x ≫ eA.hom) * (y ≫ eA.hom)) := by
      rw [mul, tb, tb, tb, toBase_mul_pullback]
    exact congrArg CommaMorphism.left e
  · exact (Over.w _).trans (Over.w _).symm
  · obtain ⟨t', ht', -⟩ := GenericSectionBasis.exists_inv_iso t ht
    have h₁ := (isGen_iff t').1 ht'
    have h₂ := (isGen_iff _).1 (pullIso_isGen A.isLB eA.hom.left)
    obtain ⟨w, Tw⟩ := Geo.Tor.exists_comp A.isLB t' (pullIso A.L eA.hom.left) h₁ h₂ P.isLB
      (pull_isLB A.isLB _)
    rw [← he]
    exact ⟨w, (isGen_iff w).2 (Tw.pgen_comp A.isLB h₁ h₂)⟩

theorem vals_change {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : CP G) (T : Over S) (z : T.left)
    {J' J : (T.left ⟶ G.left) → P.L.L.ι} (hJ' : Good P.L.L z J') (hJ : Good P.L.L z J)
    (W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ)
    (a : ∀ x : T ⟶ G, W x = gm x.left z _ (P.L.L.g (J x.left) (J' x.left))) :
    (val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig T.hom z J =
        W 1 * val (L := P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.L.rig T.hom z J') ∧
      (∀ x : T ⟶ G, val P.sym x.left z J * W x = W x⁻¹ * val P.sym x.left z J') ∧
      ∀ x y u : T ⟶ G, cubV P.c z J x y u * W (x * y) * W (x * u) * W (y * u) * W 1 =
        W (x * y * u) * W x * W y * W u * cubV P.c z J' x y u := by
  obtain ⟨h₁, h₂, h₃⟩ := (IsCPMap.id P).vals T z J' J hJ' hJ W fun x => by
    rw [a, Category.comp_id, gw_idIso _ _ _ (hJ _) (hJ' _)]
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · rwa [Category.comp_id] at h₁
  · have := h₂ x
    rwa [Category.comp_id] at this
  · have := h₃ x y u
    rwa [_root_.id, cubV_toBase_id] at this

theorem cub_transfer {A A' U : Type} [Monoid A] [Monoid A'] [Monoid U] (β : A →* A') (W : A → U) (W' : A' → U)
    (a : ∀ x, W x = W' (β x)) {x y u : A} {c₁ c₁' c₂ c₂' : U} (e₁ : c₁ = c₁') (e₂ : c₂ = c₂')
    (h : c₁' * W' (β x * β y) * W' (β x * β u) * W' (β y * β u) * W' 1 =
      W' (β x * β y * β u) * W' (β x) * W' (β y) * W' (β u) * c₂') :
    c₁ * W (x * y) * W (x * u) * W (y * u) * W 1 = W (x * y * u) * W x * W y * W u * c₂ := by
  simpa only [a, map_mul, map_one, e₁, e₂] using h

open SelfUnif in

def selfPreU (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) [Subsingleton D.X]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (eA : (Over.pullback (jK R)).obj D.P.A ≅ A.A)
    (hA : IsMonHom eA.hom) (w : LB.Iso (A.L.pull eA.hom.left) (D.P.L.pull (pullback.fst D.P.A.hom (jK R))))
    (hw : w.IsGen) : PreU I D A D.P.A where
  semi := isSemiAbelian_of_isAbelianScheme _ D.P.isAb
  gen := eA
  gen_hom := hA
  P := CP.ofDegPre hG D
  wA := w
  wA_gen := hw
  gt := selfGt I D
  gt_q e := by rw [selfGt_pG_left, selfGt_pG_left, UnifPullRig.thickMap_fstG]
  gt_t e χ := corr_of_val D.P.isLB fun y J hJ =>
    (val_pull hJ _ _ _).trans ((selfTorusExtensionCoord_values_eq_one I _ _ χ _ y hJ).trans (selfTorusExtensionCoord_values_eq_one I _ _ χ _ y hJ).symm)
  w := selfW I D
  w_gen := selfW_gen I D
  w_vals e T z JG J hJG hJ W hW := by
    let β := toBaseHom (toBase_mul_pullback D.P.A (thick R I e)) T
    have hβ : ∀ x : T ⟶ thickObj R I e D.P.A, (Over.map (thick R I e)).map x ≫ fstG I e D.P.A = β x :=
      fun x => Over.OverMorphism.ext rfl
    obtain ⟨W', hW'⟩ : ∃ W' : (Over.mk (T.hom ≫ thick R I e) ⟶ D.P.A) → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W' x = gm x.left z _ (D.P.L.g (J x.left) (JG x.left)) := ⟨_, fun _ => rfl⟩
    obtain ⟨h₁, h₂, h₃⟩ := vals_change (CP.ofDegPre hG D) (Over.mk (T.hom ≫ thick R I e)) z hJG hJ W' hW'
    have p : ∀ x : T ⟶ thickObj R I e D.P.A, x.left ≫ (selfGt I D e).pG.left = (β x).left :=
      fun x => congrArg (x.left ≫ ·) (selfGt_pG_left I D e)
    have a : ∀ x : T ⟶ thickObj R I e D.P.A, W x = W' (β x) := fun x => by
      refine (hW x).trans ((congrArg (fun q => gw (selfW I D e) x.left z (J q) (fun _ => JG (β x).left)) (p x)).trans ?_)
      exact (selfW_ident I D e _ x.left z _ _ (hJ (β x).left) (hJG (β x).left)).trans (hW' (β x)).symm
    refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
    · rw [a, β.map_one]
      exact h₁
    · rw [a, a, β.map_inv]
      exact (congrArg (fun q => val D.sym q z J * _) (p x)).trans (h₂ (β x))
    · have c₁ : @id (T.left.presheaf.stalk z)ˣ (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J
          ((Over.map (thick R I e)).map x ≫ (selfGt I D e).pG) ((Over.map (thick R I e)).map y ≫ (selfGt I D e).pG)
          ((Over.map (thick R I e)).map u ≫ (selfGt I D e).pG)) =
          cubV (CP.ofDegPre hG D).c (T := Over.mk (T.hom ≫ thick R I e)) z J (β x) (β y) (β u) := by
        rw [selfGt_pG, hβ, hβ, hβ]; rfl
      have c₂ : @id (T.left.presheaf.stalk z)ˣ (cubV (CP.ofDegPre hG D).c (T := (Over.map (thick R I e)).obj T) z JG
          ((Over.map (thick R I e)).map x ≫ fstG I e D.P.A) ((Over.map (thick R I e)).map y ≫ fstG I e D.P.A)
          ((Over.map (thick R I e)).map u ≫ fstG I e D.P.A)) =
          cubV (CP.ofDegPre hG D).c (T := Over.mk (T.hom ≫ thick R I e)) z JG (β x) (β y) (β u) := by
        rw [hβ, hβ, hβ]; rfl
      exact cub_transfer β W W' a c₁ c₂ (h₃ (β x) (β y) (β u))
  w_compat e Z x z j k hj hk := by
    have hj' : (x ≫ (fstG I e D.P.A).left) z ∈ D.P.L.U j :=
      (congrArg (fun q => q (x z) ∈ _) (selfGt_pG_left I D e)).mp hj
    have t : (x ≫ thickMap R I e D.P.A) ≫ (fstG I (e + 1) D.P.A).left = x ≫ (fstG I e D.P.A).left :=
      (Category.assoc _ _ _).trans (congrArg (x ≫ ·) (UnifPullRig.thickMap_fstG I e D.P.A))
    have a := selfW_ident I D e _ x z _ _ hj' hk
    have b := selfW_ident I D (e + 1) _ (x ≫ thickMap R I e _) z _ _
      ((congrArg (fun q => q z ∈ _) t).mpr hj') ((congrArg (fun q => q z ∈ _) t).mpr hk)
    exact (b.trans (congrArg (fun q => gm q z _ (D.P.L.g j k)) t)).trans a.symm

theorem main : Laws → Laws2 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ P : PolAV (Spec (CommRingCat.of V)), ∃ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (D : DegData V (IsLocalRing.maximalIdeal V)), Nonempty (Unif (IsLocalRing.maximalIdeal V) D A P.A) ∧ Nonempty (PreU (IsLocalRing.maximalIdeal V) D.toPre A P.A)) := by
  intro hL _ V _ _ _ hV P
  obtain ⟨h₁, h₂, -⟩ := hV
  have : IsNoetherianRing V := inferInstance
  obtain ⟨A, eA, hA, w, hw⟩ := exists_baseChange hL.polBaseChange (jK V) P
  obtain ⟨D, rfl, hX, hU⟩ := exists_unif_abelianScheme hL.globalFns hL.secBaseChange hL.cube V
    (IsLocalRing.maximalIdeal V) P A eA hA ⟨w, hw⟩
  exact ⟨A, D, hU, ⟨selfPreU hL.globalFns _ D.toPre A eA hA w hw⟩⟩

end GlobalTheory.GoodReductionUnif

end
