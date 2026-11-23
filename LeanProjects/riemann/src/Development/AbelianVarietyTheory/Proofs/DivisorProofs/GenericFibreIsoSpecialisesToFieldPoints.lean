import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.Spread

theorem spread_fibre : ∀ (o Ω : Type) [CommRing o] [IsNoetherianRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (G : Over M.Z) [GrpObj G], IsSemiAbelian G → ∀ (R' : Subalgebra o Ω) (B : Over (Sp R')) [GrpObj B], IsSemiAbelian B → ∀ (A₀ : Over (Sp Ω)) [GrpObj A₀] (a' : A₀.left ⟶ B.left) (ψ : A₀.left ⟶ G.left), IsGrpPullback A₀ B (spMap R'.val.toRingHom) a' → IsGrpPullback A₀ G M.pt ψ → ∀ (K : Type) [Field K] (s : Sp K ⟶ M.Z), R' ≤ M.O (s (closedPoint K)) → ∀ (yK : R' →+* K), (∀ x : R', yK x = M.val s x) → ∀ (AK : Over (Sp K)) [GrpObj AK] (φK : AK.left ⟶ B.left), IsGrpPullback AK B (spMap yK) φK → ∃ Ψ : AK.left ⟶ G.left, IsGrpPullback AK G s Ψ ∧ (∀ (e : B ⟶ B) (F : G ⟶ G) (e₀ : A₀ ⟶ A₀), e₀.left ≫ a' = a' ≫ e.left → e₀.left ≫ ψ = ψ ≫ F.left → ∀ eK : AK ⟶ AK, eK.left ≫ φK = φK ≫ e.left → eK.left ≫ Ψ = Ψ ≫ F.left) ∧ ∀ (b : Sp R' ⟶ B.left) (gγ : Over.mk M.pt ⟶ G) (w : Sp Ω ⟶ A₀.left), b ≫ B.hom = 𝟙 _ → w ≫ A₀.hom = 𝟙 _ → w ≫ a' = spMap R'.val.toRingHom ≫ b → w ≫ ψ = gγ.left → ∀ (T : Scheme.{0}) (x : T ⟶ AK.left) (v : T ⟶ G.left), x ≫ φK = x ≫ AK.hom ≫ spMap yK ≫ b → ValAt gγ (x ≫ AK.hom ≫ s) v → x ≫ Ψ = v := by
  intro o Ω _ _ _ _ M hN G _ hG R' B _ hB A₀ _ a' ψ ha' hψ K _ s hR' yK hyK AK _ φK hφK
  set z := s (closedPoint K) with hz
  haveI : IsNoetherianRing (M.O z) := M.isNoetherianRing_O z
  haveI : IsIntegrallyClosed (M.O z) := RatModel.isIntegrallyClosed_O hN z

  let ιO : Sp (M.O z) ⟶ M.Z :=
    Spec.map (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) ≫
      M.Z.fromSpecStalk z
  have key : ∀ {C : Type} [CommRing C] [IsLocalRing C] (y : Sp C ⟶ M.Z) (hy : y (closedPoint C) ⤳ z)
      (r : M.O z →+* C), r.comp (M.stalkEquiv z).toRingHom =
        (M.Z.presheaf.stalkSpecializes hy ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of C) y).hom →
      spMap r ≫ ιO = y := by
    intro C _ _ y hy r hr
    have e : (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) ≫
        CommRingCat.ofHom r = M.Z.presheaf.stalkSpecializes hy ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of C) y := by
      ext a
      exact congrArg (fun f : M.Z.presheaf.stalk z →+* C => f a) hr
    have e2 : spMap r ≫ Spec.map (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) =
        Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of C) y) ≫ Spec.map (M.Z.presheaf.stalkSpecializes hy) :=
      (Spec.map_comp _ _).symm.trans ((congrArg Spec.map e).trans (Spec.map_comp _ _))
    change spMap r ≫ Spec.map (CommRingCat.ofHom (M.stalkEquiv z).toRingHom : M.Z.presheaf.stalk z ⟶ CommRingCat.of (M.O z)) ≫
      M.Z.fromSpecStalk z = y
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ M.Z.fromSpecStalk z) e2).trans
      ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of C) y) ≫ ·)
      (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hy)).trans ?_
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk y
  have hpt : spMap (algebraMap (M.O z) Ω) ≫ ιO = M.pt :=
    key M.pt (M.pt_specializes _ z) _ (by ext a; rfl)
  let v : M.O z →+* K := RatModel.valLoc s z specializes_rfl
  have hs : spMap v ≫ ιO = s := key s specializes_rfl v (by ext a; simp [v, RatModel.valLoc])

  let ι' : R' →+* M.O z := (Subalgebra.inclusion hR').toRingHom
  have hyv : yK = v.comp ι' := by
    ext x
    rw [hyK x, RingHom.comp_apply]
    exact (RatModel.valLoc_eq_val s specializes_rfl (ι' x)).symm
  have spc : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap (g.comp f) = spMap g ≫ spMap f := fun f g => by
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hyK' : spMap yK = spMap v ≫ spMap ι' := by rw [hyv, spc]
  have hval : spMap R'.val.toRingHom = spMap (algebraMap (M.O z) Ω) ≫ spMap ι' := by
    rw [← spc]; rfl

  let BO := (Over.pullback (spMap ι')).obj B
  let GO := (Over.pullback ιO).obj G
  have hBO : IsGrpPullback BO B (spMap ι') (pullback.fst _ _) := isGrpPullback_pullback B _
  have hGO : IsGrpPullback GO G ιO (pullback.fst _ _) := isGrpPullback_pullback G _
  have hBOs : IsSemiAbelian BO := IsSemiAbelian.pullback _ B hB
  have hGOs : IsSemiAbelian GO := IsSemiAbelian.pullback _ G hG
  let j := spMap (algebraMap (M.O z) Ω)
  let a₀ : A₀.left ⟶ BO.left := pullback.lift a' (A₀.hom ≫ j) (by
    rw [ha'.1.w, hval, Category.assoc])
  have ha₀ : a₀ ≫ pullback.fst _ _ = a' := pullback.lift_fst _ _ _
  have ha₀' : a₀ ≫ BO.hom = A₀.hom ≫ j := pullback.lift_snd _ _ _
  have hA₀B : IsGrpPullback A₀ BO j a₀ :=
    hBO.cancel (ha'.congr hval ha₀.symm) ha₀'
  let ψ₀ : A₀.left ⟶ GO.left := pullback.lift ψ (A₀.hom ≫ j) (by
    rw [hψ.1.w, ← hpt, Category.assoc])
  have hψ₀ : ψ₀ ≫ pullback.fst _ _ = ψ := pullback.lift_fst _ _ _
  have hψ₀' : ψ₀ ≫ GO.hom = A₀.hom ≫ j := pullback.lift_snd _ _ _
  have hA₀G : IsGrpPullback A₀ GO j ψ₀ :=
    hGO.cancel (hψ.congr hpt.symm hψ₀.symm) hψ₀'
  have hj : GlobalTheory.IsGenericPointHom j := GlobalTheory.IsGenericPointHom.fractionField (M.O z) Ω
  obtain ⟨E, ⟨hEm, hE⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.generic_existsUnique_iso_of_extensions
    GlobalTheory.semiAbelianHomExtension_holds (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec (M.O z)) hj
    hBOs hGOs hA₀B hA₀G

  let φO : AK.left ⟶ BO.left := pullback.lift φK (AK.hom ≫ spMap v) (by
    rw [hφK.1.w, hyK', Category.assoc])
  have hφO : φO ≫ pullback.fst _ _ = φK := pullback.lift_fst _ _ _
  have hφO' : φO ≫ BO.hom = AK.hom ≫ spMap v := pullback.lift_snd _ _ _
  have hAKB : IsGrpPullback AK BO (spMap v) φO := hBO.cancel (hφK.congr hyK' hφO.symm) hφO'

  obtain ⟨-, hGsep⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨hBOf, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian BO hBOs
  obtain ⟨-, hGOsep⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian GO hGOs
  obtain ⟨hjq, hjd⟩ := hj.quasiCompact_and_dominant
  have hEw : E.hom.left ≫ GO.hom = BO.hom := Over.w E.hom
  refine ⟨φO ≫ E.hom.left ≫ pullback.fst _ _, ?_, ?_, ?_⟩
  · refine ((hAKB.comp (isGrpPullback_of_iso E)).comp hGO).congr ?_ ?_
    · rw [Category.comp_id, hs]
    · simp only [Category.assoc]
  · intro e F e₀ he₀a he₀ψ eK heK
    let eO := (Over.pullback (spMap ι')).map e
    let FO := (Over.pullback ιO).map F
    have heO : eO.left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ e.left := pullback.lift_fst _ _ _
    have heO' : eO.left ≫ BO.hom = BO.hom := Over.w eO
    have hFO : FO.left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ F.left := pullback.lift_fst _ _ _
    have hFO' : FO.left ≫ GO.hom = GO.hom := Over.w FO
    have h1 : e₀.left ≫ a₀ = a₀ ≫ eO.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, ha₀, Category.assoc, heO, ← Category.assoc, ha₀, he₀a]
      · change e₀.left ≫ a₀ ≫ BO.hom = a₀ ≫ eO.left ≫ BO.hom
        rw [heO', ha₀', ← Category.assoc, Over.w e₀]
    have h2 : e₀.left ≫ ψ₀ = ψ₀ ≫ FO.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, hψ₀, Category.assoc, hFO, ← Category.assoc, hψ₀, he₀ψ]
      · change e₀.left ≫ ψ₀ ≫ GO.hom = ψ₀ ≫ FO.left ≫ GO.hom
        rw [hFO', hψ₀', ← Category.assoc, Over.w e₀]
    have h3 : eO ≫ E.hom = E.hom ≫ FO := by
      refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback hA₀B.1 ?_
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← h1, Category.assoc, hE, ← Category.assoc, hE, h2]
    have h4 : eK.left ≫ φO = φO ≫ eO.left := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφO, Category.assoc, heO, ← Category.assoc, hφO, heK]
      · change eK.left ≫ φO ≫ BO.hom = φO ≫ eO.left ≫ BO.hom
        rw [heO', hφO', ← Category.assoc, Over.w eK]
    have h5 := congrArg (fun f => f.left ≫ pullback.fst G.hom ιO) h3
    simp only [Over.comp_left, Category.assoc, hFO] at h5
    rw [← Category.assoc, h4, Category.assoc, h5]
    simp only [Category.assoc]
  · intro b gγ w hb hw hwa hwψ T x vv hx hv
    by_cases hT : IsEmpty T
    · exact (isInitialOfIsEmpty (X := T)).hom_ext _ _
    obtain ⟨t₀⟩ := not_isEmpty_iff.1 hT
    obtain ⟨W, h, s', ⟨h1, h2⟩, hs', rfl⟩ := id hv
    have hzpt : (x ≫ AK.hom ≫ s) t₀ = z := by
      simp only [Scheme.Hom.comp_apply]
      exact congrArg s (Subsingleton.elim _ _)
    have hzW : z ∈ W := by rw [← hzpt, ← hs']; exact (s' t₀).2
    have hr : Set.range ιO ⊆ Set.range W.ι := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hp : ιO p ∈ Set.range (M.Z.fromSpecStalk z) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rw [Scheme.range_fromSpecStalk] at hp
      exact Specializes.mem_open hp W.isOpen hzW
    let ℓ := IsOpenImmersion.lift W.ι ιO hr
    have hℓ : ℓ ≫ W.ι = ιO := IsOpenImmersion.lift_fac _ _ _
    let bO : Sp (M.O z) ⟶ BO.left := pullback.lift (spMap ι' ≫ b) (𝟙 _) (by
      rw [Category.assoc, hb, Category.comp_id, Category.id_comp])
    have hbO : bO ≫ pullback.fst _ _ = spMap ι' ≫ b := pullback.lift_fst _ _ _
    have hbO' : bO ≫ BO.hom = 𝟙 _ := pullback.lift_snd _ _ _
    have hEG : E.hom.left ≫ pullback.fst G.hom ιO ≫ G.hom = BO.hom ≫ ιO := by
      rw [pullback.condition, ← Category.assoc, ← hEw]; rfl
    have hσ : bO ≫ E.hom.left ≫ pullback.fst G.hom ιO = ℓ ≫ h := by
      refine ext_of_isDominant_of_isSeparated G.hom ?_ j ?_
      · rw [Category.assoc, Category.assoc, hEG, ← Category.assoc, hbO', Category.id_comp, Category.assoc, h1, hℓ]
      · have hjb : j ≫ bO = w ≫ a₀ := by
          apply pullback.hom_ext
          · rw [Category.assoc, hbO, Category.assoc, ha₀, hwa, hval, Category.assoc]
          · change j ≫ bO ≫ BO.hom = w ≫ a₀ ≫ BO.hom
            rw [hbO', ha₀', ← Category.assoc, hw, Category.comp_id, Category.id_comp]
        rw [← Category.assoc, hjb, Category.assoc, ← Category.assoc a₀, hE, hψ₀, hwψ, ← Category.assoc]
        exact (h2 _ (by rw [Category.assoc, hℓ]; exact hpt)).symm
    have hxb : x ≫ φO = (x ≫ AK.hom ≫ spMap v) ≫ bO := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφO, hx, Category.assoc, hbO, hyK']
        simp only [Category.assoc]
      · change x ≫ φO ≫ BO.hom = (x ≫ AK.hom ≫ spMap v) ≫ bO ≫ BO.hom
        rw [hφO', hbO', Category.comp_id]
    refine ValAt.unique ?_ hv
    refine ⟨W, h, (x ≫ AK.hom ≫ spMap v) ≫ ℓ, ⟨h1, h2⟩, ?_, ?_⟩
    · rw [Category.assoc, hℓ]
      simp only [Category.assoc, hs]
    · have hxb' : x ≫ φO ≫ E.hom.left ≫ pullback.fst G.hom ιO = ((x ≫ AK.hom ≫ spMap v) ≫ ℓ) ≫ h := by
        rw [← Category.assoc x φO, hxb, Category.assoc, hσ]
        simp only [Category.assoc]
      simpa only [Category.assoc] using hxb'.symm

end GlobalTheory.Poinc.Spread
