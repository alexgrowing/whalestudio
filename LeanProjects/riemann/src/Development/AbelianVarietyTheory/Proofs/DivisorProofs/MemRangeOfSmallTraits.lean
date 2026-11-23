import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCExtComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyFormulaUnitOverNormalBaseOfFamilyUnitOfTraits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInAllCompleteDVRNormalNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfCompatibleRationalLocalUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValuesDetOmegaDeltaUnitAffineOpensStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrSplitExt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven GlobalTheory.MBLow
open scoped CategoryTheory.Obj Cardinal
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.KeySmall

open Cardinal in

theorem mk_adicCompletion_le {D : Type} [CommRing D] (I : Ideal D) (h : #D ≤ 𝔠) : #(AdicCompletion I D) ≤ 𝔠 := by
  have hs : ∀ a : AdicCompletion I D, ∃ s : ℕ → D, ∀ n, a.val n = Submodule.Quotient.mk (s n) := fun a => by
    choose s hs using fun n => Submodule.Quotient.mk_surjective _ (a.val n)
    exact ⟨s, fun n => (hs n).symm⟩
  choose s hs using hs
  have hinj : Function.Injective s := fun a b hab => AdicCompletion.ext fun n => by rw [hs, hs, hab]
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat]
  exact (Cardinal.power_le_power_right h).trans_eq Cardinal.continuum_power_aleph0

open Cardinal in

theorem dvd_of_forall_small : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R],
    #R ≤ 𝔠 → ∀ a b : R, b ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → #V ≤ 𝔠 →
      ∀ φ : R →+* V, Function.Injective φ → φ b ∣ φ a) → b ∣ a := by
  intro R _ _ _ _ _ hR a b hb h
  classical
  by_cases ha : a = 0
  · exact ha ▸ dvd_zero b
  let K := FractionRing R
  obtain ⟨h1, h2, -⟩ := GlobalTheory.normal_domain_height_one.{0, 0, 0} R K
  have hbK : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb
  suffices hmem : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      algebraMap R K a / algebraMap R K b ∈ primeLocalSubalgebra K p by
    obtain ⟨r, hr⟩ := (h2 (algebraMap R K a / algebraMap R K b)).2 hmem
    refine ⟨r, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr, mul_div_cancel₀ _ hbK]
  intro p _ hp
  obtain ⟨-, hD, -⟩ := h1 p hp
  let D := primeLocalSubalgebra K p
  haveI : IsDiscreteValuationRing D := hD
  let W := AdicCompletion (IsLocalRing.maximalIdeal D) D
  let iW : D →+* W := algebraMap D W
  let φ : R →+* W := iW.comp (algebraMap R D)
  have hRD : Function.Injective (algebraMap R D) := fun x y hxy =>
    IsFractionRing.injective R K (congrArg Subtype.val hxy)
  have hφ : Function.Injective φ := (algebraMap_adicCompletion_injective_of_dvr D).comp hRD
  haveI : CharZero W := (RingHom.charZero_iff hφ).1 inferInstance
  have hW : GlobalTheory.LN.CDvr W := ⟨inferInstance, inferInstance, inferInstance⟩
  have hcD : #D ≤ 𝔠 := by
    refine (Cardinal.mk_le_of_injective (f := fun d : D => (d : K)) Subtype.val_injective).trans ?_
    rw [Cardinal.mk_fractionRing]; exact hR
  obtain ⟨t, ht⟩ := h W hW (mk_adicCompletion_le _ hcD) φ hφ
  have hdvd : algebraMap R D b ∣ algebraMap R D a := by
    rcases ValuationRing.dvd_total (algebraMap R D b) (algebraMap R D a) with hd | ⟨c, hc⟩
    · exact hd
    have ha' : φ a ≠ 0 := (map_ne_zero_iff _ hφ).mpr ha
    have e : φ a * (iW c * t) = φ a * 1 := by
      rw [_root_.mul_one]
      calc φ a * (iW c * t) = iW (algebraMap R D a * c) * t := by
            rw [map_mul, _root_.mul_assoc]; rfl
        _ = φ a := by rw [← hc]; exact ht.symm
    have hu : IsUnit (iW c) := isUnit_iff_exists_inv.mpr ⟨t, mul_left_cancel₀ ha' e⟩
    obtain ⟨u, rfl⟩ := isUnit_of_map_unit iW c hu
    exact ⟨↑u⁻¹, by rw [hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩
  obtain ⟨c, hc⟩ := hdvd
  have hcK : algebraMap R K a = algebraMap R K b * (c : K) := congrArg Subtype.val hc
  rw [hcK, mul_div_cancel_left₀ _ hbK]
  exact c.2

theorem dvd_of_map_dvd {V W : Type} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing W] [IsDomain W] (g : V →+* W)
    [IsLocalHom g] (hg : Function.Injective g) {a b : V} (h : g b ∣ g a) : b ∣ a := by
  by_cases ha : a = 0
  · exact ha ▸ dvd_zero b
  obtain ⟨t, ht⟩ := h
  rcases ValuationRing.dvd_total b a with hd | ⟨c, hc⟩
  · exact hd
  have ha' : g a ≠ 0 := (map_ne_zero_iff _ hg).mpr ha
  have e : g a * (g c * t) = g a * 1 := by
    rw [_root_.mul_one, ← _root_.mul_assoc, ← map_mul, ← hc]
    exact ht.symm
  have hu : IsUnit (g c) := isUnit_iff_exists_inv.mpr ⟨t, mul_left_cancel₀ ha' e⟩
  obtain ⟨u, rfl⟩ := isUnit_of_map_unit g c hu
  exact ⟨↑u⁻¹, by rw [hc, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]⟩

open Cardinal in

theorem mem_range_of_small_traits {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A]
    (hA : #A ≤ 𝔠) (f : A) (hf : f ≠ 0) (b : Localization.Away f)
    (H : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → #V ≤ 𝔠 →
      ∀ (t : A →+* V), Function.Injective t → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (g : V →+* W),
        Function.Injective g ∧ IsLocalHom g ∧ ∀ h : Localization.Away f →+* FractionRing W,
        h.comp (algebraMap A _) = (algebraMap W (FractionRing W)).comp (g.comp t) →
        ∃ w : W, h b = algebraMap W (FractionRing W) w) :
    ∃ c : A, algebraMap A (Localization.Away f) c = b := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) b
  obtain ⟨n, hn⟩ := s.2
  have hdiv : f ^ n ∣ a := by
    refine dvd_of_forall_small A hA a (f ^ n) (pow_ne_zero n hf) ?_
    intro V _ _ _ hc hV t ht
    obtain ⟨W, _, _, g, hg, hgl, HW⟩ := H V hc hV t ht
    obtain ⟨hd, -, -⟩ := (GlobalTheory.LN.cDvr_iff V).1 hc
    refine dvd_of_map_dvd g hg ?_
    have htf : (g.comp t) f ≠ 0 := (map_ne_zero_iff (g.comp t) (fun a b e => ht (hg e))).2 hf
    have hinjV := IsFractionRing.injective W (FractionRing W)
    have hu : IsUnit (((algebraMap W (FractionRing W)).comp (g.comp t)) f) :=
      isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinjV).2 htf)
    have hcomp := IsLocalization.Away.lift_comp (S := Localization.Away f) f hu
    obtain ⟨w, hw⟩ := HW _ hcomp
    have e := congrArg (IsLocalization.Away.lift (S := Localization.Away f) f hu) hs
    rw [map_mul, hw, ← RingHom.comp_apply, hcomp, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
      RingHom.comp_apply (algebraMap W (FractionRing W)), ← map_mul] at e
    have e' := hinjV e
    refine ⟨w, ?_⟩
    change (g.comp t) a = (g.comp t) (f ^ n) * w
    rw [← e', ← hn, mul_comm]
  obtain ⟨c, hc⟩ := hdiv
  refine ⟨c, ?_⟩
  have hsu : IsUnit (algebraMap A (Localization.Away f) (s : A)) := IsLocalization.map_units _ s
  have hn' : (s : A) = f ^ n := hn.symm
  rw [hc, map_mul] at hs
  refine (hsu.mul_left_inj).1 ?_
  rw [hs, hn', mul_comm]

theorem polAt_of_fibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (g : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) (h : PolFib t.G t.PP.L g x) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨P, α, -, hc, hL⟩ := h
  have g₁ := isGrpPullback_pullback t.G x
  have w : pullback.fst t.G.hom x ≫ t.G.hom = (pullback.snd t.G.hom x ≫ 𝟙 _) ≫ x := by
    rw [Category.comp_id]; exact pullback.condition
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ P.A.left,
      ψ ≫ α = pullback.fst t.G.hom x ∧ ψ ≫ P.A.hom = pullback.snd t.G.hom x ≫ 𝟙 _ :=
    ⟨_, hc.1.lift_fst _ _ w, hc.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback ((Over.pullback x).obj t.G) P.A (𝟙 _) ψ :=
    hc.cancel (g₁.congr (Category.id_comp _).symm h₁.symm) h₂
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom x)
  have e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (P.L.pull ψ) :=
    (GlobalTheory.LN.GenericPoint.lbIso_pull hL ψ h₁.symm).symm
  have hq := amplePt (Sp K) K (𝟙 _) P.A ((Over.pullback x).obj t.G) ψ g₂ P.L
    (t.PP.L.pull (pullback.fst t.G.hom x)) P.isLB hM e P.ample P.ktriv
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) g₂.1 P.isAb.proper, hq.1, hq.2⟩

section Triples

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def pullT {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : SAB H S' :=
  (fun {t' : SAB H S'} (_ : SABMap t' t f) => t')
    (sabPull Out.CubePf.cubePull f t).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

theorem pullT_map {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ m : SABMap (pullT f t) t f, m.φ = pullback.fst t.G.hom f :=
  (sabPull Out.CubePf.cubePull f t).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

theorem pullT_iso {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) {L : LB t.G.left} (hL : L.IsLB) (h : LBIso t.PP.L L)
    {L' : LB ((Over.pullback f).obj t.G).left} (hL' : L'.IsLB) (h' : LBIso (L.pull (pullback.fst t.G.hom f)) L') :
    LBIso (X := ((Over.pullback f).obj t.G).left) (pullT f t).PP.L L' := by
  obtain ⟨m, hm⟩ := pullT_map f t
  have e : LBIso (X := ((Over.pullback f).obj t.G).left) (pullT f t).PP.L (t.PP.L.pull (pullback.fst t.G.hom f)) := by
    rw [← hm]
    exact GlobalTheory.ModelSum.lbIso_of_map m
  have e' : LBIso (t.PP.L.pull (pullback.fst t.G.hom f)) (L.pull (pullback.fst t.G.hom f)) :=
    (CechPic.cls_eq_iff (pull_isLB t.PP.isLB _) (pull_isLB hL _)).1 (by
      rw [CechPic.cls_pull t.PP.isLB, CechPic.cls_pull hL, (CechPic.cls_eq_iff t.PP.isLB hL).2 h])
  have i₀ : LB.IsLB (X := ((Over.pullback f).obj t.G).left) (pullT f t).PP.L := (pullT f t).PP.isLB
  have i₁ := pull_isLB t.PP.isLB (pullback.fst t.G.hom f)
  have i₂ := pull_isLB hL (pullback.fst t.G.hom f)
  have e'' := LBIso.trans i₁ i₂ hL' e' h'
  exact LBIso.trans i₀ i₁ hL' e e''

open Cardinal in

theorem key_unit_split (κ : Rule) (hR : Rule4 κ) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W]
    (hc : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (hW : #W ≤ 𝔠) (t : SAB H (Sp W))
    (hS : ∃ E' : SplitExt (Sp (IsLocalRing.ResidueField W)),
      E'.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj t.G))
    (L : RigLB t.G) (hL : LBIso t.PP.L L.L) (σ : L.L.Sec) (x : KeyIn (FractionRing W)) (y : Fin x.P.g → (epsR W ⟶ t.G))
    (hy : IsLieBasis y) (hσ : NzFib σ) (hk : KeyOn (algebraMap W (FractionRing W)) x t.G L σ y) :
    ∃ u : Wˣ, (κ (FractionRing W) x : FractionRing W) = algebraMap W (FractionRing W) u := by
  have hk0 := hk
  obtain ⟨φ, -, ψ, -, hpb, hψ, -⟩ := hk
  have e₁ : LBIso x.P.L (L.L.pull φ) := ⟨ψ, hψ⟩
  have e₂ : LBIso x.P.L (t.PP.L.pull φ) :=
    (CechPic.cls_eq_iff x.P.isLB (pull_isLB t.PP.isLB _)).1 (by
      rw [(CechPic.cls_eq_iff x.P.isLB (pull_isLB L.isLB φ)).2 e₁, CechPic.cls_pull t.PP.isLB, CechPic.cls_pull L.isLB,
        (CechPic.cls_eq_iff t.PP.isLB L.isLB).2 hL])
  have hp : GlobalTheory.LN.PolAt t (jK W) := polAt_of_fibre t x.P.g _ ⟨x.P, φ, rfl, hpb, e₂⟩
  have hW' : GlobalTheory.LN.CDvr W := (GlobalTheory.LN.cDvr_iff W).2 ⟨inferInstance, hc, inferInstance⟩
  obtain ⟨U, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W hW' t hp hS
  exact key_unit_trait κ hR W hc hW t.G L σ x y t.semi ⟨U.D, U.A, U.U, by rw [U.bundle]; exact hL⟩ hy hσ hk0

open Cardinal in

theorem key_unit_normal (κ : Rule) (hR : Rule4 κ) (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [CharZero A] (hA : #A ≤ 𝔠) (t : SAB H (Sp A)) (L : RigLB t.G) (hL : LBIso t.PP.L L.L)
    (σ : L.L.Sec) (x : KeyIn (FractionRing A)) (y : Fin x.P.g → (epsR A ⟶ t.G))
    (hsm : SmoothOfRelativeDimension x.P.g t.G.hom) (hopen : IsOpen (abLocus t.G)) (hsym : L.IsSymmetric)
    (hpol : PolOnAb t.G L.L) (hy : IsLieBasis y) (hσ : NzFib σ)
    (hkey : KeyOn (algebraMap A (FractionRing A)) x t.G L σ y) :
    ∃ u : Aˣ, (κ (FractionRing A) x : FractionRing A) = algebraMap A (FractionRing A) u := by
  have hkey0 := hkey
  obtain ⟨φ, -, -, -, hpb, -⟩ := hkey
  haveI : IsProper x.P.A.hom := x.P.isAb.proper
  have hab := GlobalTheory.range_subset_abLocus_of_isProper t.semi hpb.1
  obtain ⟨f, hf0, hfab⟩ := LocPf.exists_away_subset (abLocus t.G) hopen hab
  have hle : Submonoid.powers f ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing (Localization.Away f) :=
    IsLocalization.isNoetherianRing (Submonoid.powers f) (Localization.Away f) inferInstance
  haveI : IsIntegrallyClosed (Localization.Away f) :=
    isIntegrallyClosed_of_isLocalization (Localization.Away f) (Submonoid.powers f) hle
  have hinj : Function.Injective (algebraMap A (Localization.Away f)) := IsLocalization.injective _ hle
  haveI : CharZero (Localization.Away f) := charZero_of_injective_algebraMap hinj
  obtain ⟨xB, hgB, hkB⟩ := GlobalTheory.T.exists_keyDatum_abelianLocus_point A (Localization.Away f) (algebraMap A _) t.G L σ x.P.g y x.g_pos t.semi hsm hopen
    hsym hpol hy hσ hfab
  obtain ⟨u, hu⟩ := hR.2.2.2 (Localization.Away f) xB
  have hfu : IsUnit ((algebraMap A (FractionRing A)) f) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hf0)
  have hc := IsLocalization.Away.lift_comp (S := Localization.Away f) f hfu
  have hpbx : KeyPB x xB (IsLocalization.Away.lift (S := Localization.Away f) f hfu) :=
    GlobalTheory.T.keyDatum_fibre_of_composable_baseChange A (Localization.Away f) (FractionRing A) (algebraMap A _) _ t.G L σ x.P.g y xB x hgB rfl hkB
      (by rw [hc]; exact hkey0)
  have hval := hu _ _ x hpbx
  have trait : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → #V ≤ 𝔠 →
      ∀ (a : A →+* V), Function.Injective a → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (g : V →+* W),
        Function.Injective g ∧ IsLocalHom g ∧ ∀ h : Localization.Away f →+* FractionRing W,
        h.comp (algebraMap A _) = (algebraMap W (FractionRing W)).comp (g.comp a) →
        ∃ w : Wˣ, h u = algebraMap W (FractionRing W) w := by
    intro V _ _ _ hV hcV a ha
    obtain ⟨hd, hcomp, h0⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
    haveI := hd
    haveI := h0
    obtain ⟨W, _, _, _, _, g, hcW, hgi, hginj, hgl, Ex, hEx⟩ :=
      GlobalTheory.SplitExtDVR.exists_complete_dvr_split_ext V hcomp (pullT (spMap a) t).G (pullT (spMap a) t).semi
    refine ⟨W, inferInstance, inferInstance, g, hginj, hgl, fun h hh => ?_⟩
    have hW : #W ≤ 𝔠 := by
      letI := g.toAlgebra
      haveI : Algebra.IsIntegral V W := ⟨hgi⟩
      haveI : Module.IsTorsionFree V W := Module.isTorsionFree_iff_algebraMap_injective.2 hginj
      exact (Algebra.IsAlgebraic.cardinalMk_le_max V W).trans (max_le hcV aleph0_le_continuum)
    have hrange : Set.range (spMap ((algebraMap W (FractionRing W)).comp (g.comp a))) ⊆ abLocus t.G := by
      rw [← hh]
      rintro _ ⟨p, rfl⟩
      exact hfab ⟨spMap h p, rfl⟩
    obtain ⟨xV, hgV, hkV⟩ := GlobalTheory.T.exists_keyDatum_abelianLocus_point A (FractionRing W) ((algebraMap W _).comp (g.comp a)) t.G L σ x.P.g y x.g_pos
      t.semi hsm hopen hsym hpol hy hσ hrange
    have hpbV : KeyPB xV xB h :=
      GlobalTheory.T.keyDatum_fibre_of_composable_baseChange A (Localization.Away f) (FractionRing W) (algebraMap A _) h t.G L σ x.P.g y xB xV hgB hgV hkB
        (by rw [hh]; exact hkV)
    have hvalV := hu _ h xV hpbV
    haveI : IsCommMonObj ((Over.pullback (spMap a)).obj t.G) := (pullT (spMap a) t).comm
    obtain ⟨L₁, σ₁, y₁, hiso₁, hy₁, hσ₁, hk₁⟩ := GlobalTheory.T.keyDatum_pullback_baseChange_lieBasis A V (FractionRing W) a ((algebraMap W _).comp g) t.G L σ xV
      (fun i => y (i.cast hgV)) t.semi (LocPf.isLieBasis_cast hgV y hy) hσ hkV
    have e₁ := pullT_iso (spMap a) t L.isLB hL L₁.isLB hiso₁
    haveI : IsCommMonObj ((Over.pullback (spMap g)).obj ((Over.pullback (spMap a)).obj t.G)) :=
      (pullT (spMap g) (pullT (spMap a) t)).comm
    obtain ⟨L₂, σ₂, y₂, hiso₂, hy₂, hσ₂, hk₂⟩ := GlobalTheory.T.keyDatum_pullback_baseChange_lieBasis V W (FractionRing W) g (algebraMap W _)
      ((Over.pullback (spMap a)).obj t.G) L₁ σ₁ xV y₁ (pullT (spMap a) t).semi hy₁ hσ₁ hk₁
    have e₂ := pullT_iso (spMap g) (pullT (spMap a) t) L₁.isLB e₁ L₂.isLB hiso₂
    obtain ⟨w, hw⟩ := key_unit_split κ hR W hcW hW (pullT (spMap g) (pullT (spMap a) t)) ⟨Ex, hEx⟩ L₂ e₂ σ₂ xV y₂ hy₂
      hσ₂ hk₂
    exact ⟨w, hvalV.symm.trans hw⟩
  obtain ⟨c, hcu⟩ := mem_range_of_small_traits hA f hf0 (u : Localization.Away f) (fun V _ _ _ hV hcV a ha => by
    obtain ⟨W, _, _, g, h1, h2, h3⟩ := trait V hV hcV a ha
    refine ⟨W, inferInstance, inferInstance, g, h1, h2, fun h hh => ?_⟩
    obtain ⟨w, hw⟩ := h3 h hh
    exact ⟨w, hw⟩)
  obtain ⟨c', hcu'⟩ := mem_range_of_small_traits hA f hf0 ((u⁻¹ : (Localization.Away f)ˣ) : Localization.Away f)
    (fun V _ _ _ hV hcV a ha => by
      obtain ⟨W, _, _, g, h1, h2, h3⟩ := trait V hV hcV a ha
      refine ⟨W, inferInstance, inferInstance, g, h1, h2, fun h hh => ?_⟩
      obtain ⟨w, hw⟩ := h3 h hh
      refine ⟨((w⁻¹ : Wˣ) : W), ?_⟩
      rw [map_units_inv, map_units_inv, hw])
  have hcc : c * c' = 1 := hinj (by rw [map_mul, hcu, hcu', Units.mul_inv, map_one])
  refine ⟨⟨c, c', hcc, by rw [mul_comm]; exact hcc⟩, ?_⟩
  rw [hval, Units.val_mk, ← hcu, ← RingHom.comp_apply, hc]

end Triples

theorem lbPow_U' {S : Scheme.{0}} (M : LB S) (n : ℕ) (j : (lbPow M n).ι) : (lbPow M n).U j = M.U (j PUnit.unit) := by
  ext x
  simp only [lbPow, LB.LinComb, LB.wchart]
  simp
  exact ⟨fun h => h _, fun h i => h⟩

theorem germ_lbPow_g' {S : Scheme.{0}} (M : LB S) (n : ℕ) (j j' : (lbPow M n).ι) (x : S)
    (h : x ∈ (lbPow M n).U j ⊓ (lbPow M n).U j') (h' : x ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)) :
    S.presheaf.germ _ x h ((lbPow M n).g j j' : Γ(S, (lbPow M n).U j ⊓ (lbPow M n).U j')) =
      S.presheaf.germ _ x h' (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(S, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) ^ n := by
  simp only [lbPow, LB.LinComb, Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  congr 1
  simp [res, pullU]
  erw [map_pow]
  congr 1
  erw [Units.coe_map, Units.coe_map]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

open Cardinal in

theorem key_sab {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (S : Scheme.{0}) [IsIntegral S]
    (t : SAB H S) (g : ℕ) (δ : LB S) (σ : (CechPic.tens t.PP.L (δ.pull t.G.hom)).Sec) (hg : 1 ≤ g)
    (hN : Geo.Tor.IsNormalScheme S) (hn : IsLocallyNoetherian S) (h0 : CharZero Γ(S, ⊤))
    (hsmall : ∀ (A : Type) [CommRing A] (ξ : Sp A ⟶ S), IsOpenImmersion ξ → #A ≤ 𝔠)
    (hsm : SmoothOfRelativeDimension g t.G.hom) (hne : (abLocus t.G).Nonempty) (hop : IsOpen (abLocus t.G))
    (hδ : δ.IsLB) (hpol : PolOnAb t.G t.PP.L) (hnz : NzFib σ) :
    LBIso (lbPow δ 8) (lbPow (GlobalTheory.SiegelTor.hodge t.G g) 4) := by
  obtain ⟨κ, hH, hF, -, hT, -, hU, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  have h4 : Rule4 κ := ⟨hH, hF, hT, hU⟩
  obtain ⟨f, hloc, hcomp⟩ := GlobalTheory.T.keyValues_detOmega_delta_unit_affineOpens κ hH hF S t.G g t.PP δ σ hg hN hn h0 t.semi hsm hne hop t.sym hδ hpol hnz
    (fun A _ _ _ _ _ ξ hξ _ L' σ' x y hiso hsm' hop' hsym' hpol' hy hσ' hk =>
      key_unit_normal κ h4 A (hsmall A ξ hξ) (pullT ξ t) L'
        (pullT_iso ξ t t.PP.isLB (PolBaseChange.lbIso_refl t.PP.isLB) L'.isLB hiso) σ' x y hsm' hop' hsym' hpol' hy hσ' hk)
  refine GlobalTheory.GlueRat.lbIso_of_rat S (lbPow δ 8) (lbPow (SiegelTor.hodge t.G g) 4) (fun p => f (p.1 PUnit.unit) (p.2 PUnit.unit)) ?_ ?_
  · rintro ⟨c, i⟩ x hx
    rw [lbPow_U', lbPow_U'] at hx
    obtain ⟨V, hV, hxV, u, hu⟩ := hloc _ _ x hx
    exact ⟨V, by rw [lbPow_U', lbPow_U']; exact hV, hxV, u, hu⟩
  · rintro ⟨c, i⟩ ⟨c', i'⟩ h1 h2
    have h1' : genericPoint S ∈ (VB.det (LieVB.omega t.G) g).U (c PUnit.unit) ⊓ (VB.det (LieVB.omega t.G) g).U (c' PUnit.unit) := by
      rw [lbPow_U', lbPow_U'] at h1; exact h1
    have h2' : genericPoint S ∈ δ.U (i PUnit.unit) ⊓ δ.U (i' PUnit.unit) := by
      rw [lbPow_U', lbPow_U'] at h2; exact h2
    dsimp only
    rw [germ_lbPow_g' δ 8 i i' _ h2 h2', germ_lbPow_g' _ 4 c c' _ h1 h1']
    exact hcomp _ _ _ _ h1' h2'

theorem cls_eq_zero_of_chart {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) (i₀ : L.ι) (h : L.U i₀ = ⊤) :
    CechPic.cls L hL = 0 := by
  have le : ∀ j, L.U j ≤ L.U j ⊓ L.U i₀ := fun j => le_inf le_rfl (h ▸ le_top)
  have hm : ∀ y : Z, y ∈ L.U i₀ := fun y => h ▸ TopologicalSpace.Opens.mem_top y
  exact (CechPic.cls_eq_zero_iff hL).2 ⟨⟨fun j => res (le j) (L.g j i₀)⟩, fun i j => unit_ext fun y hy => by
      rw [map_mul, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy.1, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy.2]
      exact (gm_cocycle hL (𝟙 Z) y hy.1 hy.2 (hm y)).symm⟩

theorem cls_O1_zero (o : Type) [CommRing o] : CechPic.cls _ (ProjSpace.O1_isLB o 0) = 0 := by
  refine cls_eq_zero_of_chart _ (0 : Fin 1) (top_le_iff.1 fun x _ => ?_)
  obtain ⟨i, hi⟩ := Semi.LB.mem_of_cover (ProjSpace.O1_isLB o 0) x
  obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  exact hi

theorem cls_det_zero {X : Scheme.{0}} (F : X.Modules) (h : (VB.det F 0).IsLB) : CechPic.cls _ h = 0 := by
  refine (CechPic.cls_eq_zero_iff h).2 ⟨⟨fun _ => 1⟩, fun c c' => ?_⟩
  have e : (VB.det F 0).g c c' = 1 := Units.ext (by
    refine (VB.IsFrame.val_detUnit c.isFrame c'.isFrame inf_le_left inf_le_right).trans ?_
    rw [Module.Basis.det_apply, Matrix.det_isEmpty]
    rfl)
  simp [e]

open Cardinal in

theorem mk_le_of_lft {k A : Type} [Field k] [CommRing A] (hk : #k ≤ 𝔠) (s : Sp A ⟶ Sp k) [LocallyOfFiniteType s] :
    #A ≤ 𝔠 := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have hft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 ‹_›
  letI := φ.hom.toAlgebra
  obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 (show Algebra.FiniteType k A from hft)
  refine (Cardinal.mk_le_of_surjective hp).trans (MvPolynomial.cardinalMk_le_max.trans ?_)
  exact max_le (max_le hk ((Cardinal.lt_aleph0_of_finite _).le.trans aleph0_le_continuum)) aleph0_le_continuum

theorem nzFib_of_geom {S : Scheme.{0}} {G : Over S} {L : LB G.left} (σ : L.Sec)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), ∃ (y : Sp K ⟶ G.left) (j : L.ι), y ≫ G.hom = x ∧
      Set.range y ⊆ L.U j ∧ valF y _ (σ.f j) ≠ 0) : NzFib σ := by
  intro s
  let K := AlgebraicClosure (S.residueField s)
  obtain ⟨y, j, hy, hj, hv⟩ := h K (spMap (algebraMap (S.residueField s) K) ≫ S.fromSpecResidueField s)
  let q : Sp K := IsLocalRing.closedPoint K
  refine ⟨y q, ?_, TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩⟩
  · rw [← Scheme.Hom.comp_apply, hy, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  · have hle : ⊤ ≤ y ⁻¹ᵁ L.U j := fun z _ => hj ⟨z, rfl⟩
    rw [valF, dif_pos hle] at hv
    have hu : IsUnit ((y.appLE (L.U j) ⊤ hle).hom (σ.f j)) :=
      (isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv _).1 (isUnit_iff_ne_zero.2 hv)
    have hb := (Sp K).basicOpen_of_isUnit hu
    rw [Scheme.basicOpen_appLE] at hb
    have : q ∈ (⊤ ⊓ y ⁻¹ᵁ G.left.basicOpen (σ.f j) : (Sp K).Opens) := by rw [hb]; trivial
    exact this.2

end GlobalTheory.UMin.KeySmall
