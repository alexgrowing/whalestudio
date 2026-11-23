import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEndOfEighthPowerOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationModelFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithBaseFiniteContainingRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelNormalisationDedekind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsFiniteOverProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealisedThetaSystemOfUniversalSectionBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowerGaloisExtSymplecticLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosureFiniteGaloisStableThetaRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelExtendsNoetherianNormalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationSectionBasisPullbackAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaRealisationLabelsOfGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaRealisationLabelPermOfRingEndoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRealisationLabelsInjectiveOfGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

noncomputable section

namespace GlobalTheory.GSep.UTower

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem lbIso_pull_comp_of_eq {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M j j rfl)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem isMonHom_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) (e : G ⟶ G) [IsMonHom e] (e' : G' ⟶ G')
    (he : e'.left ≫ φ = φ ≫ e.left) : IsMonHom e' := by
  have push_comp : ∀ {T₁ : Over S'} (x : T₁ ⟶ G'), pushPt hφ.1.w (x ≫ e') = pushPt hφ.1.w x ≫ e :=
    fun x => Over.OverMorphism.ext (by
      show (x.left ≫ e'.left) ≫ φ = (x.left ≫ φ) ≫ e.left
      rw [Category.assoc, he, Category.assoc])
  have pm : ∀ {T₁ : Over S'} (x y : T₁ ⟶ G'), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have inj : ∀ {T₁ : Over S'} {x y : T₁ ⟶ G'}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y :=
    fun h => GlobalTheory.SiegelPull.push_injective hφ _ h
  refine isMonHom_of_mul _ fun T₁ x y => inj ?_
  rw [push_comp, pm, pm, push_comp, push_comp]
  exact MonObj.mul_comp _ _ _

theorem deep_of_uLink : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → GlobalTheory.GSep.Deep X₁ act := by
  intro E _ _ _ H Dw _ l Xo c C X₁ act u π hU N₀
  have hact : IsAct X₁ act := hU.1
  have hℓp : X₁.ρ.n.Prime := X₁.ρ.n_prime
  have hℓ2 : 2 ≤ X₁.ρ.n := hℓp.two_le
  obtain ⟨j₁, hj₁, hr⟩ := X₁.ρ.r_eq
  have hL₁ : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) := by
    rw [hr, X₁.ρ.N_eq, ← pow_mul, ← pow_add, mul_comm X₁.ρ.k 2]
  obtain ⟨k, j₀, hk, hBk, hj₀, big⟩ := GlobalTheory.Poinc.GSetup.exists_big_ge X₁.ρ.P.g X₁.ρ.n hℓ2 N₀
  have hun1 : IsUnit (X₁.ρ.n : X₁.o₁) := by
    have hd : X₁.ρ.n ∣ X₁.S.r * X₁.S.N := by
      rw [hL₁]; exact dvd_pow_self _ (by omega)
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) X₁.S.unit
  haveI : CharZero X₁.Ω₁ := ArithBase.char (o := X₁.o₁)
  have hM : 0 < X₁.S.r * X₁.S.N := by rw [hL₁]; exact pow_pos hℓp.pos _
  have hζ₀ : ∃ ζ₀ : X₁.Ω₁, IsPrimitiveRoot ζ₀ (X₁.S.r * X₁.S.N) :=
    ⟨_, (X₁.S.prim.pow (by positivity) (sq _)).map_of_injective (ArithBase.inj (o := X₁.o₁) (Ω := X₁.Ω₁))⟩
  have htors : ∀ (E : Type) [Field E] [IsAlgClosed E] (x : Sp E ⟶ Sp X₁.S.R) (z : Over.mk x ⟶ X₁.ρ.P.A),
      z ^ (X₁.S.r * X₁.S.N) = 1 → ∃ y : baseOver (Sp X₁.S.R) ⟶ X₁.ρ.P.A,
        (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp X₁.S.R)) ≫ y = z := by
    intro E _ _ x z hz
    obtain ⟨a, ha, -⟩ := X₁.ρ.pt_bij E x z hz
    exact ⟨_, ha⟩
  set j := j₀ + (j₁ + 2 * X₁.ρ.k) with hj
  set K := (X₁.ρ.n ^ j * (X₁.ρ.n ^ k) ^ 2) ^ 2 with hK
  have hKpos : 0 < K := by have := hℓp.pos; positivity
  obtain ⟨Ω₂, _, _, Q, φQ, ζ, fd, gal, -, hζ, hQg, hQpb, hQlb, ⟨levQ⟩⟩ :=
    GlobalTheory.T.exists_primePower_galois_ext_symplecticLevel X₁.S.R.val.toRingHom X₁.ρ.P X₁.ρ.n (X₁.S.r * X₁.S.N) K hℓp hM
      (by rw [hL₁]; exact dvd_pow_self _ (by omega)) ⟨2 * (j + 2 * k), by rw [hK]; ring⟩ hζ₀ htors
  haveI := fd
  obtain ⟨o₂, _, _, _, κ, ze, hκ, hc, hze⟩ :=
    GlobalTheory.Poinc.exists_arithBase_rootOfUnity (o₁ := X₁.o₁) (Ω₁ := X₁.Ω₁) Ω₂ K ζ hKpos hζ
  haveI : CharZero Ω₂ := ArithBase.char (o := o₂)
  obtain ⟨R, h, hfg, hfr, hh, hfin, hic, hstab⟩ := GlobalTheory.T.exists_integralClosure_finite_galoisStable_thetaRing X₁.S.R X₁.S.fg X₁.S.frac κ hκ hc
  haveI := GlobalTheory.ThetaReal.isNoetherian_of_fg hfg
  haveI := GlobalTheory.GenSpread.isFractionRing_of_forall_div hfr
  have hun2 : IsUnit (X₁.ρ.n : o₂) := by simpa using hun1.map κ
  have hKunit : IsUnit (K : R) := by
    have := (hun2.map (algebraMap o₂ R))
    rw [map_natCast] at this
    rw [hK]; push_cast
    exact ((this.pow _).mul ((this.pow _).pow _)).pow _
  let zeR : (↥R)ˣ := Units.map (algebraMap o₂ R).toMonoidHom ze
  have hzeR : Units.map (algebraMap R Ω₂).toMonoidHom zeR = ζ := by
    rw [← hze]; ext; rfl
  have hQpb' : IsGrpPullback Q.A X₁.ρ.P.A (spMap ((algebraMap R Ω₂).comp h)) φQ := by
    have e : (algebraMap R Ω₂).comp h = (algebraMap X₁.Ω₁ Ω₂).comp X₁.S.R.val.toRingHom := RingHom.ext hh
    rw [e]; exact hQpb
  obtain ⟨P, ψ, hPg, hpb, hlb, ⟨lev⟩⟩ := GlobalTheory.T.symplecticLevel_extends_noetherian_normalDomain X₁.ρ.P R Ω₂ h Q φQ K zeR hKpos hKunit hQg hQpb' hQlb
    ⟨by rw [hzeR]; exact levQ⟩
  have hS := GlobalTheory.Poinc.hypS_polAV_pullback X₁.ρ.P P (spMap h) ψ hpb hlb X₁.ρ.hypS
  obtain ⟨th, hth⟩ := GlobalTheory.T.exists_polarization_sectionBasis_pullback_affine X₁.ρ.P P h ψ hpb hlb X₁.ρ.th₁ X₁.ρ.th₁_basis
  obtain ⟨S₂, ρ₂, hR, φ₂, hSR, -, -, hN₂, hr₂, hg₂, hpb₂, hlb₂⟩ :=
    GlobalTheory.T.exists_realisedThetaSystem_of_universalSectionBasis o₂ Ω₂ R hfg hfr P X₁.ρ.n k j ze hℓp X₁.ρ.n_odd hk (by omega) hun2 hS th hth lev
  set om : X₁.S.R →+* S₂.R := (Subalgebra.inclusion hR).toRingHom.comp h with hom
  have hval : ∀ a, ((om a : S₂.R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a := fun a => hh a
  have hcart : IsGrpPullback ρ₂.P.A X₁.ρ.P.A (spMap om) (φ₂ ≫ ψ) := by
    rw [hom, ← spMap_comp_ring]
    exact hpb₂.comp hpb
  have hlbc : LBIso ρ₂.P.L (X₁.ρ.P.L.pull (φ₂ ≫ ψ)) :=
    LBIso.trans ρ₂.P.isLB (pull_isLB P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hlb₂ (lbIso_pull_comp_of_eq hlb φ₂ rfl)

  have hφp := hcart.1
  have wε : ∀ a, ((φ₂ ≫ ψ) ≫ (act a).left) ≫ X₁.ρ.P.A.hom = ρ₂.P.A.hom ≫ spMap om := fun a => by
    rw [Category.assoc, Over.w, hφp.w]
  let act₂ : 𝓞 E → (ρ₂.P.A ⟶ ρ₂.P.A) := fun a =>
    Over.homMk (hφp.lift ((φ₂ ≫ ψ) ≫ (act a).left) ρ₂.P.A.hom (wε a)) (hφp.lift_snd _ _ _)
  have hact₂ : ∀ a, (act₂ a).left ≫ (φ₂ ≫ ψ) = (φ₂ ≫ ψ) ≫ (act a).left := fun a => hφp.lift_fst _ _ _
  have hmon : ∀ a, IsMonHom (act₂ a) := fun a => by
    haveI := hact a
    exact isMonHom_of_isGrpPullback hcart (act a) (act₂ a) (hact₂ a)

  haveI : IsDedekindDomain X₁.o₁ := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
  have hp : (spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt) ≫ X₁.M.s = spMap ((algebraMap o₂ Ω₂).comp κ) := by
    rw [Category.assoc, X₁.M.pt_s, hc]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap X₁.o₁ X₁.Ω₁))
      (CommRingCat.ofHom (algebraMap X₁.Ω₁ Ω₂))).symm
  have hst : ((spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt).stalkMap (genericPoint (Sp Ω₂))).hom.Finite := by
    rw [Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (GlobalTheory.Poinc.stalkMap_spMap_finite _ (RingHom.finite_algebraMap.2 inferInstance) _)
      (RingHom.Finite.of_surjective _ (GlobalTheory.Poinc.RatModel.stalkMap_pt_surjective X₁.M _))
  obtain ⟨M₂, q, hMn, hq, hqgen⟩ := GlobalTheory.Poinc.exists_ratModel_normalization X₁.o₁ o₂ Ω₂ κ hκ X₁.M.Z X₁.M.s X₁.M.lft
    X₁.M.qc X₁.M.sep _ hp hst
  have hs : M₂.s ≫ spMap κ = q ≫ X₁.M.s := by
    refine ext_of_isDominant M₂.pt ?_
    rw [← Category.assoc, M₂.pt_s, spMap_comp_ring, ← Category.assoc, hqgen, hp]
  have hproj : IsProjOver M₂.s :=
    GlobalTheory.T.isProjOver_of_isFinite_over_projective X₁.o₁ o₂ κ M₂.Z X₁.M.Z X₁.M.s q M₂.s X₁.projM hq inferInstance hs

  have hrat : ∀ x : ratHull X₁.S.R, algebraMap X₁.Ω₁ Ω₂ (x : X₁.Ω₁) ∈ ratHull S₂.R := fun x => by
    obtain ⟨n, hn, hx⟩ := mem_ratHull.1 x.2
    refine mem_ratHull.2 ⟨n, hn, ?_⟩
    have h₀ := (om ⟨_, hx⟩).2
    rw [hval] at h₀
    simpa using h₀
  let rh : ratHull X₁.S.R →+* ratHull S₂.R :=
    ((algebraMap X₁.Ω₁ Ω₂).comp (ratHull X₁.S.R).val.toRingHom).codRestrict (ratHull S₂.R) hrat
  have hrv : spMap (ratHull S₂.R).val.toRingHom ≫ spMap rh =
      spMap (algebraMap X₁.Ω₁ Ω₂) ≫ spMap (ratHull X₁.S.R).val.toRingHom := by
    rw [spMap_comp_ring, spMap_comp_ring]
    rfl
  have hUO₂ : UOver Xo c ρ₂.P (toRat S₂.R) (spMap rh ≫ u) := by
    refine (uOver_baseChange_iff hcart hlbc (toRat S₂.R)).2 ?_
    have e : (toRat S₂.R).comp om = rh.comp (toRat X₁.S.R) := RingHom.ext fun a => Subtype.ext (hval a)
    rw [e]
    exact hU.uOver.comp rh
  have hgen₂ : ∀ w, (spMap (ratHull S₂.R).val.toRingHom ≫ spMap rh ≫ u) w ∈ genericPoints (Xo.XF c) := fun w => by
    rw [← Category.assoc, hrv, Category.assoc, Scheme.Hom.comp_apply]
    exact hU.2.2.1 _
  have hcomp₂ : M₂.pt ≫ q ≫ π = spMap (ratHull S₂.R).val.toRingHom ≫ (spMap rh ≫ u) ≫ C.i := by
    rw [← Category.assoc, hqgen, Category.assoc, hU.2.2.2, ← Category.assoc (spMap (ratHull S₂.R).val.toRingHom),
      ← Category.assoc (spMap (ratHull S₂.R).val.toRingHom), hrv]
    simp only [Category.assoc]
  have hMn' : GlobalTheory.IsNormalScheme M₂.Z := GlobalTheory.IsNormalScheme.of_pred hMn
  have hdiv : M₂.HasDiv S₂.th :=
    C.thetaInt o₂ Ω₂ S₂ ρ₂ (spMap rh ≫ u) hUO₂ hgen₂ M₂ (q ≫ π) hMn' hcomp₂
  have hbig : S₂.Big := big j (by omega) o₂ Ω₂ S₂ (hg₂.trans hPg) hN₂ hr₂
  let X₂ : GSet :=
    { o₁ := o₂, Ω₁ := Ω₂, S := S₂, ρ := ρ₂, big := hbig, M := M₂, normal := hMn', projM := hproj, div := hdiv }
  set d := X₁.ρ.n ^ (j₀ + 2 * k) with hd
  have hlev : S₂.r * S₂.N = X₁.S.r * X₁.S.N * d := by
    rw [hr₂, hN₂, hL₁, hd, hj, ← pow_mul, ← pow_add, ← pow_add, mul_comm k 2]
    ring_nf
  obtain ⟨lam, hlam, hlamr⟩ := GlobalTheory.T.exists_thetaRealisation_labels_of_grpPullback X₁.S S₂ X₁.ρ ρ₂ om (φ₂ ≫ ψ) d hcart hlev
  have hRS : ∀ x : Ω₂, x ∈ S₂.R ↔ x ∈ R := fun x => by rw [hSR]
  let sR : (Ω₂ ≃ₐ[X₁.Ω₁] Ω₂) → (S₂.R →+* S₂.R) := fun σ =>
    RingHom.codRestrict (((σ : Ω₂ ≃+* Ω₂) : Ω₂ →+* Ω₂).comp S₂.R.val.toRingHom) S₂.R
      (fun x => (hRS _).2 (hstab σ x ((hRS _).1 x.2)))
  have hsR : ∀ σ, (sR σ).comp om = om := fun σ => RingHom.ext fun a => Subtype.ext
    ((congrArg σ (hval a)).trans ((σ.commutes _).trans (hval a).symm))
  choose gl hgl using fun σ => GlobalTheory.T.exists_thetaRealisation_label_perm_of_ringEndo X₁.S S₂ X₁.ρ ρ₂ om (φ₂ ≫ ψ) hcart (sR σ) (hsR σ)
  have hgll : ∀ σ a, gl σ (lam a) = lam a := fun σ a => GlobalTheory.T.thetaRealisation_labels_injective_of_grpPullback S₂ ρ₂ X₁.ρ.P.A (spMap om) (φ₂ ≫ ψ) hcart _ _ (by
      rw [hgl, hlam, ← Category.assoc, spMap_comp_ring, hsR])
  let 𝔗 : Tower X₁ act :=
    { X₂ := X₂
      act₂ := act₂
      isAct := hmon
      alg := inferInstance
      fd := fd
      gal := gal
      d := d
      lev := hlev
      om := om
      om_eq := hval
      om_fin := RingHom.Finite.comp (RingHom.Finite.of_surjective _ fun x => ⟨⟨x.1, (hRS _).1 x.2⟩, rfl⟩) hfin
      sR := sR
      sR_eq := fun σ a => rfl
      p := q
      p_fin := hq
      p_pt := hqgen
      φ := φ₂ ≫ ψ
      cart := hcart
      lb := hlbc
      act_eq := hact₂
      lam := lam
      lam_pt := hlam
      lam_range := hlamr
      gl := gl
      gl_pt := hgl
      gl_lam := hgll }
  refine ⟨𝔗, ?_⟩
  show N₀ ≤ S₂.r * S₂.N
  rw [hN₂, hr₂]
  exact hBk.trans (Nat.le_mul_of_pos_left _ (by have := hℓp.pos; positivity))

end GlobalTheory.GSep.UTower
