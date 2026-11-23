import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEndOfEighthPowerOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationModelFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithBaseFiniteContainingRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.TowerLarge

theorem isDiagEnd_of_isAct {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (h : IsAct X₁ act) :
    IsDiagEnd F W X₁.ρ.P X₁.u act := by
  obtain ⟨c, hc, pr, hpr, hu, hL, hact⟩ := h
  exact ⟨c, hc, pr, hpr, hu, hL, fun E a => by simpa [List.ofFn_eq_map] using hact E a⟩

theorem isAct_of_isDiagEnd {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A))
    (h : IsDiagEnd F W X₁.ρ.P X₁.u act) : IsAct X₁ act := by
  obtain ⟨c, hc, pr, hpr, hu, hL, hact⟩ := h
  exact ⟨c, hc, pr, hpr, hu, hL, fun E a => by simpa [List.ofFn_eq_map] using hact E a⟩

theorem lbIso_pull_comp' {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M j j rfl)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem exists_tower_ge : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ N₀ : ℕ, ∃ 𝔗 : Tower X₁ act, N₀ ≤ 𝔗.X₂.S.r * 𝔗.X₂.S.N := by
  intro g _ n _ _ F Z z i _ _ _ _ _ W _ _ X₁ _ act hact N₀
  have hε₁ := isDiagEnd_of_isAct X₁ act hact
  have hℓp : X₁.ρ.n.Prime := X₁.ρ.n_prime
  have hℓ2 : 2 ≤ X₁.ρ.n := hℓp.two_le
  obtain ⟨j₁, hj₁, hr⟩ := X₁.ρ.r_eq
  have hL₁ : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) := by
    rw [hr, X₁.ρ.N_eq, ← pow_mul, ← pow_add, mul_comm X₁.ρ.k 2]
  obtain ⟨k, j₀, hk, hBk, hj₀, big⟩ := GSetup.exists_big_ge X₁.ρ.P.g X₁.ρ.n hℓ2 N₀
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
  obtain ⟨Ω₂, _, _, Q, φQ, ζ, fd, gal, deg, hζ, hQg, hQpb, hQlb, ⟨levQ⟩⟩ :=
    GlobalTheory.T.exists_primePower_galois_ext_symplecticLevel X₁.S.R.val.toRingHom X₁.ρ.P X₁.ρ.n (X₁.S.r * X₁.S.N) K hℓp hM
      (by rw [hL₁]; exact dvd_pow_self _ (by omega)) ⟨2 * (j + 2 * k), by rw [hK]; ring⟩ hζ₀ htors
  haveI := fd
  obtain ⟨o₂, _, _, _, κ, ze, hκ, hc, hze⟩ := GlobalTheory.Poinc.exists_arithBase_rootOfUnity (o₁ := X₁.o₁) (Ω₁ := X₁.Ω₁) Ω₂ K ζ hKpos hζ
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
    rw [hom, ← spMap_comp']
    exact hpb₂.comp hpb
  have hlbc : LBIso ρ₂.P.L (X₁.ρ.P.L.pull (φ₂ ≫ ψ)) :=
    LBIso.trans ρ₂.P.isLB (pull_isLB P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hlb₂ (lbIso_pull_comp' hlb φ₂ rfl)
  obtain ⟨ε₂, hε₂, hεc⟩ := GlobalTheory.Poinc.isDiagEnd_pullback F W X₁.ρ.P ρ₂.P X₁.u (spMap om) (φ₂ ≫ ψ) act hε₁ hcart hlbc
  have hsharp : SharpOver F W ρ₂.P (spMap om ≫ X₁.u) := by
    obtain ⟨c, hc₁, pr, hpr, hun, hLc, -⟩ := hε₂
    exact ⟨c, hc₁, pr, hpr, hun, hLc⟩
  have key : spMap S₂.R.val.toRingHom ≫ spMap om = spMap (algebraMap X₁.Ω₁ Ω₂) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [spMap_comp', spMap_comp']
    congr 1
    ext a
    exact hval a
  have hgen : ∀ w, (spMap S₂.R.val.toRingHom ≫ spMap om ≫ X₁.u) w ∈ genericPoints F.X := by
    intro w
    rw [← Category.assoc, key, Category.assoc, Scheme.Hom.comp_apply]
    exact X₁.gen _
  obtain ⟨M₂, q, hMn, hq, hqgen⟩ := GlobalTheory.Poinc.Setup.exists_model_of_finiteDimensional X₁ o₂ Ω₂ κ hκ hc
  haveI := hq
  haveI := X₁.fin
  have hcomp : M₂.pt ≫ q ≫ X₁.π = spMap S₂.R.val.toRingHom ≫ (spMap om ≫ X₁.u) ≫ i := by
    rw [← Category.assoc, hqgen, Category.assoc, X₁.comp, Category.assoc, ← Category.assoc (spMap S₂.R.val.toRingHom),
      key, Category.assoc]
  have hbase : spMap S₂.R.val.toRingHom ≫ (spMap om ≫ X₁.u) ≫ F.s =
      spMap ((algebraMap o₂ Ω₂).comp (κ.comp X₁.κ)) := by
    rw [← Category.assoc, ← Category.assoc, key, Category.assoc, Category.assoc, X₁.base, spMap_comp', ← RingHom.comp_assoc, ← hc]
  have hbig : S₂.Big := big j (by omega) o₂ Ω₂ S₂ (hg₂.trans hPg) hN₂ hr₂
  let X₂ : Setup F W i := Setup.mk o₂ Ω₂ S₂ ρ₂ hbig (spMap om ≫ X₁.u) hsharp hgen M₂ hMn (q ≫ X₁.π) inferInstance hcomp
    X₁.one_le X₁.three_le X₁.odd X₁.z X₁.proj X₁.normalZ X₁.imm X₁.thetaSetup_structureMap_comp X₁.dense X₁.e8 X₁.thetaInt (κ.comp X₁.κ) hbase
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
      rw [hgl, hlam, ← Category.assoc, spMap_comp', hsR])
  let 𝔗 : Tower X₁ act :=
    { X₂ := X₂
      act₂ := ε₂
      isAct := isAct_of_isDiagEnd X₂ ε₂ hε₂
      alg := inferInstance
      fd := fd
      gal := gal
      deg := deg
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
      p_π := rfl
      φ := φ₂ ≫ ψ
      cart := hcart
      lb := hlbc
      act_eq := hεc
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

end GlobalTheory.Poinc.Sep.TowerLarge
