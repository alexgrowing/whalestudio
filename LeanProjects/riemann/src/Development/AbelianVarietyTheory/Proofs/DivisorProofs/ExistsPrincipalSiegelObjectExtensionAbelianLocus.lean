import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGenericFibreNormalLocalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegeneratePairingOfGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelBasisEveryGeometricPointLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDeterminedAtGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDescendsFromGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEndomorphismPlaceIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedExtensionFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianTorsionFiniteAndMulNSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslatesCoverSemiAbelian

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegExtend

open GlobalTheory.CechPic

section Bundle

variable {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]

omit [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] in

theorem pic_local [IsLocalRing O] (c : Pic (Sp O)) : c = 0 := by
  obtain ⟨D, hD, rfl⟩ := cls_surj c
  obtain ⟨i, hi⟩ := exists_chart hD (IsLocalRing.closedPoint O)
  have hV : D.U i = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 hi
  have := (cls_eq_zero_iff (pull_isLB hD (𝟙 _))).2 (IsoExtend.exists_gen_of_chart hD (𝟙 _) i fun y => by
    rw [hV]; trivial)
  rwa [cls_pull hD, pull_id] at this

theorem generic_props : IsPreimmersion (spMap (algebraMap O K)) ∧ Flat (spMap (algebraMap O K)) ∧
    IsDominant (spMap (algebraMap O K)) := by
  refine ⟨IsPreimmersion.of_isLocalization (nonZeroDivisors O), ?_, ⟨?_⟩⟩
  · exact (HasRingHomProperty.Spec_iff (P := @Flat)).2
      (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors O)))
  · exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap O K)).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O K)]; exact bot_le)

theorem pic_generic [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] (X : Over (Sp O)) [Smooth X.hom]
    [GeometricallyIntegral X.hom] (e : 𝟙_ (Over (Sp O)) ⟶ X) {X' : Scheme.{0}} {t : X' ⟶ Sp K} {ψ : X' ⟶ X.left}
    (h : IsPullback ψ t X.hom (spMap (algebraMap O K))) {a b : Pic X.left} (hab : pull ψ a = pull ψ b) : a = b := by
  obtain ⟨_, _, _⟩ := generic_props (O := O) (K := K)
  refine ZH.EndoExtend.pic_ext (spMap (algebraMap O K)) (ZJ.isNormalScheme_sp O) X e.left (Over.w e)
    ((pic_local _).trans (pic_local _).symm) ?_
  rw [← h.isoPullback_inv_fst, pull_comp, pull_comp, hab]

theorem exists_extension [IsRegularRing O] (X : Over (Sp O)) [Smooth X.hom] [IsProper X.hom]
    [GeometricallyIntegral X.hom] {X' : Scheme.{0}} {t : X' ⟶ Sp K} {ψ : X' ⟶ X.left}
    (h : IsPullback ψ t X.hom (spMap (algebraMap O K))) (L : LB X') (hL : L.IsLB) :
    ∃ M : LB X.left, M.IsLB ∧ LBIso (M.pull ψ) L := by
  obtain ⟨h₁, h₂, _⟩ := generic_props (O := O) (K := K)
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian X.hom
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : GeometricallyIntegral t := MorphismProperty.of_isPullback (P := @GeometricallyIntegral) h inferInstance
  have : Smooth t := MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
  have : IsIntegral X' := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian t
  have : IsPreimmersion ψ := MorphismProperty.of_isPullback (P := @IsPreimmersion) h.flip h₁
  have : Flat ψ := MorphismProperty.of_isPullback (P := @Flat) h.flip h₂
  have hY : ∀ y, IsRegularLocalRing ((Sp O).presheaf.stalk y) := fun y => by
    have := y.isPrime
    have := isRegularRing_iff.1 ‹IsRegularRing O› y.asIdeal
    letI : Algebra O ((Sp O).presheaf.stalk y) := StructureSheaf.stalkAlgebra O y
    haveI : IsLocalization.AtPrime ((Sp O).presheaf.stalk y) y.asIdeal := StructureSheaf.IsLocalization.to_stalk O y
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv y.asIdeal.primeCompl (Localization.AtPrime y.asIdeal) ((Sp O).presheaf.stalk y)).toRingEquiv
  exact exists_lineBundle_extension_of_generalizing X.left X' ψ (Flat.generalizingMap ψ)
    (fun x => have := ThetaExtend.isRegularRing_stalk hY X.hom x; ThetaExtend.ufd_of_regular _) L hL

theorem exists_bundle [IsRegularLocalRing O] {A : Over (Sp O)} [GrpObj A] {A' : Over (Sp K)} [GrpObj A']
    {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hA : IsAbelianScheme A)
    (h : IsGrpPullback A' A (spMap (algebraMap O K)) φ) (sq : IsSquare φ φ₂) {P' : LB (A' ⊗ A').left} (hP' : P'.IsLB)
    (r₁ : ∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen)
    (r₂ : ∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen)
    (sy : LBIso P' (P'.pull (lift (snd A' A') (fst A' A')).left)) :
    ∃ P : LB (A ⊗ A).left, P.IsLB ∧ LBIso P' (P.pull φ₂) ∧
      (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
      (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧
      LBIso P (P.pull (lift (snd A A) (fst A A)).left) := by
  have := isRegularRing_of_isRegularLocalRing O
  have := ThetaExtend.ufd_of_regular O
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have : GeometricallyIntegral A.hom := geometricallyIntegral_of_smooth _
  have := smooth_tensorObj_hom A A
  have := geometricallyIntegral_tensorObj_hom A A
  have : IsProper (A ⊗ A).hom := inferInstanceAs (IsProper (pullback.fst A.hom A.hom ≫ A.hom))
  have h₂ := AbDual.isPullback_prod h.1 h.1 sq.1 sq.2
  obtain ⟨P, hP, e⟩ := exists_extension (A ⊗ A) h₂ P' hP'
  have e₀ : pull φ₂ (cls P hP) = cls P' hP' := (cls_eq_iff (pull_isLB hP φ₂) hP').2 e
  have one : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
    have a := congrArg (fun q => q.left) (map_one (pushHom h A'))
    have b := congrArg (fun q => q.left) (GlobalTheory.Mum.Cover.comp_one_pt (G := A) (Over.homMk φ h.1.w :
      Over.mk (A'.hom ≫ spMap (algebraMap O K)) ⟶ A))
    exact a.trans b.symm
  have key : ∀ (a' b' : A' ⟶ A') (a b : A ⟶ A), a'.left ≫ φ = φ ≫ a.left → b'.left ≫ φ = φ ≫ b.left →
      (∃ t : (P'.pull (lift a' b').left).Gen, t.IsGen) → ∃ t : (P.pull (lift a b).left).Gen, t.IsGen := by
    intro a' b' a b ha hb ht
    refine (cls_eq_zero_iff (pull_isLB hP _)).1 (pic_generic A η[A] h.1 ?_)
    have := SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) a' b' φ a b
      ((Category.id_comp _).trans ha) ((Category.id_comp _).trans hb)
    have e : (lift a' b').left ≫ φ₂ = φ ≫ (lift a b).left := (Category.id_comp _).symm.trans this
    rw [map_zero, cls_pull hP, ← pull_comp, ← e, pull_comp, e₀, ← cls_pull hP']
    exact (cls_eq_zero_iff (pull_isLB hP' _)).2 ht
  refine ⟨P, hP, e.symm, key _ _ _ _ one (by simp) r₁, key _ _ _ _ (by simp) one r₂, ?_⟩
  refine (cls_eq_iff hP (pull_isLB hP _)).1 (pic_generic (A ⊗ A) (lift η[A] η[A]) h₂ ?_)
  have := SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (A ⊗ A).hom)) (T' := A' ⊗ A') (𝟙 _) (snd A' A') (fst A' A')
    φ₂ (snd A A) (fst A A) ((Category.id_comp _).trans sq.2.symm) ((Category.id_comp _).trans sq.1.symm)
  rw [Category.id_comp] at this
  rw [cls_pull hP, ← pull_comp, ← this, pull_comp, e₀, ← cls_pull hP']
  exact (cls_eq_iff hP' (pull_isLB hP' _)).2 sy

end Bundle

section Level

variable {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]

omit [IsDomain O] [IsFractionRing O K] in
theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f f' : R →+* R'} (e : spMap f = spMap f') : f = f' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective e)

variable {A : Over (Sp O)} [GrpObj A] {A' : Over (Sp K)} [GrpObj A'] {ψ : A'.left ⟶ A.left}

theorem sec_ext (hA : IsAbelianScheme A) {u v : 𝟙_ (Over (Sp O)) ⟶ A}
    (e : spMap (algebraMap O K) ≫ u.left = spMap (algebraMap O K) ≫ v.left) : u = v := by
  have := hA.proper
  exact LabelExt.ext_frac (K := K) (G := A) (y := 𝟙 (Sp O)) e

theorem exists_lev [IsIntegrallyClosed O] (hA : IsAbelianScheme A) (h : IsGrpPullback A' A (spMap (algebraMap O K)) ψ)
    {g n : ℕ} (hn : n ≠ 0) (lev' : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp K)) ⟶ A'))
    (add' : ∀ a b, lev' (a + b) = lev' a * lev' b) (tors' : ∀ a, lev' a ^ n = 1) :
    ∃ lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp O)) ⟶ A), (∀ a b, lev (a + b) = lev a * lev b) ∧
      (∀ a, lev a ^ n = 1) ∧ ∀ a, (lev' a).left ≫ ψ = spMap (algebraMap O K) ≫ (lev a).left := by
  have hy : spMap (algebraMap O K) ≫ 𝟙 (Sp O) = (𝟙_ (Over (Sp K))).hom ≫ spMap (algebraMap O K) := by
    rw [Category.comp_id]; exact (Category.id_comp _).symm
  have ex : ∀ a, ∃ v : Over.mk (𝟙 (Sp O)) ⟶ A, spMap (algebraMap O K) ≫ v.left = (pushHom h _ (lev' a)).left :=
    fun a => LabelExt.lift_tors (K := K) A hA hn hy (pushHom h _ (lev' a)) (by rw [← map_pow, tors', map_one])
  choose lev hlev using ex
  have hl : ∀ a, (lev' a).left ≫ ψ = spMap (algebraMap O K) ≫ (lev a).left := fun a => (hlev a).symm
  let J : Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (algebraMap O K)) ⟶ 𝟙_ (Over (Sp O)) := toUnit _
  have K1 : ∀ a, J ≫ lev a = pushHom h _ (lev' a) := fun a => by
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    change (toUnit (Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap (algebraMap O K)))).left ≫ (lev a).left =
      (lev' a).left ≫ ψ
    rw [Over.toUnit_left, hl]
    exact congrArg (· ≫ (lev a).left) (Category.id_comp (spMap (algebraMap O K)))
  have K2 : ∀ u v : 𝟙_ (Over (Sp O)) ⟶ A, J ≫ u = J ≫ v → u = v := fun u v e => by
    refine sec_ext (K := K) hA ?_
    have e' := congrArg (fun q => q.left) e
    simp only [Over.comp_left, J, Over.toUnit_left] at e'
    simpa using e'
  refine ⟨lev, fun a b => K2 _ _ ?_, fun a => K2 _ _ ?_, hl⟩
  · rw [MonObj.comp_mul, K1, K1, K1, add', map_mul]
  · rw [MonObj.comp_pow, K1, ← map_pow, tors', map_one, MonObj.comp_one]

omit [IsDomain O] [IsFractionRing O K] in

theorem push_lev (h : IsGrpPullback A' A (spMap (algebraMap O K)) ψ) {u' : 𝟙_ (Over (Sp K)) ⟶ A'}
    {u : 𝟙_ (Over (Sp O)) ⟶ A} (hu : u'.left ≫ ψ = spMap (algebraMap O K) ≫ u.left) (T : Over (Sp K)) :
    pushHom h T (toUnit T ≫ u') = toUnit (Over.mk (T.hom ≫ spMap (algebraMap O K))) ≫ u := by
  apply Over.OverMorphism.ext
  change (toUnit T ≫ u').left ≫ ψ = (toUnit (Over.mk (T.hom ≫ spMap (algebraMap O K))) ≫ u).left
  rw [Over.comp_left, Over.comp_left, Category.assoc, hu, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

end Level

section Extend

open SiegelPull in

theorem extend (O K : Type) [CommRing O] [IsRegularLocalRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    {B : Type} [CommRing B] (ζ : B) (hζ : IsUnit ζ) (g n : ℕ) (hn : n ≠ 0) (hnB : IsUnit (n : B))
    (s' : Sp O ⟶ Sp B) (s₀ : Sp K ⟶ Sp B) (hs₀ : spMap (algebraMap O K) ≫ s' = s₀) (A : Over (Sp O)) [GrpObj A]
    [IsCommMonObj A] (hA : IsAbelianScheme A) (c' : SiegPre g n ζ s₀) (hc' : c'.Principal) (ψ : c'.A.left ⟶ A.left)
    (h : IsGrpPullback c'.A A (spMap (algebraMap O K)) ψ) :
    ∃ c : SiegPre g n ζ s', c.Principal ∧ SiegPB c' c (spMap (algebraMap O K)) := by
  subst hs₀
  obtain ⟨_, _⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing O
  obtain ⟨φ₂, q₁, q₂⟩ := AbDual.exists_prod_pullback h h
  have sq : IsSquare ψ φ₂ := ⟨q₁, q₂⟩
  obtain ⟨P, hP, e, r₁, r₂, sy⟩ := exists_bundle hA h sq c'.isLB c'.rig₁ c'.rig₂ c'.symm
  have ed : LBIso c'.diag ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull ψ) := diag_iso sq e
  have amp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) :=
    GlobalTheory.T.relAmple_of_genericFibre_normalLocalDomain O K A c'.A ψ hA h _ _ (pull_isLB hP _) (pull_isLB c'.isLB _) ed hc'.1
  have nd := GlobalTheory.T.nondegenerate_pairing_of_generic_fibre O K A c'.A ψ φ₂ hA h sq P c'.P hP c'.isLB e r₁ r₂ sy amp hc'.2
  obtain ⟨σ, rfl⟩ := Models.RankZero.exists_spMap s'
  have hnO : IsUnit (n : O) := by simpa using hnB.map σ
  obtain ⟨lev, add, tors, hl⟩ := exists_lev (K := K) hA h hn c'.lev c'.lev_add c'.lev_tors
  let k₀ := AlgebraicClosure K
  let xk : Sp k₀ ⟶ Sp K := spMap (algebraMap K k₀)
  let j : O →+* k₀ := (algebraMap K k₀).comp (algebraMap O K)
  have hj : xk ≫ spMap (algebraMap O K) = spMap j := Models.RankZero.spMap_comp _ _
  have hjinj : Function.Injective j := (algebraMap K k₀).injective.comp (IsFractionRing.injective O K)
  let ζO : Oˣ := (hζ.map σ).unit
  have hβ₀ : xk ≫ spMap (algebraMap O K) ≫ spMap σ = spMap (j.comp σ) := by
    rw [← Category.assoc, hj, Models.RankZero.spMap_comp]
  obtain ⟨g1, g2, g3⟩ := c'.geom k₀ xk (j.comp σ) (Units.map j.toMonoidHom ζO) hβ₀ rfl
  have pl : ∀ a, pushHom h (Over.mk xk) (toUnit _ ≫ c'.lev a) =
      toUnit (Over.mk (xk ≫ spMap (algebraMap O K))) ≫ lev a := fun a => push_lev h (hl a) _
  have t1 : ∀ a, (toUnit (Over.mk (xk ≫ spMap (algebraMap O K))) ≫ lev a = 1 ↔ ∃ b, a = n • b) := fun a => by
    rw [← g1 a, ← pl a, ← map_one (pushHom h (Over.mk xk))]
    exact (push_injective h _).eq_iff
  have t2 : ∀ u : Over.mk (xk ≫ spMap (algebraMap O K)) ⟶ A, u ^ n = 1 →
      ∃ a, toUnit _ ≫ lev a = u := fun u hu => by
    obtain ⟨u', rfl⟩ := push_surjective h (Over.mk xk) u
    obtain ⟨a, ha⟩ := g2 u' (push_injective h _ (by rw [map_pow, hu, map_one]))
    exact ⟨a, by rw [← pl a, ha]⟩
  have TT := GlobalTheory.T.levelBasis_every_geometricPoint_localRing O A hA g n hnO lev add tors k₀ _ t1 t2
  have w0 : ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n (toUnit (Over.mk (spMap j)) ≫ lev a)
      (toUnit (Over.mk (spMap j)) ≫ lev b) (unitOn (Units.map j.toMonoidHom (ζO ^ (2 * omegaStd a b)))) :=
    fun a b => by
      rw [← hj, map_zpow]
      exact (weilIs_grpPullback_of_comm (Sp O) (Sp K) A c'.A (spMap (algebraMap O K)) ψ _ _ (pull_isLB hP _)
        (pull_isLB c'.isLB _) h ed (Over.mk xk) n _ _ _ _ _ (congrArg (fun q => q.left) (pl a)).symm
        (congrArg (fun q => q.left) (pl b)).symm).1 (g3 a b)
  refine ⟨{
      A := A
      ab := hA
      P := P
      isLB := hP
      rig₁ := r₁
      rig₂ := r₂
      symm := sy
      lev := lev
      lev_add := add
      lev_tors := tors
      geom := ?_ }, ⟨amp, nd⟩, ψ, φ₂, h, sq, e, hl⟩
  intro k _ _ x β z hx hz
  obtain ⟨ρ, rfl⟩ := Models.RankZero.exists_spMap x
  obtain ⟨c1, c2⟩ := TT k (spMap ρ)
  refine ⟨c1, c2, fun a b => ?_⟩
  have hβ : ρ.comp σ = β := spMap_inj ((Models.RankZero.spMap_comp σ ρ).symm.trans hx)
  have hzz : Units.map ρ.toMonoidHom ζO = z := Units.ext (by rw [hz, ← hβ]; rfl)
  have := GlobalTheory.T.commutatorPairing_determined_at_genericPoint O A hA P hP r₁ r₂ amp n (Nat.pos_of_ne_zero hn) hnO (lev a) (lev b) (tors a) (tors b)
    (ζO ^ (2 * omegaStd a b)) k₀ j hjinj (w0 a b) k ρ
  rwa [map_zpow, hzz] at this

end Extend

section Main

theorem zero_case {g : ℕ} {K : Type} [Field K] [CharZero K] {s₀ : Sp K ⟶ Sp (cycAway 0)}
    (c' : SiegPre g 0 (zetaAway 0) s₀) : g = 0 ∧ IsIso c'.A.hom := by
  have hz1 : zetaAway 0 = 1 := Subtype.ext (by simp [zetaAway, zeta])
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp K),
      (∀ a, toUnit (Over.mk x) ≫ c'.lev a = 1 ↔ a = 0) ∧ ∀ u : Over.mk x ⟶ c'.A, ∃ a, toUnit _ ≫ c'.lev a = u := by
    intro k _ _ x
    obtain ⟨β, hβ⟩ := Models.RankZero.exists_spMap (x ≫ s₀)
    obtain ⟨g1, g2, -⟩ := c'.geom k x β 1 hβ (by rw [hz1, map_one]; rfl)
    exact ⟨fun a => (g1 a).trans (by simp), fun u => g2 u (pow_zero u)⟩
  have lev0 : c'.lev 0 = 1 := by
    have := c'.lev_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have iso : IsIso c'.A.hom := by
    refine Models.RankZero.isIso_of_no_torsion GlobalTheory.card_torsion_abelianVariety c'.A c'.ab fun k _ _ x => ?_
    obtain ⟨ρ, rfl⟩ := Models.RankZero.exists_spMap x
    have : CharZero k := charZero_of_injective_ringHom ρ.injective
    refine ⟨2, one_lt_two, two_ne_zero, fun u hu => ?_⟩
    obtain ⟨a, rfl⟩ := (key k _).2 u
    have h2 : toUnit (Over.mk (spMap ρ)) ≫ c'.lev (a + a) = 1 := by
      rw [c'.lev_add, MonObj.comp_mul, ← sq, hu]
    have ha : a = 0 := by
      have h0 := ((key k _).1 _).1 h2
      funext i
      have := congrFun h0 i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      show a i = 0
      omega
    rw [ha, lev0, MonObj.comp_one]
  refine ⟨?_, iso⟩
  by_contra hg
  let k := AlgebraicClosure K
  let a : Fin g ⊕ Fin g → ℤ := Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hg⟩) 1
  have h0 := ((key k (spMap (algebraMap K k))).1 a).1 (Models.RankZero.hom_unique iso _ _)
  have := congrFun h0 (Sum.inl ⟨0, Nat.pos_of_ne_zero hg⟩)
  simp [a] at this

theorem exists_principal_extension : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R] (b : cycAway n →+* R) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → ∀ (p : Sp R) [p.asIdeal.IsPrime], IsAbelianScheme ((Over.pullback (spMap (algebraMap R (Localization.AtPrime p.asIdeal)))).obj G₁) → ∀ (κ : Sp (FractionRing R) ⟶ Sp (Localization.AtPrime p.asIdeal)) (s' : Sp (Localization.AtPrime p.asIdeal) ⟶ Sp (cycAway n)), κ ≫ spMap (algebraMap R (Localization.AtPrime p.asIdeal)) = jK R → κ ≫ s' = y ≫ F.s → ∃ (c : SiegPre g n (zetaAway n) s') (c' : SiegPre g n (zetaAway n) (y ≫ F.s)), c.Principal ∧ SiegPB c' c κ ∧ SiegPB c' F.univ y := by
  intro g n F R _ _ _ _ b G₁ _ _ y A₁ _ i₁ β hsemi hp1 hp2 p _ hab κ s' hκ hs'
  let O := Localization.AtPrime p.asIdeal
  have : IsRegularLocalRing O := isRegularRing_iff.mp (isRegularRing_of_isRegularLocalRing R) p.asIdeal
  obtain ⟨κ₀, rfl⟩ := Models.RankZero.exists_spMap κ
  have hκ₀ : κ₀.comp (algebraMap R O) = algebraMap R (FractionRing R) :=
    spMap_inj ((Models.RankZero.spMap_comp _ _).symm.trans hκ)
  letI : Algebra O (FractionRing R) := κ₀.toAlgebra
  haveI : IsScalarTower R O (FractionRing R) :=
    IsScalarTower.of_algebraMap_eq fun r => (RingHom.congr_fun hκ₀ r).symm
  haveI : IsFractionRing O (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.asIdeal.primeCompl O (FractionRing R)
  have hAp := isGrpPullback_pullback G₁ (spMap (algebraMap R O))
  haveI : IsCommMonObj ((Over.pullback (spMap (algebraMap R O))).obj G₁) :=
    GlobalTheory.TorusPart.isCommMonObj_of_isGrpPullback hAp
  obtain ⟨φ', hφ', -⟩ := GlobalTheory.PlaceModel.exists_factor_pullback hAp hp1 (spMap κ₀) hκ
  obtain ⟨⟨c'₀, hpb⟩, hprin⟩ := siegPre_pullback g n (cycAway n) (zetaAway n) F.X (Sp (FractionRing R)) F.s
    (y ≫ F.s) y F.univ rfl
  have pc' := hprin c'₀ hpb F.princ
  obtain ⟨φc, -, hφc, -⟩ := id hpb
  obtain ⟨e, he, -⟩ := grpPullback_iso hφc hp2
  have hψ : IsGrpPullback c'₀.A ((Over.pullback (spMap (algebraMap R O))).obj G₁) (spMap κ₀) (e.hom.left ≫ φ') :=
    ((isGrpPullback_of_iso e).comp hφ').congr (Category.id_comp _) rfl
  by_cases hn : n = 0
  · subst hn
    have : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
    obtain ⟨rfl, iso⟩ := zero_case c'₀
    exact ⟨Models.RankZero.zeroSieg 0 (zetaAway 0) s', c'₀, Models.RankZero.principal_zeroSieg s',
      Models.RankZero.siegPB_zero iso (Models.RankZero.isIso_unit _) _, hpb⟩
  · have hζ : IsUnit (zetaAway n) := by
      have h1 : zetaAway n ^ n = 1 := Subtype.ext (by
        simpa [zetaAway, zeta] using (Complex.isPrimitiveRoot_exp n hn).pow_eq_one)
      exact ⟨Units.ofPowEqOne _ n h1 hn, rfl⟩
    obtain ⟨c, hc, pb⟩ := extend O (FractionRing R) (zetaAway n) hζ g n hn (GlobalTheory.SiegelTor.isUnit_natCast hn) s'
      (y ≫ F.s) hs' _ hab c'₀ pc' _ hψ
    exact ⟨c, c'₀, hc, pb, hpb⟩

end Main

end GlobalTheory.SiegExtend
