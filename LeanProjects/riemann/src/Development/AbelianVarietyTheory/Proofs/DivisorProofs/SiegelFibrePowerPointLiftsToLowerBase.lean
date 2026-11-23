import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedCubicalRootPolarisationEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackPasteFactorisation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfFiniteOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVROfFiniteEtaleBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowLift

theorem etCompl : ∀ {o : Type} [CommRing o] [IsNoetherianRing o] {ζ : o} {h n : ℕ} (F : SFam h n ζ) {r : ℕ} (y : (GlobalTheory.LowChart.powA F r).left) (R' : Type) [CommRing R'] [IsLocalRing R'] (ρ : GlobalTheory.LowChart.W F y →+* R'), IsLocalHom ρ → ρ.Finite → ρ.Etale → IsEtaleCompletion (Scheme.stalkClosedPointTo (spMap ρ ≫ GlobalTheory.LowChart.toPow F y)).hom ∧ ((residue R').comp (Scheme.stalkClosedPointTo (spMap ρ ≫ GlobalTheory.LowChart.toPow F y)).hom).FormallyUnramified := by
  intro o _ _ ζ h n F r y R' _ _ ρ hloc hfin het
  let y₀ : Sp (GlobalTheory.LowChart.W F y) ⟶ (GlobalTheory.LowChart.powA F r).left := GlobalTheory.LowChart.toPow F y
  obtain ⟨hEt₀, hres₀⟩ := GlobalTheory.InteriorChart.completedStalk_chart (GlobalTheory.LowChart.powA F r).left y
  change IsEtaleCompletion (Scheme.stalkClosedPointTo y₀).hom at hEt₀
  change Function.Surjective ((residue (GlobalTheory.LowChart.W F y)).comp (Scheme.stalkClosedPointTo y₀).hom) at hres₀
  have hfu : ρ.FormallyUnramified ∧ ρ.Flat := by
    algebraize [ρ]
    exact ⟨inferInstanceAs (Algebra.FormallyUnramified _ R'), inferInstanceAs (Module.Flat _ R')⟩
  have hm' : (maximalIdeal (GlobalTheory.LowChart.W F y)).map ρ = maximalIdeal R' := by
    algebraize [ρ]
    haveI : IsLocalHom (algebraMap (GlobalTheory.LowChart.W F y) R') := hloc
    exact Algebra.FormallyUnramified.map_maximalIdeal
  let ξ₀ : Sp R' ⟶ (GlobalTheory.LowChart.powA F r).left := spMap ρ ≫ y₀
  have hcp : ξ₀ (closedPoint R') = y₀ (closedPoint (GlobalTheory.LowChart.W F y)) := by
    show y₀ (spMap ρ (closedPoint R')) = _
    rw [show spMap ρ (closedPoint R') = closedPoint (GlobalTheory.LowChart.W F y) from IsLocalRing.comap_closedPoint ρ]
  have hs : ξ₀ (closedPoint R') ⤳ y₀ (closedPoint (GlobalTheory.LowChart.W F y)) := specializes_of_eq hcp
  have key := GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes (GlobalTheory.LowChart.powA F r).left y₀ ρ hs
  let E := RingEquiv.ofBijective ((GlobalTheory.LowChart.powA F r).left.presheaf.stalkSpecializes hs).hom
    (GlobalTheory.InteriorChart.bijective_stalkSpecializes hcp hs)
  have hξ : (Scheme.stalkClosedPointTo ξ₀).hom =
      (ρ.comp (Scheme.stalkClosedPointTo y₀).hom).comp E.symm.toRingHom := by
    ext b
    obtain ⟨a, rfl⟩ := E.surjective b
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply]
    exact key a
  refine ⟨?_, ?_⟩
  · show IsEtaleCompletion (Scheme.stalkClosedPointTo ξ₀).hom
    rw [hξ]
    exact isEtaleCompletion_comp_bij _ E.symm.bijective _
      (GlobalTheory.InteriorChart.isEtaleCompletion_comp _ ρ hEt₀ hfu.2 hm' hfin)
  · show ((residue R').comp (Scheme.stalkClosedPointTo ξ₀).hom).FormallyUnramified
    have hmap : (ResidueField.map ρ).FormallyUnramified := by
      apply RingHom.FormallyUnramified.of_comp (f := residue (GlobalTheory.LowChart.W F y))
      rw [ResidueField.map_comp_residue]
      exact RingHom.FormallyUnramified.comp hfu.1 (RingHom.FormallyUnramified.of_surjective residue_surjective)
    have e2 : (residue R').comp (Scheme.stalkClosedPointTo ξ₀).hom = (ResidueField.map ρ).comp
        (((residue (GlobalTheory.LowChart.W F y)).comp (Scheme.stalkClosedPointTo y₀).hom).comp E.symm.toRingHom) := by
      rw [hξ, ← RingHom.comp_assoc, ← RingHom.comp_assoc, ← ResidueField.map_comp_residue]
      rfl
    rw [e2]
    exact RingHom.FormallyUnramified.comp
      (RingHom.FormallyUnramified.of_surjective (hres₀.comp E.symm.surjective)) hmap

theorem prodPush : ∀ {S S' T : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}, IsGrpPullback G' G f φ → ∀ {r : ℕ} (p : Fin r → (𝟙_ (Over S') ⟶ G')) (t : T ⟶ S) (q : Fin r → (Over.mk t ⟶ G)) (g : T ⟶ S'), g ≫ f = t → (∀ i, g ≫ (p i).left ≫ φ = (q i).left) → ∀ a : Fin r → ℤ, g ≫ (∏ i, p i ^ a i).left ≫ φ = (∏ i, q i ^ a i).left := by
  intro S S' T G G' _ _ _ _ f φ hG r p t q g ht hq a
  subst ht
  let U : Over.mk g ⟶ 𝟙_ (Over S') := toUnit _
  let Φ : (𝟙_ (Over S') ⟶ G') →* (Over.mk ((Over.mk g).hom ≫ f) ⟶ G) := (pushHom hG (Over.mk g)).comp (preHom U)
  have hΦ : ∀ x, (Φ x).left = g ≫ x.left ≫ φ := fun x => by
    show (U ≫ x).left ≫ φ = _
    rw [Over.comp_left, Category.assoc]
    rfl
  have hpq : ∀ i, Φ (p i) = q i := fun i => Over.OverMorphism.ext ((hΦ _).trans (hq i))
  have e : Φ (∏ i, p i ^ a i) = ∏ i, q i ^ a i := by
    rw [map_prod]
    simp only [map_zpow, hpq]
  exact (hΦ _).symm.trans (congrArg (fun z => z.left) e)

end GlobalTheory.LowLift

namespace GlobalTheory.LowLift

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem main : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (h : ℕ) (F : SFam h n (zetaAway n)) (r : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsDiscreteValuationRing V₁ → ∀ (b₁ : cycAway n →+* V₁) (v : Sp V₁ ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = spMap b₁), ∃ (L : LowBase (zetaAway n) n) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V₁ →+* V') (κ : L.W →+* V') (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)), L.h = h ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b₁ ∧ ∃ (B' : Over (Sp V')) (_ : GrpObj B') (β' : B'.left ⟶ (GlobalTheory.LowChart.siegAt F v _ hs).A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 (GlobalTheory.LowChart.siegAt F v _ hs).A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsGrpPullback B' (GlobalTheory.LowChart.siegAt F v _ hs).A (spMap f) β' ∧ IsGrpPullback B' L.T.B (spMap κ) β'' ∧ IsSquare β' β₂ ∧ IsSquare β'' β₂' ∧ LBIso ((GlobalTheory.LowChart.siegAt F v _ hs).P.pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') ∧ ∀ a : Fin L.T.r → ℤ, ∃ x : Sp V' ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f ≫ (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • e a)).left ∧ x ≫ β'' = spMap κ ≫ (L.T.c₀ ((n : ℤ) • a)).left := by
  intro n hn _ h F r V₁ _ _ _ hV hdvr b₁ v hs
  have hV0 := hV
  obtain ⟨-, -, hVc, -⟩ := hV
  haveI := hVc
  let w := v (closedPoint V₁)
  obtain ⟨ψ, hψl, hψ⟩ := GlobalTheory.LowChart.exists_local_hom F w V₁ v rfl
  haveI : IsNoetherianRing (GlobalTheory.LowChart.W F w) := GlobalTheory.LowChart.isNoetherianRing_completedStalkSiegelFibrePower F w
  obtain ⟨R', _, _, ρ, hc', hloc, hinj, hfin, het, B, _, _, β, β₂, M, cub, hpb, hsq, hamp, hk, hiso⟩ :=
    GlobalTheory.T.exists_rigidified_cubical_root_polarisation_etale F (GlobalTheory.LowChart.W F w) (GlobalTheory.LowChart.isAdicComplete_completedStalkSiegelFibrePower F w) (GlobalTheory.LowChart.toPow F w ≫ (GlobalTheory.LowChart.powA F r).hom)

  let pt : Fin r → (𝟙_ (Over (Sp R')) ⟶ B) := fun i => Over.homMk
    (hpb.1.lift (spMap ρ ≫ GlobalTheory.LowChart.toPow F w ≫ (GlobalTheory.LowChart.coord F i).left) (𝟙 _) (by
      rw [Category.id_comp, Category.assoc, Category.assoc, Over.w (GlobalTheory.LowChart.coord F i)])) (hpb.1.lift_snd _ _ _)
  have hpt : ∀ i, (pt i).left ≫ β = spMap ρ ≫ GlobalTheory.LowChart.toPow F w ≫ (GlobalTheory.LowChart.coord F i).left := fun i =>
    hpb.1.lift_fst _ _ _
  let c : (Fin r → ℤ) → (𝟙_ (Over (Sp R')) ⟶ B) := fun a => ∏ i, pt i ^ a i
  have hc : ∀ a a', c (a + a') = c a * c a' := fun a a' => by
    simp only [c, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  obtain ⟨τ, hτg, hτs, hτa⟩ := GlobalTheory.TauLocal.exists_tau_local M cub c hc
  have hab : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) hpb.1 F.univ.ab.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) hpb.1 F.univ.ab.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb.1 F.univ.ab.geomConnected }
  have hdim : SmoothOfRelativeDimension h B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange h).of_isPullback hpb.1
      (GlobalTheory.SiegSharpCover.smoothDim F.univ (by omega) (GlobalTheory.LowChart.isUnit_zetaAway n hn) (isUnit_natCast (show n ≠ 0 by omega)))

  let T : TautBase (cycAway n) R' :=
    { b := ρ.comp (GlobalTheory.LowChart.base F w)
      B := B
      isAb := hab
      g := h
      smoothDim := hdim
      M := M
      cub := cub
      ample := hamp
      ktriv := hk
      r := r
      c₀ := c
      c₀_add := hc
      τ₀ := τ
      τ₀_gen := hτg
      τ₀_symm := hτs
      τ₀_add := hτa }
  have hcomp : IsNoetherianRing R' := by
    algebraize [ρ]
    exact Algebra.FiniteType.isNoetherianRing (GlobalTheory.LowChart.W F w) R'
  obtain ⟨hEt, hur⟩ := etCompl F w R' ρ hloc hfin het
  have hcart : IsGrpPullback B F.univ.A ((spMap ρ ≫ GlobalTheory.LowChart.toPow F w) ≫ (GlobalTheory.LowChart.powA F r).hom) β := by
    rw [Category.assoc]; exact hpb
  have hsingle : ∀ i, c (Pi.single i 1) = pt i := fun i => by
    classical
    show ∏ j, pt j ^ (Pi.single i 1 : Fin r → ℤ) j = _
    rw [Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zpow_zero]) (by simp),
      Pi.single_eq_same, zpow_one]
  let L : LowBase (zetaAway n) n :=
    { h := h
      F := F
      W := R'
      noeth := hcomp
      complete := hc'
      T := T
      u := spMap ρ ≫ GlobalTheory.LowChart.toPow F w
      u_et := hEt
      u_sep := hur
      u_base := by
        show _ = spMap (ρ.comp (GlobalTheory.LowChart.base F w))
        rw [spMap_comp', GlobalTheory.LowChart.spMap_base, Category.assoc]
      dim := rfl
      β := β
      β₂ := β₂
      cart := hcart
      sq := hsq
      lb := hiso
      coord := fun i => by
        show (c (Pi.single i 1)).left ≫ β = _
        rw [hsingle, hpt, Category.assoc] }

  obtain ⟨V', _, _, _, f, κ, hV', hdvr', hfi, hff, hfl, hκl, hκρ⟩ :=
    GlobalTheory.T.exists_completeDVR_of_finite_etale_baseChange (GlobalTheory.LowChart.W F w) R' V₁ ρ ψ hloc hfin het hV0 hdvr hψl
  have hspec : spMap κ ≫ (spMap ρ ≫ GlobalTheory.LowChart.toPow F w) = spMap f ≫ v := by
    rw [← Category.assoc, ← spMap_comp', hκρ, spMap_comp', Category.assoc, hψ]
  have hb : κ.comp T.b = f.comp b₁ := by
    have e : spMap (κ.comp T.b) = spMap (f.comp b₁) := by
      show spMap (κ.comp (ρ.comp (GlobalTheory.LowChart.base F w))) = _
      rw [spMap_comp', spMap_comp', spMap_comp', GlobalTheory.LowChart.spMap_base, ← hs]
      simpa only [Category.assoc] using congrArg (· ≫ GlobalTheory.LowChart.toO F r) hspec
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

  let SA := (GlobalTheory.LowChart.siegAt F v _ hs).A
  have hSA : IsGrpPullback SA F.univ.A (v ≫ (GlobalTheory.LowChart.powA F r).hom)
      (Pdiv.PullbackComparison.pφ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A) :=
    Pdiv.PullbackComparison.isGrpPullback _ _
  have hB' : IsGrpPullback ((Over.pullback (spMap f)).obj SA) SA (spMap f) (Pdiv.PullbackComparison.pφ (spMap f) SA) :=
    Pdiv.PullbackComparison.isGrpPullback _ _
  have hcomm : spMap κ ≫ ((spMap ρ ≫ GlobalTheory.LowChart.toPow F w) ≫ (GlobalTheory.LowChart.powA F r).hom) =
      spMap f ≫ (v ≫ (GlobalTheory.LowChart.powA F r).hom) := by
    rw [← Category.assoc, hspec, Category.assoc]
  obtain ⟨β'', hβ'', hββ⟩ := GlobalTheory.isGrpPullback_paste F.univ.A B SA ((Over.pullback (spMap f)).obj SA) _ _ (spMap f)
    (spMap κ) β _ _ hcart hSA hB' hcomm
  obtain ⟨β₂', hsq'⟩ : ∃ β₂', IsSquare β'' β₂' := ⟨_, GlobalTheory.LamPull.exists_isSquare hβ''.1.w⟩
  refine ⟨L, V', inferInstance, inferInstance, inferInstance, f, κ, AddEquiv.refl _, rfl, hV', hdvr', hfi, hff, hfl, hκl, hb,
    (Over.pullback (spMap f)).obj SA, inferInstance, Pdiv.PullbackComparison.pφ (spMap f) SA, β'', Pdiv.PullbackComparison.pφ₂ (spMap f) SA, β₂', hB',
    hβ'', Pdiv.PullbackComparison.isSquare _ _, hsq', ?_, ?_⟩
  · have key : β₂' ≫ β₂ = Pdiv.PullbackComparison.pφ₂ (spMap f) SA ≫ Pdiv.PullbackComparison.pφ₂ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A :=
      GlobalTheory.LamPull.isSquare_unique (isSquare_comp hsq' hsq)
        (by rw [hββ]; exact isSquare_comp (Pdiv.PullbackComparison.isSquare _ _) (Pdiv.PullbackComparison.isSquare _ _))
    have e1 : LBIso ((abelian₂ B M.L).pull β₂') (F.univ.P.pull (β₂' ≫ β₂)) := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hiso β₂' rfl
    have e2 : LBIso (F.univ.P.pull (Pdiv.PullbackComparison.pφ₂ (spMap f) SA ≫ Pdiv.PullbackComparison.pφ₂ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A))
        ((F.univ.P.pull (Pdiv.PullbackComparison.pφ₂ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A)).pull (Pdiv.PullbackComparison.pφ₂ (spMap f) SA)) :=
      GlobalTheory.GenSpread.lbIso_pull_pull F.univ.isLB _ rfl
    rw [key] at e1
    exact LBIso.trans (pull_isLB (pull_isLB F.univ.isLB _) _) (pull_isLB F.univ.isLB _)
      (pull_isLB (DVR.linComb_isLB M.L M.isLB _ _) _) (LBIso.symm e2) (LBIso.symm e1)
  · intro a
    let q : Fin r → (Over.mk (spMap κ ≫ ((spMap ρ ≫ GlobalTheory.LowChart.toPow F w) ≫ (GlobalTheory.LowChart.powA F r).hom)) ⟶ F.univ.A) :=
      fun i => Over.homMk (spMap f ≫ v ≫ (GlobalTheory.LowChart.coord F i).left) (by
        show _ = spMap κ ≫ _
        rw [hcomm, Category.assoc, Category.assoc, Over.w (GlobalTheory.LowChart.coord F i)])
    have cA : (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ≫ SA.hom = 𝟙 _ := Over.w _
    have h0 : (spMap f ≫ (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left) ≫ SA.hom = 𝟙 _ ≫ spMap f := by
      rw [Category.assoc, cA]
      simp
    obtain ⟨x, lf, ls⟩ : ∃ x : Sp V' ⟶ ((Over.pullback (spMap f)).obj SA).left,
        x ≫ Pdiv.PullbackComparison.pφ (spMap f) SA = spMap f ≫ (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ∧
          x ≫ ((Over.pullback (spMap f)).obj SA).hom = 𝟙 _ :=
      ⟨hB'.1.lift _ _ h0, hB'.1.lift_fst _ _ _, hB'.1.lift_snd _ _ _⟩
    refine ⟨x, ls, lf, ?_⟩
    have e1 := prodPush hSA (GlobalTheory.LowChart.ptAt F v _ hs) _ q (spMap f) hcomm.symm
      (fun i => by rw [GlobalTheory.LowChart.ptAt_left]; rfl) ((n : ℤ) • a)
    have e2 := prodPush hcart pt _ q (spMap κ) rfl (fun i => by
      rw [hpt]
      show _ = spMap f ≫ v ≫ _
      simpa only [Category.assoc] using congrArg (· ≫ (GlobalTheory.LowChart.coord F i).left) hspec) ((n : ℤ) • a)
    apply hcart.1.hom_ext
    · calc (x ≫ β'') ≫ β = x ≫ Pdiv.PullbackComparison.pφ (spMap f) SA ≫ Pdiv.PullbackComparison.pφ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A := by
            rw [Category.assoc, hββ]
        _ = spMap f ≫ (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ≫
            Pdiv.PullbackComparison.pφ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A :=
          (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Pdiv.PullbackComparison.pφ (v ≫ (GlobalTheory.LowChart.powA F r).hom) F.univ.A) lf).trans
            (Category.assoc _ _ _))
        _ = (∏ i, q i ^ ((n : ℤ) • a) i).left := e1
        _ = (spMap κ ≫ (c ((n : ℤ) • a)).left) ≫ β := e2.symm.trans (Category.assoc _ _ _).symm
    · calc (x ≫ β'') ≫ B.hom = x ≫ ((Over.pullback (spMap f)).obj SA).hom ≫ spMap κ := by
            rw [Category.assoc, hβ''.1.w]
        _ = spMap κ := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ spMap κ) ls).trans (Category.id_comp _))
        _ = spMap κ ≫ (c ((n : ℤ) • a)).left ≫ B.hom := by rw [Over.w (c ((n : ℤ) • a))]; exact (Category.comp_id _).symm
        _ = (spMap κ ≫ (c ((n : ℤ) • a)).left) ≫ B.hom := (Category.assoc _ _ _).symm

end GlobalTheory.LowLift
