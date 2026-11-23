import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallCompleteDvrDominating
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialDataStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.Poinc.ChartTraitForm

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear in

theorem exists_pull {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I')
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ (D' : DegData R' I') (_ : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
      (_ : Unif I' D' A' ((Over.pullback (spMap g)).obj G)) (gA : A'.A.left ⟶ A.A.left),
      IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA ∧ LBIso A'.L (A.L.pull gA) := by
  have hP : PolBaseChangeSt := polBaseChange_holds
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hg)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) =
      pullback.fst G.hom (spMap g) := Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec ((Over.pullback (specOf g)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) :=
    ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
      rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig,
      pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨D', hD, A', U', gA, gpA, LBIso.symm tA⟩

theorem isMonomial_pull {R W : Type} [CommRing R] [IsDomain R] [CommRing W] [IsDomain W] [IsLocalRing W] {κ : R →+* W}
    {D : DegPre R} {D' : DegPre W} (hD : IsPullDeg κ D D') {m : ℕ} {r : Fin m → R}
    {B : Fin m → LinearMap.BilinForm ℤ D.X} (h : IsMonomial D r B) {ϖ : W} {a : Fin m → ℕ}
    (ha : ∀ k, Associated (κ (r k)) (ϖ ^ a k)) (β : LinearMap.BilinForm ℤ D'.X)
    (hβ : ∀ y, β y y = ∑ k, (a k : ℤ) * B k (hD.xe y) (hD.xe y)) : IsMonomial D' ![ϖ] ![β] := by
  intro y
  obtain ⟨u, n, hn, hc⟩ := h (hD.xe y)
  obtain ⟨u', hc'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD y _ hc
  have h₁ : Associated (ϖ ^ ∑ k, a k * n k) (u' * κ (u * ∏ i, r i ^ n i)) := by
    refine Associated.symm ((associated_unit_mul_left _ _ u'.isUnit).trans ?_)
    rw [map_mul, map_prod, ← Finset.prod_pow_eq_pow_sum]
    refine (associated_unit_mul_left _ _ (u.isUnit.map κ)).trans (Associated.prod _ _ _ fun i _ => ?_)
    rw [map_pow, pow_mul]
    exact (ha i).pow_pow
  obtain ⟨v, hv⟩ := h₁
  refine ⟨v, ![∑ k, a k * n k], fun i => ?_, ?_⟩
  · fin_cases i
    simp only [Fin.zero_eta, Matrix.cons_val_zero, hβ, hn]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rw [Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_zero, mul_comm, hv]
    exact hc'

theorem exists_trait : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) (S : Scheme.{0}) (j : F.X ⟶ S)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (ξ : Sp V ⟶ S), UnifOver F j ξ Q →
    ∀ (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (R' : Type) [CommRing R'] [IsDomain R']
      [IsLocalRing R'] (ρ : V →+* R') (r : Fin m → R') (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X),
      IsCN R' → Function.Injective ρ → ρ.Finite → IsLocalHom ρ → (∀ k, r k ^ 2 = ρ (t k)) → (∀ k, t k ≠ 0) →
      (∀ k a b, δ k a b = δ k b a) → Refines Q ρ D.toPre e →
      IsMonomial D.toPre r (fun k => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ k)) →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W], IsAdicComplete (maximalIdeal W) W →
    ∀ κ : R' →+* W, Function.Injective κ → IsLocalHom κ →
      ∃ (T : Trait F) (σ : W →+* T.V) (c : Fin m → ℕ) (e' : T.D.toPre.X ≃+ Q.X), Function.Bijective σ ∧
        jK T.V ≫ spMap σ ≫ spMap κ ≫ spMap ρ ≫ ξ = T.y ≫ j ∧ (∀ k, Associated (σ (κ (ρ (t k)))) (T.ϖ ^ c k)) ∧
        ∀ a b, T.β a b = ∑ k, (c k : ℤ) * δ k (e' a) (e' b) := by
  intro o _ ζ g n F S j V _ _ _ Q ξ hUO m t δ R' _ _ _ ρ r D e hR' hρ hρf _ hr ht hδ hRef hmon W _ _ _ hW κ hκ hκl
  obtain ⟨G', _, _, A, U, y', α, α₂, hG, hy, hα, hsq, hL⟩ := hUO.2 R' ρ hR' hρ hρf D e hRef
  have h0 : CharZero R' := hR'.2.2.2
  have hW0 : CharZero W := charZero_of_injective_ringHom hκ
  obtain ⟨D', hD, A', U', gA, gpA, tA⟩ := exists_pull (I := maximalIdeal R') (I' := maximalIdeal W)
    ⟨hR'.1, inferInstance, hR'.2.1, hR'.2.2.1⟩ ⟨inferInstance, inferInstance, inferInstance, hW⟩ κ hκ
    (Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit κ a ha) hG U
  obtain ⟨β₂, hβ₂, hΛ⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ A.A A'.A gA gpA
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hr0 : ∀ k, κ (r k) ≠ 0 := fun k h => ht k (hρ (hκ (by rw [← hr, map_pow, h]; simp)))
  choose a u hu using fun k => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hr0 k) hϖ
  have ha : ∀ k, Associated (κ (r k)) (ϖ ^ a k) := fun k => by
    rw [hu]; exact associated_unit_mul_left _ _ (u k).isUnit
  let e' : D'.toPre.X ≃+ Q.X := hD.xe.trans e
  let β : LinearMap.BilinForm ℤ D'.toPre.X := ∑ k, ((2 * a k : ℕ) : ℤ) • pull e'.toIntLinearEquiv.toLinearMap (δ k)
  have hβ : ∀ x y, β x y = ∑ k, ((2 * a k : ℕ) : ℤ) * δ k (e' x) (e' y) := fun x y => by
    simp only [β, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rfl
  have sq : spMap (GlobalTheory.ArcPull.fracMap hκ) ≫ jK R' = jK W ≫ spMap κ :=
    (GlobalTheory.ArcPull.fracMap_sq hκ).symm.trans (Category.id_comp _)
  let T : Trait F :=
    { V := W, complete := hW, ϖ := ϖ, irr := hϖ, y := spMap (GlobalTheory.ArcPull.fracMap hκ) ≫ y'
      G := (Over.pullback (spMap κ)).obj G', semi := IsSemiAbelian.pullback _ G' hG, D := D', A := A', U := U'
      α := gA ≫ α, α₂ := β₂ ≫ α₂, cart := gpA.comp hα
      sq := ⟨by rw [Category.assoc, hsq.1, ← Category.assoc, hβ₂.1, Category.assoc],
        by rw [Category.assoc, hsq.2, ← Category.assoc, hβ₂.2, Category.assoc]⟩
      lb := hΛ A.L A'.L _ F.univ.P α₂ A.isLB A'.isLB F.univ.isLB tA hL
      β := β
      symm := fun x y => by
        rw [hβ, hβ]
        exact Finset.sum_congr rfl fun k _ => by rw [hδ]
      mono := isMonomial_pull hD hmon ha β fun y => by
        rw [hβ]
        refine Finset.sum_congr rfl fun k _ => ?_
        have : ((2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ k)) (hD.xe y) (hD.xe y) = 2 * δ k (e' y) (e' y) := rfl
        rw [this]
        push_cast
        ring }
  refine ⟨T, RingHom.id W, fun k => 2 * a k, e', Function.bijective_id, ?_, fun k => ?_, hβ⟩
  · show jK W ≫ spMap (RingHom.id W) ≫ spMap κ ≫ spMap ρ ≫ ξ = (spMap (GlobalTheory.ArcPull.fracMap hκ) ≫ y') ≫ j
    have : spMap (RingHom.id W) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp, Category.assoc, hy, ← Category.assoc (spMap (GlobalTheory.ArcPull.fracMap hκ)), sq, Category.assoc]
  · show Associated (κ (ρ (t k))) (ϖ ^ (2 * a k))
    rw [← hr, map_pow, mul_comm, pow_mul]
    exact (ha k).pow_pow

end GlobalTheory.Poinc.ChartTraitForm
