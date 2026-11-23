import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLinearOfIsPullUniformisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FactorPull

def ringActPull {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] [IsCommMonObj G] {O : Type} [Ring O]
    (o : RingAct G O) : RingAct ((Over.pullback f).obj G) O where
  act a := (Over.pullback f).map (o.act a)
  hom a := by have := o.hom a; infer_instance
  map_one := by rw [o.map_one, CategoryTheory.Functor.map_id]
  map_mul a b := by rw [o.map_mul, CategoryTheory.Functor.map_comp]
  map_add a b := by
    rw [o.map_add]
    exact CategoryTheory.Functor.map_mul (Over.pullback f) (o.act a) (o.act b)

open ReciprocityTheory.ChartRestriction.G.DVR in

theorem polAct_pull : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (P : Out.PolAV S) (P' : Out.PolAV S') (g : P'.A.left ⟶ P.A.left),
    IsGrpPullback P'.A P.A f g → LBIso (P.L.pull g) P'.L →
    ∀ (O : Type) [Ring O] [StarRing O] (o : P.OAct O), ∃ o' : P'.OAct O,
      ∀ a, (o'.act a).left ≫ g = g ≫ (o.act a).left := by
  intro S S' f P P' g hg hw O _ _ o
  have inj : ∀ {T : Over S'} {x y : T ⟶ P'.A}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let act : O → (P'.A ⟶ P'.A) := fun a => Over.homMk (hg.1.lift (g ≫ (o.act a).left) P'.A.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act a).left ≫ g = g ≫ (o.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ P'.A) a, pushPt hg.1.w (x ≫ act a) = pushPt hg.1.w x ≫ o.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have pm : ∀ {T : Over S'} (x y : T ⟶ P'.A), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y := fun x y =>
    map_mul (pushHom hg _) x y
  obtain ⟨w, gw'⟩ := LBIso.symm hw
  refine ⟨⟨⟨act, fun a => isMonHom_of_mul _ fun T x y => inj ?_, inj ?_, fun a b => inj ?_, fun a b => inj ?_⟩,
    fun a s => ?_⟩, ha⟩
  · have := o.hom a
    rw [pa, pm, pm, pa, pa, MonObj.mul_comp]
  · rw [← Category.id_comp (act 1), pa, o.map_one, Category.comp_id]
  · rw [← Category.id_comp (act (a * b)), pa, pa, ← Category.id_comp (act b), pa, o.map_mul, Category.assoc]
  · refine Eq.trans ?_ (pm (act a) (act b)).symm
    rw [← Category.id_comp (act (a + b)), ← Category.id_comp (act a), ← Category.id_comp (act b), pa, pa, pa, o.map_add]
    exact MonObj.comp_mul _ _ _
  · obtain ⟨U, hU, t, ht⟩ := o.rosati a (f s)
    let V : (P'.A ⊗ P'.A).left.Opens := (P'.A ⊗ P'.A).hom ⁻¹ᵁ (f ⁻¹ᵁ U)
    let T' : Over S' := Over.mk (V.ι ≫ (P'.A ⊗ P'.A).hom)
    let j : T' ⟶ P'.A ⊗ P'.A := Over.homMk V.ι rfl
    let m := lift (pushPt hg.1.w (j ≫ fst _ _)) (pushPt hg.1.w (j ≫ snd _ _))
    obtain ⟨n, hn⟩ : ∃ n : V.toScheme ⟶ ((P.A ⊗ P.A).hom ⁻¹ᵁ U).toScheme, n ≫ ((P.A ⊗ P.A).hom ⁻¹ᵁ U).ι = m.left :=
      ⟨IsOpenImmersion.lift _ m.left (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y ∈ U) (Over.w m)).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨t', ht', -⟩ := exists_gen P.isLB (φ' := fun i => (V.ι ≫ rosatiφ P'.A (act a) (act (star a)) i) ≫ g)
      (ε' := rosatiε) (fun W _ k => by
        have p₁ := prod_ros (o.act a) (o.act (star a)) (pushPt hg.1.w (j ≫ fst _ _)) (pushPt hg.1.w (j ≫ snd _ _)) k
        have p₂ := prod_ros (act a) (act (star a)) (j ≫ fst _ _) (j ≫ snd _ _) (fun q => k (q ≫ g))
        rw [← comp_lift, lift_fst_snd, Category.comp_id] at p₂
        rw [← pa, ← pa, ← pm, ← pm] at p₁
        exact ((Finset.prod_congr rfl fun i _ => by
          show k (n ≫ _ ≫ _) ^ _ = k (m.left ≫ _) ^ _
          rw [← Category.assoc, hn]).trans p₁).trans p₂.symm) (LB.pullGen P.L _ _ t n) (pullGen_isGen _ _ _ _ ht n)
    exact ⟨f ⁻¹ᵁ U, hU, exists_down ((isGen_iff w).1 gw') P.isLB P'.isLB t' ht'⟩

theorem degAct_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (O : Type) [Ring O] [StarRing O] [Module O D.X] (ιD : D.OAct O), ∃ (_ : Module O D'.X) (ιD' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) ∧ (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) := by
  intro hG R R' _ _ _ _ φ D D' hD O _ _ _ ιD
  have gp := pull_grp hD
  obtain ⟨o', ho'⟩ := polAct_pull _ _ _ D.P D'.P _ gp (LBIso.symm ⟨hD.w, hD.w_gen⟩) O ιD.onB
  letI inst : Module O D'.X := hD.xe.module O
  have hs : ∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y := fun a y =>
    hD.xe.apply_symm_apply _
  have he : ∀ a, o'.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a) := fun a => by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · have := ho' a
      simp only [Over.comp_left, Category.assoc, Over.pullback_map_left] at this ⊢
      erw [pullback.lift_fst]
      exact this
    · exact (Over.w (o'.act a ≫ hD.e.hom)).trans
        (Over.w (hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a))).symm
  refine ⟨inst, ⟨o', fun a y => ?_, fun a => ?_⟩, hs, he⟩
  · refine Over.OverMorphism.ext (gp.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [hD.c_pr, hs, ιD.c_lin, Over.comp_left, Over.comp_left, Category.assoc, ho', ← Category.assoc,
      ← Category.assoc (D'.c y).left, hD.c_pr]
  · exact tauBal_of_isPullDeg hG R R' φ D D' hD _ _ _ _ (ιD.onB.hom a) (ιD.onB.hom (star a)) (ιD.onB.rosati a)
      (he a) (he (star a)) _ _ _ _ (hs a) (hs (star a)) (ιD.c_lin a) (ιD.c_lin (star a)) (ιD.tau_bal a)

open GlobalTheory.TorusCoord GlobalTheory.PullLinear in

theorem oLinear_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (U : Unif I D A G) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' → ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), U.OLinear O ιD ιA ιG → (∀ a, (ιG'.act a) ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf φ)).map (ιG.act a)) → (∀ a, (Over.pullback (jK R')).map (ιG'.act a) ≫ U'.gen.hom = U'.gen.hom ≫ ιA'.act a) → (∀ (a : O) (y : D'.toPre.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) → U'.OLinear O ιD' ιA' ιG' := by
  intro R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc _ U U' hU O _ _ _ _ ιD ιD' ιA ιA' ιG ιG'
    hlin hG hgen hx hB
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  choose h hf hpt _hw using H
  have hact : ∀ (e : ℕ) (a : O), ((Over.pullback (thick R' I' e)).map (ιG'.act a)).left ≫ h e =
      h e ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left := by
    intro e a
    have hf' : h e ≫ pullback.fst G.hom (thick R I e) = pullback.fst G'.hom (thick R' I' e) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ) := hf e
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono (pullback.fst G.hom (thick R I e)) := inferInstance
    rw [← cancel_mono (pullback.fst G.hom (thick R I e)), Category.assoc, Category.assoc, map_left_fst,
      ← Category.assoc (h e), hf', ← Category.assoc, map_left_fst, Category.assoc,
      act_proj _ bc.hom (hG a), Category.assoc, Category.assoc, Category.assoc]
  have hq : ∀ (e : ℕ) (a : O), (Over.pullback (thick R' I' e)).map (ιG'.act a) ≫ (U'.gt e).q =
      (U'.gt e).q ≫ (Over.pullback (thick R' I' e)).map (ιD'.onB.act a) := by
    intro e a
    have k : ∀ {S : Type} [CommRing S] [IsDomain S] {J : Ideal S} {E : DegPre S}
        {K : Over (Spec (CommRingCat.of S))} [GrpObj K] [IsCommMonObj K] (g : GtCoord J E e K)
        (u : E.P.A ⟶ E.P.A), (g.q ≫ (Over.pullback (thick S J e)).map u).left ≫
          pullback.fst E.P.A.hom (thick S J e) = g.pG.left ≫ u.left := by
      intro S _ _ J E K _ _ g u
      rw [Over.comp_left, Category.assoc, map_left_fst, PullLinear.pG_left, Category.assoc]
    have k₁ : ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ (U.gt e).pG.left =
        (U.gt e).pG.left ≫ (ιD.onB.act a).left := by
      rw [← k, ← hlin.q_lin e a]
      exact (Category.assoc _ _ _).symm
    have k₂ : (Over.map (thick R' I' e)).map ((Over.pullback (thick R' I' e)).map (ιG'.act a)) ≫
        (U'.gt e).pG = (U'.gt e).pG ≫ ιD'.onB.act a := by
      refine ext_of_iso_pullback _ hD.e ?_
      change (((Over.pullback (thick R' I' e)).map (ιG'.act a)).left ≫ (U'.gt e).pG.left) ≫ _ =
        ((U'.gt e).pG.left ≫ (ιD'.onB.act a).left) ≫ _
      rw [Category.assoc, Category.assoc, act_proj _ hD.e.hom (hB a), (hpt e).1,
        ← Category.assoc (U'.gt e).pG.left, (hpt e).1, ← Category.assoc, hact, Category.assoc,
        Category.assoc, k₁]
    refine ext_of_pullback _ ?_
    rw [k, Over.comp_left, Category.assoc]
    exact congrArg (·.left) k₂
  refine ⟨hgen, hq, fun e a => ?_⟩
  obtain ⟨t, ht, hi⟩ := hlin.i_lin e a
  have := ιD'.onB.hom a
  have hk : ((U'.gt e).i ≫ (Over.pullback (thick R' I' e)).map (ιG'.act a)) ≫ (U'.gt e).q =
      toUnit _ ≫ η[thickObj R' I' e D'.toPre.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, (U'.gt e).isKernel.w, Category.assoc,
      IsMonHom.one_hom]
  have hi' := (U'.gt e).isKernel.lift_fst _ _ hk
  generalize (U'.gt e).isKernel.lift _ _ hk = t' at hi'
  refine ⟨t', ?_, hi'.symm⟩
  obtain ⟨s, τ, hτ⟩ := exists_point (U.gt e) (U'.gt e) (hpt e).1 ((hpt e).2 0).1 (𝟙 _)
  have hτ' : ((τ ≫ t) ≫ (U.gt e).i).left = (t' ≫ (U'.gt e).i).left ≫ h e := by
    rw [Category.assoc, ← hi, ← Category.assoc, Over.comp_left, hτ, hi', Category.id_comp,
      Over.comp_left, Category.assoc, Category.assoc, hact]
  intro χ
  refine unit_ext fun z _ => ?_
  have e₁ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 χ).1 ((hpt e).2 χ).2 t' (τ ≫ t) hτ' z
  have e₂ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 (star a • χ)).1 ((hpt e).2 (star a • χ)).2
    (𝟙 _) τ hτ z
  have e₃ := (torusEndOf_iff _ _ t).1 ht _ τ.left z (hD.xe χ)
  rw [hx] at e₂
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t'.left z ⊤ trivial _)).trans ?_
  rw [Category.id_comp]
  exact e₁.symm.trans (e₃.trans e₂)

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear in

theorem unif_pull {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I')
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G)
    (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O)
    (ιG : RingAct G O) (hlin : U.OLinear O ιD ιA ιG) :
    ∃ (D' : DegData R' I') (hD : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing R'))))
      (U' : Unif I' D' A' ((Over.pullback (specOf g)).obj G)), IsPullUnif g hD (Iso.refl _) U U' ∧
      ∃ (ιG' : RingAct ((Over.pullback (specOf g)).obj G) O) (ιA' : A'.OAct O),
        (∀ a, (ιG'.act a) ≫ (Iso.refl _).hom = (Iso.refl _).hom ≫ (Over.pullback (specOf g)).map (ιG.act a)) ∧
        ∀ a, (Over.pullback (jK R')).map (ιG'.act a) ≫ U'.gen.hom = U'.gen.hom ≫ ιA'.act a := by
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have hP := hL.polBaseChange
  have hU := h4.unifBaseChange
  have hψ := h5.psiOnExists
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hg)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = pullback.fst G.hom (spMap g) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec ((Over.pullback (specOf g)).obj G))
      (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) := ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
    rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, hgenU, hPU⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  obtain ⟨oA', hoA'⟩ := polAct_pull _ _ (spMap (fracMap hg)) A A' gA gpA tA O ιA
  let ιG' : RingAct ((Over.pullback (specOf g)).obj G) O := ringActPull (specOf g) ιG
  refine ⟨D', hD, A', U', hPU, ιG', oA', fun x => (Category.comp_id _).trans (Category.id_comp _).symm, fun x => ?_⟩
  have actA : (ιA.act x).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      U.gen.inv.left ≫ pullback.fst G.hom (jK R) ≫ (ιG.act x).left := by
    have e : ιA.act x ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK R)).map (ιG.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (hlin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  rw [hgenU]
  apply Over.OverMorphism.ext
  apply (gpA.comp gpG).1.hom_ext
  · have a₁ : ((Over.pullback (jK R')).map (ιG'.act x)).left ≫ pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') =
        pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ (ιG'.act x).left := pullback.lift_fst _ _ _
    have a₂ : (ιG'.act x).left ≫ pullback.fst G.hom (spMap g) =
        pullback.fst G.hom (spMap g) ≫ (ιG.act x).left := pullback.lift_fst _ _ _
    rw [Over.comp_left, Category.assoc, heA, ← Category.assoc, a₁, Category.assoc, a₂, Over.comp_left, Category.assoc,
      ← Category.assoc (oA'.act x).left, hoA', Category.assoc, actA, ← Category.assoc, ← heA]
    simp only [Category.assoc]
  · rw [Over.w, Over.w]

section abelian₂

open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull GlobalTheory.PolDeg

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B C : Over S} {B₁ C₁ : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj C]
  [IsCommMonObj C] [GrpObj B₁] [IsCommMonObj B₁] [GrpObj C₁] [IsCommMonObj C₁] {β : B₁.left ⟶ B.left}
  {δ : C₁.left ⟶ C.left} {M : LB B.left} {N : LB C.left} {M₁ : LB B₁.left} {N₁ : LB C₁.left}

theorem lift_sq (gB : IsGrpPullback B₁ B f β) (gC : IsGrpPullback C₁ C f δ) {u v : B ⟶ C} {u₁ v₁ : B₁ ⟶ C₁}
    (hu : u₁.left ≫ δ = β ≫ u.left) (hv : v₁.left ≫ δ = β ≫ v.left) :
    (lift (fst B₁ B₁ ≫ u₁) (snd B₁ B₁ ≫ v₁) : G2 B₁ ⟶ G2 C₁).left ≫ sqOf gC =
      sqOf gB ≫ (lift (fst B B ≫ u) (snd B B ≫ v) : G2 B ⟶ G2 C).left := by
  apply pullback.hom_ext
  · show _ ≫ (fst C C).left = _ ≫ (fst C C).left
    rw [Category.assoc, (isSquare_sqOf gC).1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
      ← Over.comp_left, lift_fst, Over.comp_left, Over.comp_left, Category.assoc, hu, ← Category.assoc (sqOf gB),
      (isSquare_sqOf gB).1, Category.assoc]
  · show _ ≫ (snd C C).left = _ ≫ (snd C C).left
    rw [Category.assoc, (isSquare_sqOf gC).2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
      ← Over.comp_left, lift_snd, Over.comp_left, Over.comp_left, Category.assoc, hv, ← Category.assoc (sqOf gB),
      (isSquare_sqOf gB).2, Category.assoc]

theorem gw_lam (gB : IsGrpPullback B₁ B f β) (v : LB.Iso M₁ (M.pull β)) {Z : Scheme.{0}} (p : Z ⟶ (G2 B₁).left) (z : Z)
    {J J₁} (hJ : Good M z J) (hJ₁ : Good M₁ z J₁) :
    Geo.Tor.gw (lamIso gB v) p z (fun I => J ((p ≫ sqOf gB) ≫ lamφ B I)) (fun I => J₁ (p ≫ lamφ B₁ I)) =
      ∏ I, om v z J J₁ (p ≫ lamφ B₁ I) ^ lamε I := by
  rw [gw_lamIso gB v p z _ _ (fun I => by
    have := hJ ((p ≫ sqOf gB) ≫ lamφ B I)
    rw [Category.assoc, sqOf_lamφ, ← Category.assoc] at this ⊢
    exact this) (fun I => hJ₁ (p ≫ lamφ B₁ I))]
  refine Finset.prod_congr rfl fun I _ => ?_
  rw [Category.assoc, sqOf_lamφ, ← Category.assoc]
  rfl

theorem lam_down (gB : IsGrpPullback B₁ B f β) (gC : IsGrpPullback C₁ C f δ) (hM : M.IsLB) (hN : N.IsLB)
    (hM₁ : M₁.IsLB) (hN₁ : N₁.IsLB) (v : LB.Iso M₁ (M.pull β)) (hv : v.IsGen) (v' : LB.Iso N₁ (N.pull δ))
    (hv' : v'.IsGen) {m : (G2 B).left ⟶ (G2 C).left} {m₁ : (G2 B₁).left ⟶ (G2 C₁).left}
    (hm : m₁ ≫ sqOf gC = sqOf gB ≫ m) (w : LB.Iso (abelian₂ B M) ((abelian₂ C N).pull m)) (hw : w.IsGen) :
    ∃ w₁ : LB.Iso (abelian₂ B₁ M₁) ((abelian₂ C₁ N₁).pull m₁), w₁.IsGen ∧
      ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 B₁).left) (z : Z) I J I₁ J₁, Good N z I → Good M z J → Good N₁ z I₁ →
        Good M₁ z J₁ → (∏ k, om v' z I I₁ ((p ≫ m₁) ≫ lamφ C₁ k) ^ lamε k) * lamVal w₁ p z I₁ J₁ =
          lamVal w (p ≫ sqOf gB) z I J * ∏ k, om v z J J₁ (p ≫ lamφ B₁ k) ^ lamε k := by
  have lM : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have lN : (abelian₂ C N).IsLB := DVR.linComb_isLB _ hN _ _
  have lM₁ : (abelian₂ B₁ M₁).IsLB := DVR.linComb_isLB _ hM₁ _ _
  have lN₁ : (abelian₂ C₁ N₁).IsLB := DVR.linComb_isLB _ hN₁ _ _
  have pw := (isGen_iff _).1 hw
  have pv := pgen_lamIso gB v ((isGen_iff v).1 hv)
  have pv' := pgen_lamIso gC v' ((isGen_iff v').1 hv')
  obtain ⟨w₂, T⟩ := exists_comp lM w (lamIso gB v) pw pv lN lM₁
  have p₂ := pgen_pullCongr hm.symm (T.pgen_comp lM pw pv)
  obtain ⟨w₁, T'⟩ := exists_cancel lN (lamIso gC v') (pullCongr hm.symm w₂) pv' p₂ lN₁ lM₁
  refine ⟨w₁, (isGen_iff _).2 (T'.pgen_cancel lN pv' p₂), fun Z p z I J I₁ J₁ hI hJ hI₁ hJ₁ => ?_⟩
  have e : (p ≫ m₁) ≫ sqOf gC = (p ≫ sqOf gB) ≫ m := by rw [Category.assoc, hm, Category.assoc]
  have t := T Z p z (fun k => I (((p ≫ sqOf gB) ≫ m) ≫ lamφ C k))
    (fun k => J ((p ≫ sqOf gB) ≫ lamφ B k)) (fun k => J₁ (p ≫ lamφ B₁ k))
    (Set.mem_iInter.2 fun k => hI (((p ≫ sqOf gB) ≫ m) ≫ lamφ C k))
    (Set.mem_iInter.2 fun k => hJ ((p ≫ sqOf gB) ≫ lamφ B k))
    (Set.mem_iInter.2 fun k => hJ₁ (p ≫ lamφ B₁ k))
  have t' := T' Z p z (fun k => I (((p ≫ m₁) ≫ sqOf gC) ≫ lamφ C k))
    (fun k => I₁ ((p ≫ m₁) ≫ lamφ C₁ k)) (fun k => J₁ (p ≫ lamφ B₁ k))
    (Set.mem_iInter.2 fun k => hI (((p ≫ m₁) ≫ sqOf gC) ≫ lamφ C k))
    (Set.mem_iInter.2 fun k => hI₁ ((p ≫ m₁) ≫ lamφ C₁ k))
    (Set.mem_iInter.2 fun k => hJ₁ (p ≫ lamφ B₁ k))
  replace t' := (gw_pullCongr _ _ _ _ _ _).symm.trans (t'.trans (congrArg₂ (· * ·) (gw_lam gC v' (p ≫ m₁) z hI hI₁) rfl))
  rw [e] at t'
  replace t' := (t.trans (congrArg₂ (· * ·) rfl (gw_lam gB v p z hJ hJ₁))).symm.trans t'
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) (t'.symm.trans (congrArg₂ (· * ·) ?_ rfl))
  · show Geo.Tor.gw w₁ p z (fun k => I₁ (p ≫ m₁ ≫ lamφ C₁ k)) (fun k => J₁ (p ≫ lamφ B₁ k)) = _
    simp only [Category.assoc]
  · show _ = Geo.Tor.gw w (p ≫ sqOf gB) z (fun k => I ((p ≫ sqOf gB) ≫ m ≫ lamφ C k))
      (fun k => J ((p ≫ sqOf gB) ≫ lamφ B k))
    simp only [Category.assoc]

omit [IsCommMonObj B] [IsCommMonObj C] [IsCommMonObj B₁] [IsCommMonObj C₁] in

theorem hom_pull (gB : IsGrpPullback B₁ B f β) (gC : IsGrpPullback C₁ C f δ) (u : B ⟶ C) (hu : IsMonHom u) :
    ∃ u₁ : B₁ ⟶ C₁, IsMonHom u₁ ∧ u₁.left ≫ δ = β ≫ u.left := by
  obtain ⟨e, he, he'⟩ := grpPullback_iso gB (isGrpPullback_pullback B f)
  obtain ⟨e', hd, hd'⟩ := grpPullback_iso (isGrpPullback_pullback C f) gC
  refine ⟨e.hom ≫ (Over.pullback f).map u ≫ e'.hom, inferInstance, ?_⟩
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hd', GlobalTheory.PullLinear.map_left_fst,
    ← Category.assoc, he']

omit [IsCommMonObj C] [IsCommMonObj C₁] in
theorem ext_pull (gC : IsGrpPullback C₁ C f δ) {T : Over S'} {x y : T ⟶ C₁} (h : x.left ≫ δ = y.left ≫ δ) : x = y :=
  Over.OverMorphism.ext (gC.1.hom_ext h (by rw [Over.w, Over.w]))

end abelian₂

section Factor

open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull GlobalTheory.PolDeg GlobalTheory.PullLinear
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}

theorem tau_lam {D : DegPre R} {D₁ : DegPre R'} (hD : IsPullDeg φ D D₁) (hφ : Function.Injective φ) (a b : D₁.X)
    {z : (TK R').left} {J J₁} (hJ : Good D.P.L z J) (hJ₁ : Good D₁.P.L z J₁) :
    (letI := D₁.P.isAb.comm
      ∏ k, om hD.w z J J₁ ((lift (toUnit (TK R') ≫ D₁.c a) (toUnit (TK R') ≫ D₁.c b)).left ≫ lamφ D₁.P.A k) ^ lamε k) *
      val (D.tau (hD.xe a) (hD.xe b)) (genMap hφ) z J =
      val (D₁.tau a b) (𝟙 _) z J₁ := by
  have e := tau_val hD (genMap hφ) (𝟙 _) (fracMap_sq hφ) hJ hJ₁ a b
  have p := prod_lam (DVR.cP D₁ (TK R') a) (DVR.cP D₁ (TK R') b) (om hD.w z J J₁)
  rw [← DVR.cPoint_add] at p
  simp only [Category.id_comp] at e
  refine (congrArg₂ (· * ·) p e).trans ?_
  show om hD.w z J J₁ (D₁.xK (a + b)) * (om hD.w z J J₁ (D₁.xK a))⁻¹ * (om hD.w z J J₁ (D₁.xK b))⁻¹ * _ * _ = _
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

set_option maxHeartbeats 800000 in

theorem factor_pull {D D' : DegPre R} {D₁ D₁' : DegPre R'} (hφ : Function.Injective φ) (hD : IsPullDeg φ D D₁)
    (hD' : IsPullDeg φ D' D₁') (F : Factor D D') [m : Module F.O D₁'.X] (o₁ : D₁'.OAct F.O)
    (hx : ∀ (a : F.O) (y : D₁'.X), hD'.xe (a • y) = a • hD'.xe y)
    (ho : ∀ a, (o₁.onB.act a).left ≫ proj hD' = proj hD' ≫ (F.o.onB.act a).left) :
    ∃ (inc : D₁.P.A ⟶ D₁'.P.A) (pr : D₁'.P.A ⟶ D₁.P.A) (xi : D₁.X →+ D₁'.X) (xp : D₁'.X →+ D₁.X)
      (w : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ D₁'.P.A D₁'.P.L).pull
        (lift (fst D₁.P.A D₁.P.A ≫ inc) (snd D₁.P.A D₁.P.A ≫ inc ≫ o₁.onB.act F.f) : G2 D₁.P.A ⟶ G2 D₁'.P.A).left)),
      IsMonHom inc ∧ IsMonHom pr ∧ inc ≫ pr = 𝟙 _ ∧ pr ≫ inc = o₁.onB.act F.e ∧ (∀ y, xp (xi y) = y) ∧
      (∀ z, xi (xp z) = F.e • z) ∧ (∀ y, D₁'.c (xi y) = D₁.c y ≫ inc) ∧
      (Function.Injective fun y => star F.e • F.f • xi y) ∧ (∀ z : D₁'.X, ∃ y, star F.e • z = star F.e • F.f • xi y) ∧
      w.IsGen ∧ ∀ a b z J J', Good D₁'.P.L z J → Good D₁.P.L z J' →
        val (D₁.tau a b) (𝟙 _) z J' =
          lamVal w (lift (toUnit (TK R') ≫ D₁.c a) (toUnit (TK R') ≫ D₁.c b)).left z J J' *
            val (D₁'.tau (xi a) (F.f • xi b)) (𝟙 _) z J := by
  have gp := pull_grp hD
  have gp' := pull_grp hD'
  obtain ⟨inc, mi, hi⟩ := hom_pull gp gp' F.inc F.inc_hom
  obtain ⟨pr, mp, hp⟩ := hom_pull gp' gp F.pr F.pr_hom
  obtain ⟨xi, hxi⟩ : ∃ xi : D₁.X →+ D₁'.X, ∀ y, hD'.xe (xi y) = F.xi (hD.xe y) :=
    ⟨hD'.xe.symm.toAddMonoidHom.comp (F.xi.comp hD.xe.toAddMonoidHom), fun y => hD'.xe.apply_symm_apply _⟩
  obtain ⟨xp, hxp⟩ : ∃ xp : D₁'.X →+ D₁.X, ∀ y, hD.xe (xp y) = F.xp (hD'.xe y) :=
    ⟨hD.xe.symm.toAddMonoidHom.comp (F.xp.comp hD'.xe.toAddMonoidHom), fun y => hD.xe.apply_symm_apply _⟩
  have hf : (inc ≫ o₁.onB.act F.f).left ≫ proj hD' = proj hD ≫ (F.inc ≫ F.o.onB.act F.f).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ho, ← Category.assoc, hi, Category.assoc]
  obtain ⟨w, hw, vw⟩ := lam_down gp gp' D.P.isLB D'.P.isLB D₁.P.isLB D₁'.P.isLB hD.w hD.w_gen hD'.w hD'.w_gen
    (lift_sq gp gp' hi hf) F.w F.w_gen
  have hc : ∀ y, D₁'.c (xi y) = D₁.c y ≫ inc := fun y => ext_pull gp' (by
    rw [hD'.c_pr, hxi, F.c_xi, Over.comp_left, Over.comp_left, Category.assoc, hi, ← Category.assoc (D₁.c y).left,
      hD.c_pr, Category.assoc])
  refine ⟨inc, pr, xi, xp, w, mi, mp, ext_pull gp ?_, ext_pull gp' ?_, fun y => hD.xe.injective ?_,
    fun y => hD'.xe.injective ?_, hc, fun y y' h => ?_, fun z => ?_, hw, fun a b z I₁ J₁ hI₁ hJ₁ => ?_⟩
  · rw [Over.comp_left, Category.assoc, hp, ← Category.assoc, hi, Category.assoc, ← Over.comp_left, F.inc_pr,
      Over.id_left, Over.id_left, Category.comp_id, Category.id_comp]
  · rw [Over.comp_left, Category.assoc, hi, ← Category.assoc, hp, Category.assoc, ← Over.comp_left, F.pr_inc, ho]
  · rw [hxp, hxi, F.xp_xi]
  · rw [hxi, hxp, F.xi_xp, hx]
  · have h' := congrArg hD'.xe h
    simp only [hx, hxi] at h'
    exact hD.xe.injective (F.inj h')
  · obtain ⟨y, hy⟩ := F.onto (hD'.xe z)
    refine ⟨hD.xe.symm y, hD'.xe.injective ?_⟩
    rw [hx, hx, hx, hxi, hD.xe.apply_symm_apply, hy]
  · obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB z
    obtain ⟨I, hI⟩ := DegPull.exists_good' D'.P.isLB z
    let g₀ := genMap hφ
    have sq : (TK R').hom ≫ spMap φ = g₀ ≫ (TK R).hom := (Category.id_comp _).symm.trans (fracMap_sq hφ)
    have hP : (lift (toUnit (TK R') ≫ D₁.c a) (toUnit (TK R') ≫ D₁.c b)).left ≫ sqOf gp =
        g₀ ≫ (lift (toUnit (TK R) ≫ D.c (hD.xe a)) (toUnit (TK R) ≫ D.c (hD.xe b))).left := by
      apply pullback.hom_ext
      · show _ ≫ (fst D.P.A D.P.A).left = _ ≫ (fst D.P.A D.P.A).left
        rw [Category.assoc, (isSquare_sqOf gp).1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
          ← Over.comp_left, lift_fst]
        exact cPoint_proj hD g₀ sq a
      · show _ ≫ (snd D.P.A D.P.A).left = _ ≫ (snd D.P.A D.P.A).left
        rw [Category.assoc, (isSquare_sqOf gp).2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
          ← Over.comp_left, lift_snd]
        exact cPoint_proj hD g₀ sq b
    have hQ : (lift (toUnit (TK R') ≫ D₁.c a) (toUnit (TK R') ≫ D₁.c b)).left ≫
        (lift (fst D₁.P.A D₁.P.A ≫ inc) (snd D₁.P.A D₁.P.A ≫ inc ≫ o₁.onB.act F.f) : G2 D₁.P.A ⟶ G2 D₁'.P.A).left =
        (lift (toUnit (TK R') ≫ D₁'.c (xi a)) (toUnit (TK R') ≫ D₁'.c (F.f • xi b))).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, o₁.c_lin, hc, hc]
      simp only [Category.assoc]
    have t₁ := F.tau (hD.xe a) (hD.xe b) (g₀ z) (fun ψ => I (g₀ ≫ ψ)) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => hI (g₀ ≫ ψ))
      (fun ψ => hJ (g₀ ≫ ψ))
    have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans (map_mul _ _ _)
    have n₁ : val (D.tau (hD.xe a) (hD.xe b)) (g₀ ≫ 𝟙 _) z J = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (D.tau (hD.xe a) (hD.xe b)) (𝟙 _) (g₀ z) (fun ψ => J (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z J hJ).2.2.1 _)
    have n₂ : val (D'.tau (F.xi (hD.xe a)) (F.f • F.xi (hD.xe b))) (g₀ ≫ 𝟙 _) z I =
        Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (D'.tau (F.xi (hD.xe a)) (F.f • F.xi (hD.xe b))) (𝟙 _) (g₀ z) (fun ψ => I (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z I hI).2.2.1 _)
    rw [Category.comp_id] at n₁ n₂
    have E := n₁.trans (t₂.trans (congrArg₂ (· * ·) (lamVal_comp F.w g₀ _ z I J hI hJ).symm n₂.symm))
    have K := vw _ (lift (toUnit (TK R') ≫ D₁.c a) (toUnit (TK R') ≫ D₁.c b)).left z I J I₁ J₁ hI hJ hI₁ hJ₁
    rw [hP, hQ] at K
    have a₁ := tau_lam hD hφ a b hJ hJ₁
    have a₂ := tau_lam hD' hφ (xi a) (F.f • xi b) hI hI₁
    rw [hx, hxi, hxi] at a₂
    rw [← a₁, ← a₂, E, ← _root_.mul_assoc, ← _root_.mul_assoc, mul_comm (lamVal w _ z I₁ J₁), K, mul_comm (lamVal F.w _ z I J)]

end Factor

open GlobalTheory.HalfBC GlobalTheory.PullLinear in

theorem factor_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → IsLocalHom ρ → ∃ (D₁ D₁' : DegData R' (maximalIdeal R')) (F₁ : Factor D₁.toPre D₁'.toPre) (A₁' : PolAV (Sp (FractionRing R'))) (G₁' : Over (Sp R')) (_ : GrpObj G₁') (_ : IsCommMonObj G₁') (U₁' : Unif (maximalIdeal R') D₁' A₁' G₁') (oA₁ : A₁'.OAct F₁.O) (oG₁ : RingAct G₁' F₁.O) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (inc₁ : G₁ ⟶ G₁') (pr₁ : G₁' ⟶ G₁), Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsSemiAbelian G₁' ∧ U₁'.toUnifPre.OLinear F₁.O F₁.o oA₁ oG₁ ∧ IsSemiAbelian G₁ ∧ IsMonHom inc₁ ∧ IsMonHom pr₁ ∧ inc₁ ≫ pr₁ = 𝟙 G₁ ∧ pr₁ ≫ inc₁ = oG₁.act F₁.e ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso ((abelian₂ G₁' U₁'.LG.L).pull (lift (fst G₁ G₁ ≫ inc₁) (snd G₁ G₁ ≫ inc₁ ≫ oG₁.act F₁.f) : G2 G₁ ⟶ G2 G₁').left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr mi mp hip hpi R' _ _ _ ρ hR' hρ hloc
  obtain ⟨D₁, ⟨hD⟩⟩ := GlobalTheory.MumPull.exists_pull R R' ρ hρ hloc D
  obtain ⟨D₁', hD', A₁', U₁', hU, oG₁, oA₁, h₁, h₂⟩ :=
    unif_pull hR hR' ρ hρ (map_maximalIdeal_le ρ) hG' U' F.O F.o oA oG hlin
  obtain ⟨m, o₁, hx, ho⟩ := degAct_pull GlobalTheory.firstFiveLaws.1.globalFns R R' ρ _ _ hD' F.O F.o
  have lin := oLinear_pull R R' _ _ ρ D' D₁' hD' A' A₁' G' _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) U' U₁' hU
    F.O F.o o₁ oA oA₁ oG oG₁ hlin h₁ h₂ hx ho
  obtain ⟨inc', pr', xi, xp, w, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉, b₁₀, b₁₁⟩ :=
    factor_pull hρ hD hD' F o₁ hx fun a => act_proj _ hD'.e.hom (ho a)
  let F₁ : Factor D₁.toPre D₁'.toPre :=
    { O := F.O, o := o₁, e := F.e, f := F.f, inc := inc', pr := pr', xi := xi, xp := xp, w := w, idem := F.idem,
      inc_hom := b₁, pr_hom := b₂, inc_pr := b₃, pr_inc := b₄, xp_xi := b₅, xi_xp := b₆, c_xi := b₇, inj := b₈,
      onto := b₉, w_gen := b₁₀, tau := b₁₁ }
  have ha : ∀ a, oG₁.act a = (Over.pullback (specOf ρ)).map (oG.act a) := fun a =>
    (Category.comp_id _).symm.trans ((h₁ a).trans (Category.id_comp _))
  have gG := isGrpPullback_pullback G (specOf ρ)
  have gG' := (isGrpPullback_pullback G' (specOf ρ)).congr rfl (Category.id_comp _).symm
  obtain ⟨wL, hwL, -⟩ := hU.lg
  refine ⟨D₁, D₁', F₁, A₁', _, _, _, U₁', oA₁, oG₁, (Over.pullback (specOf ρ)).obj G, inferInstance, inferInstance, _,
    sqOf gG, (Over.pullback (specOf ρ)).map inc, (Over.pullback (specOf ρ)).map pr, ⟨hD⟩,
    IsSemiAbelian.pullback _ G' hG', lin, IsSemiAbelian.pullback _ G hG, inferInstance, inferInstance, ?_, ?_, gG,
    isSquare_sqOf gG, ?_⟩
  · rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id]
  · rw [← CategoryTheory.Functor.map_comp, hpi, ha]
  · have hm := lift_sq gG gG' (u := inc) (v := inc ≫ oG.act F.f) (u₁ := (Over.pullback (specOf ρ)).map inc)
      (v₁ := (Over.pullback (specOf ρ)).map inc ≫ oG₁.act F.f)
      ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (map_left_fst _ _))
      ((congrArg (_ ≫ ·) (Category.id_comp _)).trans (by
        rw [ha, ← CategoryTheory.Functor.map_comp]; exact map_left_fst _ _))
    have H : LBIso _ _ := ⟨lamIso gG' wL, isGen_lamIso gG' wL hwL⟩
    exact H.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
      (chartPullLinComb (abelian₂ G' U'.LG.L) _ (fun _ => sqOf gG) (fun _ => sqOf gG') _ _ fun _ => hm.symm)

end GlobalTheory.FactorPull

end
