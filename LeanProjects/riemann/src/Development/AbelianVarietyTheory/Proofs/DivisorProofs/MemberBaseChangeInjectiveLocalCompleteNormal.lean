import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZHAbove
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsCarryCommonFlagSpectrumMapFieldExt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UwRQeIsNsmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackUniformisationEndomorphismCommGenericFStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsPullbackUniformisationCommonFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.MemBC

open GlobalTheory.ArcPull GlobalTheory.PullLinear

theorem exists_pull_gen {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {I : Ideal R} {I' : Ideal R'} (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g)
    (hI : I.map g ≤ I') {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ (D' : DegData R' I') (hD : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing R'))))
      (gA : A'.A.left ⟶ A.A.left) (U' : Unif I' D' A' ((Over.pullback (specOf g)).obj G)),
      IsPullUnif g hD (Iso.refl _) U U' ∧ IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA ∧ LBIso A'.L (A.L.pull gA) ∧
      gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
        U'.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (specOf g) := by
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
  have gpG := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
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
  obtain ⟨D', hD, U', -, hgU, hPU⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  refine ⟨D', hD, A', gA, U', hPU, gpA, LBIso.symm tA, ?_⟩
  have k1 : U'.gen.hom.left ≫ gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g) := by
    rw [hgU]; exact heA
  have k2 : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  calc gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)
      = U'.gen.inv.left ≫ U'.gen.hom.left ≫ gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) := by
        rw [← Category.assoc U'.gen.inv.left, k2, Category.id_comp]
    _ = _ := by rw [k1]

end GlobalTheory.Poinc.Sep.MemBC

namespace GlobalTheory.Poinc.Sep.MemBC

open GlobalTheory.ArcPull

theorem pt_comp {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (z₁ : X₁.M.Z) {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V']
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (j : V →+* V') (hj : Function.Injective j) :
    jK V' ≫ spMap (j.comp ev) ≫ X₁.M.Z.fromSpecStalk z₁ =
      spMap (fracMap hj) ≫ (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) := by
  have sq := fracMap_sq hj
  rw [Category.id_comp] at sq
  rw [spMap_comp, Category.assoc, ← Category.assoc (jK V'), sq]
  simp only [genMap, Category.assoc]

theorem regAt_comp {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (z₁ : X₁.M.Z) {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V']
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (j : V →+* V') (hj : Function.Injective j) (h : RegAt X₁ z₁ ev) :
    RegAt X₁ z₁ (j.comp ev) := by
  intro a ha
  rw [pt_comp X₁ z₁ ev j hj]
  convert h a ha using 2
  exact GlobalTheory.FlagBundle.spMap_comp_apply_field (fracMap hj) _ _ _

theorem val_spMap_comp_field' {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {k K : Type} [Field k]
    [Field K] (σ : k →+* K) (p : Sp k ⟶ M.Z) (y : Ω) : M.val (spMap σ ≫ p) y = σ (M.val p y) := by
  by_cases hy : y ∈ M.O (p (IsLocalRing.closedPoint k))
  · have := RatModel.val_spMap_comp σ p specializes_rfl ⟨y, hy⟩
    rw [RatModel.valLoc_eq_val] at this
    exact this
  · rw [RatModel.val_of_notMem (y := p) (IsLocalRing.closedPoint k) hy, map_zero,
      RatModel.val_of_notMem (y := spMap σ ≫ p) (IsLocalRing.closedPoint K)
        (fun h' => hy (by convert h' using 2; exact (GlobalTheory.FlagBundle.spMap_comp_apply_field σ p _ _).symm))]

theorem yK_comp {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X₁ : Setup F W i) (z₁ : X₁.M.Z) {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V']
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (j : V →+* V') (hj : Function.Injective j) (yK : X₁.S.R →+* FractionRing V)
    (h : ∀ a : X₁.S.R, yK a = X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a) (a : X₁.S.R) :
    (fracMap hj).comp yK a = X₁.M.val (jK V' ≫ spMap (j.comp ev) ≫ X₁.M.Z.fromSpecStalk z₁) a := by
  rw [pt_comp X₁ z₁ ev j hj]
  exact (congrArg (fracMap hj) (h a)).trans (val_spMap_comp_field' X₁.M (fracMap hj) _ _).symm

end GlobalTheory.Poinc.Sep.MemBC

namespace GlobalTheory.Poinc.Sep.MemBC
open GlobalTheory.ArcPull

theorem aA_comm {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (g : R →+* R') (hg : Function.Injective g) {D : DegData R I} {D' : DegData R' I'}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    (U' : UnifPre I' D' A' ((Over.pullback (specOf g)).obj G)) (gA : A'.A.left ⟶ A.A.left)
    (hgA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA)
    (hrel : gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      U'.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (specOf g))
    (E : EndU U) (E' : EndU U') (hE : E'.aG = (Over.pullback (specOf g)).map E.aG) :
    E'.aA.left ≫ gA = gA ≫ E.aA.left :=
  GlobalTheory.T.pulledBack_uniformisationEndomorphism_comm_genericFibre g hg U U' gA hgA hrel E E' hE

end GlobalTheory.Poinc.Sep.MemBC

namespace GlobalTheory.Poinc.Sep.MemBC

open GlobalTheory.ArcPull

theorem qk_field {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : IsCN V) {D : DegData V (maximalIdeal V)}
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (U : Unif (maximalIdeal V) D A G) (k : ℕ) (hk : 1 ≤ k)
    (p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A)
    (hx : QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) k p x) (F' : Type) [Field F'] [IsAlgClosed F']
    [Algebra (FractionRing V) F'] (σ : AlgebraicClosure (FractionRing V) →ₐ[FractionRing V] F') :
    ∃ (p₁ : QkPt D.toPre F' k) (x₁ : TFK (R := V) F' ⟶ A.A), p₁.y = p.y ∧ x₁.left = spMap σ.toRingHom ≫ x.left ∧
      QkToAkU U.toUnifPre F' k p₁ x₁ := by
  haveI : CharZero V := hV.2.2.2
  have hAd : AdmBase V (maximalIdeal V) := ⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩
  obtain ⟨p₁, hp₁⟩ := qkExtExists V D.toPre (AlgebraicClosure (FractionRing V)) F' σ.toRingHom (fun r => σ.commutes r) k p
  have hw : (spMap σ.toRingHom ≫ x.left) ≫ A.A.hom = (TFK (R := V) F').hom := by
    rw [Category.assoc, Over.w x]
    show spMap σ.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) =
      spMap (algebraMap (FractionRing V) F')
    rw [← spMap_comp]
    congr 1
    exact σ.comp_algebraMap
  let x₁ : TFK (R := V) F' ⟶ A.A := Over.homMk (spMap σ.toRingHom ≫ x.left) hw
  refine ⟨p₁, x₁, hp₁.1, rfl, ?_⟩
  exact (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt GlobalTheory.firstFiveLaws V (maximalIdeal V) hAd D A G hG U
    (AlgebraicClosure (FractionRing V)) F' σ k hk p p₁ x x₁ hp₁ rfl).1 hx

theorem qk_base {V V' : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V']
    (hV : IsCN V) (hV' : IsCN V') (j : V →+* V') (hj : Function.Injective j) (hl : IsLocalHom j)
    {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (U : Unif (maximalIdeal V) D A G) (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg j D.toPre D'.toPre)
    (A' : PolAV (Spec (CommRingCat.of (FractionRing V')))) (gA : A'.A.left ⟶ A.A.left)
    (U' : Unif (maximalIdeal V') D' A' ((Over.pullback (specOf j)).obj G)) (hPU : IsPullUnif j hD (Iso.refl _) U U')
    (hgA : IsGrpPullback A'.A A.A (spMap (fracMap hj)) gA)
    (hrel : gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) =
      U'.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf j)).obj G).hom (jK V') ≫ pullback.fst G.hom (specOf j))
    (F' : Type) [Field F'] [Algebra (FractionRing V) F'] [Algebra (FractionRing V') F']
    (hF : ∀ r : V, algebraMap (FractionRing V) F' (algebraMap V (FractionRing V) r) =
      algebraMap (FractionRing V') F' (algebraMap V' (FractionRing V') (j r)))
    (k : ℕ) (hk : 1 ≤ k) (p₁ : QkPt D.toPre F' k) (x₁ : TFK (R := V) F' ⟶ A.A)
    (hx : QkToAkU U.toUnifPre F' k p₁ x₁) :
    ∃ (p' : QkPt D'.toPre F' k) (x' : TFK (R := V') F' ⟶ A'.A), p'.y = hD.xe.symm p₁.y ∧
      QkToAkU U'.toUnifPre F' k p' x' ∧ x'.left ≫ gA = x₁.left :=
  GlobalTheory.T.torsionLabels_pullback_uniformisation_common_field hV hV' j hj hl hG U D' hD A' gA U' hPU hgA hrel F' hF k hk p₁ x₁ hx

theorem yy_pull' {V V' : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V']
    (hV : IsCN V) (hV' : IsCN V') (j : V →+* V') (hj : Function.Injective j) (hl : IsLocalHom j)
    {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (U : Unif (maximalIdeal V) D A G) (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg j D.toPre D'.toPre)
    (A' : PolAV (Spec (CommRingCat.of (FractionRing V')))) (gA : A'.A.left ⟶ A.A.left)
    (U' : Unif (maximalIdeal V') D' A' ((Over.pullback (specOf j)).obj G)) (hPU : IsPullUnif j hD (Iso.refl _) U U')
    (hgA : IsGrpPullback A'.A A.A (spMap (fracMap hj)) gA)
    (hrel : gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V) =
      U'.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf j)).obj G).hom (jK V') ≫ pullback.fst G.hom (specOf j))
    (k : ℕ) (hk : 1 ≤ k) (p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k)
    (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A)
    (hx : QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) k p x) :
    ∃ (p' : QkPt D'.toPre (AlgebraicClosure (FractionRing V')) k)
      (x' : TFK (R := V') (AlgebraicClosure (FractionRing V')) ⟶ A'.A)
      (σ : AlgebraicClosure (FractionRing V) →+* AlgebraicClosure (FractionRing V')),
      σ.comp (algebraMap (FractionRing V) _) = (algebraMap (FractionRing V') _).comp (fracMap hj) ∧
      p'.y = hD.xe.symm p.y ∧ QkToAkU U'.toUnifPre (AlgebraicClosure (FractionRing V')) k p' x' ∧
      x'.left ≫ gA = spMap σ ≫ x.left := by
  letI : Algebra (FractionRing V) (AlgebraicClosure (FractionRing V')) :=
    ((algebraMap (FractionRing V') (AlgebraicClosure (FractionRing V'))).comp (fracMap hj)).toAlgebra
  let σ : AlgebraicClosure (FractionRing V) →ₐ[FractionRing V] AlgebraicClosure (FractionRing V') :=
    IsAlgClosed.lift
  obtain ⟨p₁, x₁, hy, hx₁, hq⟩ := qk_field hV hG U k hk p x hx (AlgebraicClosure (FractionRing V')) σ
  obtain ⟨p', x', hy', hq', hx'⟩ := qk_base hV hV' j hj hl hG U D' hD A' gA U' hPU hgA hrel
    (AlgebraicClosure (FractionRing V')) (fun r => congrArg (algebraMap (FractionRing V') _) (fracMap_algebraMap hj r))
    k hk p₁ x₁ hq
  exact ⟨p', x', σ.toRingHom, σ.comp_algebraMap, hy'.trans (congrArg _ hy), hq', hx'.trans hx₁⟩

end GlobalTheory.Poinc.Sep.MemBC

namespace GlobalTheory.Poinc.Sep.MemBC
open GlobalTheory.ArcPull

theorem uMem_baseChange : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (j : V →+* V'), IsCN V' → Function.Injective j → IsLocalHom j → ∃ (m' : ℕ) (t' : Fin m' → V') (δ' : Fin m' → LinearMap.BilinForm ℤ X) (𝔫 : UMem X₁ z₁ act V' (j.comp ev) X t' δ'), ∀ a mu, 𝔪.YY a mu → 𝔫.YY a mu := by
  intro g n F W Z i X₁ z₁ act _hact V _ _ _ ev X _ m t δ 𝔪 V' _ _ _ j hV' hj hl
  have hV := 𝔪.cn
  have hAd : AdmBase V (maximalIdeal V) := ⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩
  have hAd' : AdmBase V' (maximalIdeal V') := ⟨hV'.1, inferInstance, hV'.2.1, hV'.2.2.1⟩
  have hI : (maximalIdeal V).map j ≤ maximalIdeal V' := map_maximalIdeal_le j
  obtain ⟨D', hD, A', gA, U', hPU, hgA, htA, hrel⟩ := exists_pull_gen hAd hAd' j hj hI 𝔪.semi 𝔪.U
  have hwl : LBIso A'.L (X₁.ρ.P.L.pull (gA ≫ 𝔪.φ)) :=
    LBIso.trans A'.isLB (pull_isLB 𝔪.A.isLB _) (pull_isLB X₁.ρ.P.isLB _) htA (lbIso_pull_comp ⟨𝔪.wl, 𝔪.wl_gen⟩ gA)
  obtain ⟨wl, hwl⟩ := hwl
  haveI := 𝔪.loc
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  refine ⟨m, j ∘ t, δ, {
    cn := hV'
    loc := inferInstance
    reg := regAt_comp X₁ z₁ ev j hj 𝔪.reg
    yK := (fracMap hj).comp 𝔪.yK
    yK_eq := yK_comp X₁ z₁ ev j hj 𝔪.yK 𝔪.yK_eq
    D := D'
    e₈ := 𝔪.e₈.trans hD.xe.symm
    G := (Over.pullback (specOf j)).obj 𝔪.G
    semi := IsSemiAbelian.pullback _ _ 𝔪.semi
    A := A'
    U := U'
    φ := gA ≫ 𝔪.φ
    cart := (hgA.comp 𝔪.cart).congr (by rw [spMap_comp]) rfl
    wl := wl
    wl_gen := hwl
    equiv := fun a a' ha => ?_
    psi := fun mu => ?_ }, ?_⟩
  · obtain ⟨E, hE1, hE2⟩ := 𝔪.equiv a a' ha
    have := E.homG
    obtain ⟨E', h1, h2, -⟩ := EndBaseChange.exists_end hD hPU E ((Over.pullback (specOf j)).map E.aG)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    refine ⟨E', ?_, fun mu => ?_⟩
    · rw [← Category.assoc, aA_comm j hj 𝔪.U.toUnifPre U'.toUnifPre gA hgA hrel E E' h1, Category.assoc, hE1,
        Category.assoc]
    · apply hD.xe.injective
      simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply, h2, hE2]
  · obtain ⟨u, hu⟩ := 𝔪.psi mu
    have hr : Formalism.L2.Pj.PsiCoord 𝔪.D.toPre (hD.xe (hD.xe.symm (𝔪.e₈ mu))) (u * mono W t δ mu) := by
      rw [AddEquiv.apply_symm_apply]; exact hu
    obtain ⟨u', hu'⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD _ _ hr
    refine ⟨u' * Units.map j.toMonoidHom u, ?_⟩
    have hm : mono W (j ∘ t) δ mu = j (mono W t δ mu) := by simp [mono, map_prod, map_pow]
    convert hu' using 1
    · exact AddEquiv.trans_apply _ _ _
    · rw [hm, map_mul]
      simp [_root_.mul_assoc]
  · rintro a mu ⟨p, x, hpy, hqx, hxφ⟩
    obtain ⟨p', x', σ, hσ, hp'y, hq', hx'⟩ := yy_pull' hV hV' j hj hl 𝔪.semi 𝔪.U D' hD A' gA U' hPU hgA hrel _ hk p x hqx
    refine ⟨p', x', ?_, hq', ?_⟩
    · show p'.y = (𝔪.e₈.trans hD.xe.symm) mu
      rw [AddEquiv.trans_apply, hp'y, hpy]
    · show x'.left ≫ gA ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V') (AlgebraicClosure (FractionRing V'))).comp
          ((fracMap hj).comp 𝔪.yK)) ≫ (X₁.ρ.pt a).left
      rw [← Category.assoc, hx', Category.assoc, hxφ, ← Category.assoc, ← spMap_comp]
      congr 2
      rw [← RingHom.comp_assoc, hσ, RingHom.comp_assoc]

end GlobalTheory.Poinc.Sep.MemBC
