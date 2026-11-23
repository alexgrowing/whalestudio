import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLinearOfIsPullUniformisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformizationEndomorphismOfLinear
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.UT.EndBaseChange

open GlobalTheory.ArcPull GlobalTheory.PullLinear
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_pull (hP : PolBaseChangeSt) (hU : UnifBaseChangeSt) (hψ : PsiOnExistsSt) {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I')
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ (D' : DegData R' I') (hD : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing R'))))
      (U' : Unif I' D' A' ((Over.pullback (specOf g)).obj G)), IsPullUnif g hD (Iso.refl _) U U' := by
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
      ((LBIso.symm tA).chartPull (chartPullPull A'.L _ _ rfl) (chartPullPull (A.L.pull gA) _ _ rfl)) ?_
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
  obtain ⟨D', hD, U', -, -, hPU⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨D', hD, A', U', hPU⟩

section Points

attribute [local instance] GlobalTheory.TorusExt.gtGroup

open GlobalTheory.TorusExt

theorem points (hG : GlobalFnsSt) {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D')
    (hB : D.TauBimult) (hB' : D'.TauBimult) (F : Type) [Field F] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R') F] (hF : Compat φ F) :
    (∀ g, ∃! g', IsPullGtF φ hD F g g') ∧ (∀ g', ∃! g, IsPullGtF φ hD F g g') ∧
      (∀ g g' y, IsPullGtF φ hD F g g' → (GtPtF.IsIota (hD.xe y) g ↔ GtPtF.IsIota y g')) ∧
      ∀ k g g' h h', IsPullGtF φ hD F g g' → IsPullGtF φ hD F h h' →
        (GtPtF.IsNsmul k g h ↔ GtPtF.IsNsmul k g' h') := by
  have inj := pullGt_injective hD hG hF
  refine ⟨fun g => (exists_pullGt hD hG hF g).elim fun g' h => ⟨g', h, fun _ h' => pullGt_unique hD hF h' h⟩,
    fun g' => ?_, fun g g' y h => ?_, fun k g g' h h' a b => ?_⟩
  · obtain ⟨p, -, hp⟩ := qkPullExists hG R R' φ D D' hD F hF 0
      (qkMk hB' 0 g' ((zero_nsmul g').trans (map_zero _).symm))
    exact ⟨p.g, hp, fun _ h' => pullGt_unique' hD h' hp⟩
  · rw [(isPullGtF_iff_eq hD hG hF _ _).1 h, isIota_iff_eq hB, isIota_iff_eq hB', ← pullGt_iota hD hG hF hB hB',
      inj.eq_iff]
  · rw [(isPullGtF_iff_eq hD hG hF _ _).1 a, (isPullGtF_iff_eq hD hG hF _ _).1 b, isNsmul_iff_eq, isNsmul_iff_eq,
      ← map_nsmul, inj.eq_iff]

end Points

theorem cancel_iff {U : Type} [CommGroup U] (P Q a b c : U) : Q * a = P * b * (P⁻¹ * Q * c) ↔ a = b * c := by
  rw [show P * b * (P⁻¹ * Q * c) = Q * (b * c) by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel, mul_right_inj]

theorem prod_u (D : DegPre R) (a : D.P.A ⟶ D.P.A) (x y : D.X) {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A)
    {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k, h (p.left ≫ Sum.elim (D.Oφ (𝟙 _) x) (D.Oφ a y) k) ^ Sum.elim Oε Oinvε k =
      (∏ k, h (D.Oφ p x k) ^ Oinvε k)⁻¹ * ∏ k, h (D.Oφ (p ≫ a) y k) ^ Oinvε k := by
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, WeightPf.Oφ_comp, Category.comp_id]
  rw [OLinEnd.prod_Oφ, OLinEnd.prod_Oφ_inv D p]
  simp only [mul_inv, inv_inv]

section End

variable {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D')

theorem exists_u {a : D.P.A ⟶ D.P.A} {a' : D'.P.A ⟶ D'.P.A} [IsMonHom a']
    (ha : a'.left ≫ proj hD = proj hD ≫ a.left) {x : D.X} (x' y' : D'.X) (hx : hD.xe x' = x)
    (u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) x) (D.Oφ a (hD.xe y'))) (Sum.elim Oε Oinvε))) (hu : Normd u) :
    ∃ u' : LB.Gen (LB.LinComb D'.P.L (Sum.elim (D'.Oφ (𝟙 _) x') (D'.Oφ a' y')) (Sum.elim Oε Oinvε)), Normd u' ∧
      ∀ (T : Over (Spec (CommRingCat.of R'))) (p : T ⟶ D'.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J',
        Good D.P.L z J → Good D'.P.L z J' → val u ((r ≫ p.left) ≫ proj hD) z J =
          (∏ k, om hD.w z J J' (r ≫ D'.Oφ p x' k) ^ Oinvε k)⁻¹ *
            (∏ k, om hD.w z J J' (r ≫ D'.Oφ (p ≫ a') y' k) ^ Oinvε k) * val u' (r ≫ p.left) z J' := by
  subst hx
  obtain ⟨u', hu', vu⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB
    (φ' := Sum.elim (D'.Oφ (𝟙 _) x') (D'.Oφ a' y')) (proj hD) (by
      rintro (k | k)
      · exact TorusCoordPull.Oφ_pull hD (𝟙 _) (𝟙 _) _ ((Category.id_comp _).trans (Category.comp_id _).symm) x' k
      · exact TorusCoordPull.Oφ_pull hD a a' _ ha y' k) u hu.1
  have key : ∀ (T : Over (Spec (CommRingCat.of R'))) (p : T ⟶ D'.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J',
      Good D.P.L z J → Good D'.P.L z J' → val u ((r ≫ p.left) ≫ proj hD) z J =
        (∏ k, om hD.w z J J' (r ≫ D'.Oφ p x' k) ^ Oinvε k)⁻¹ *
          (∏ k, om hD.w z J J' (r ≫ D'.Oφ (p ≫ a') y' k) ^ Oinvε k) * val u' (r ≫ p.left) z J' :=
    fun T p Z r z J J' hJ hJ' => by
    refine (vu Z (r ≫ p.left) z J J' hJ hJ').trans (congrArg₂ (· * ·) ?_ rfl)
    refine Eq.trans ?_ (prod_u D' a' x' y' p (fun q => om hD.w z J J' (r ≫ q)))
    simp only [Category.assoc]
  refine ⟨u', ⟨hu', corr_of_val D'.P.isLB fun y J' hJ' => ?_⟩, key⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
  have o₁ : (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A).left = eSec D'.P.A := Category.id_comp _
  have e := key _ 1 _ (𝟙 _) y J J' hJ hJ'
  rw [OLinEnd.prod_Oφ_inv D' _ _ (fun q => om hD.w y J J' (𝟙 _ ≫ q)),
    OLinEnd.prod_Oφ_inv D' _ _ (fun q => om hD.w y J J' (𝟙 _ ≫ q)), MonObj.one_comp, _root_.mul_one, _root_.mul_one,
    o₁, Category.id_comp (eSec D'.P.A), hD.he] at e
  have e₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ hu.2 (specOf φ)).trans (val_one _))
  rw [e₁] at e
  rw [val_pull hJ', val_one, Category.id_comp]
  simpa using e.symm

theorem act_iff {a : D.P.A ⟶ D.P.A} {a' : D'.P.A ⟶ D'.P.A} (ha : a'.left ≫ proj hD = proj hD ≫ a.left)
    {h : D.X → D.X} {h' : D'.X → D'.X} (hx : ∀ χ, hD.xe (h' χ) = h (hD.xe χ))
    (u : ∀ χ, LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (h χ)) (D.Oφ a χ)) (Sum.elim Oε Oinvε)))
    (u' : ∀ χ, LB.Gen (LB.LinComb D'.P.L (Sum.elim (D'.Oφ (𝟙 _) (h' χ)) (D'.Oφ a' χ)) (Sum.elim Oε Oinvε)))
    (vu : ∀ χ (T : Over (Spec (CommRingCat.of R'))) (p : T ⟶ D'.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) J J',
        Good D.P.L z J → Good D'.P.L z J' → val (u (hD.xe χ)) ((r ≫ p.left) ≫ proj hD) z J =
          (∏ k, om hD.w z J J' (r ≫ D'.Oφ p (h' χ) k) ^ Oinvε k)⁻¹ *
            (∏ k, om hD.w z J J' (r ≫ D'.Oφ (p ≫ a') χ k) ^ Oinvε k) * val (u' χ) (r ≫ p.left) z J')
    {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
    {g₁ g₂ : GtPtF D F} {g₁' g₂' : GtPtF D' F} (h₁ : IsPullGtF φ hD F g₁ g₁') (h₂ : IsPullGtF φ hD F g₂ g₂') :
    (g₂.b = g₁.b ≫ a ∧ ∀ χ z J, Good D.P.L z J →
      val (g₂.s χ) (𝟙 _) z J = val (g₁.s (h χ)) (𝟙 _) z J * val (u χ) g₁.b.left z J) ↔
    (g₂'.b = g₁'.b ≫ a' ∧ ∀ χ z J, Good D'.P.L z J →
      val (g₂'.s χ) (𝟙 _) z J = val (g₁'.s (h' χ)) (𝟙 _) z J * val (u' χ) g₁'.b.left z J) := by
  have hb : (g₁'.b ≫ a').left ≫ proj hD = (g₁.b ≫ a).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc]
    exact congrArg (· ≫ _) h₁.1
  have hiff : g₂.b = g₁.b ≫ a ↔ g₂'.b = g₁'.b ≫ a' :=
    ⟨fun H => ext_of_iso_pullback _ hD.e (h₂.1.trans ((congrArg (·.left) H).trans hb.symm)),
      fun H => Over.OverMorphism.ext (h₂.1.symm.trans ((congrArg (·.left ≫ proj hD) H).trans hb))⟩
  rw [hiff]
  refine and_congr_right fun H => ?_
  have key : ∀ χ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' →
      (vS (g₂.s (hD.xe χ)) y J = vS (g₁.s (h (hD.xe χ))) y J * val (Z := Sp F) (u (hD.xe χ)) g₁.b.left y J ↔
        vS (g₂'.s χ) y J' = vS (g₁'.s (h' χ)) y J' * val (Z := Sp F) (u' χ) g₁'.b.left y J') := by
    intro χ y J J' hJ hJ'
    have e₁ : vS (g₁.s (hD.xe (h' χ))) y J =
        (∏ k, om hD.w y J J' (𝟙 (Sp F) ≫ D'.Oφ g₁'.b (h' χ) k) ^ Oinvε k) * vS (g₁'.s (h' χ)) y J' :=
      (pullGt_val hD h₁ (h' χ) (𝟙 _) hJ hJ').trans (congrArg₂ (· * ·)
        (OLinEnd.prod_Oφ_inv D' g₁'.b (h' χ) (fun q => om hD.w y J J' (𝟙 (Sp F) ≫ q))).symm rfl)
    have e₂ : vS (g₂.s (hD.xe χ)) y J =
        (∏ k, om hD.w y J J' (𝟙 (Sp F) ≫ D'.Oφ (g₁'.b ≫ a') χ k) ^ Oinvε k) * vS (g₂'.s χ) y J' := by
      rw [← H]
      exact (pullGt_val hD h₂ χ (𝟙 _) hJ hJ').trans (congrArg₂ (· * ·)
        (OLinEnd.prod_Oφ_inv D' g₂'.b χ (fun q => om hD.w y J J' (𝟙 (Sp F) ≫ q))).symm rfl)
    have e₃ : val (Z := Sp F) (u (hD.xe χ)) g₁.b.left y J =
        (∏ k, om hD.w y J J' (𝟙 (Sp F) ≫ D'.Oφ g₁'.b (h' χ) k) ^ Oinvε k)⁻¹ *
          (∏ k, om hD.w y J J' (𝟙 (Sp F) ≫ D'.Oφ (g₁'.b ≫ a') χ k) ^ Oinvε k) *
          val (Z := Sp F) (u' χ) g₁'.b.left y J' :=
      (congrArg (fun q => val (Z := Sp F) (u (hD.xe χ)) q y J)
        ((congrArg (· ≫ proj hD) (Category.id_comp _)).trans h₁.1).symm).trans
        ((vu χ _ g₁'.b (Sp F) (𝟙 _) y J J' hJ hJ').trans (congrArg₂ (· * ·) rfl
          (congrArg (fun q => val (Z := Sp F) (u' χ) q y J') (Category.id_comp _))))
    rw [hx] at e₁
    rw [e₁, e₂, e₃]
    exact cancel_iff _ _ _ _ _
  constructor
  · intro H χ y J' hJ'
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB (Z := Sp F) y
    exact (key χ y J J' hJ hJ').1 (H _ y J hJ)
  · intro H χ y J hJ
    obtain ⟨χ, rfl⟩ := hD.xe.surjective χ
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := Sp F) y
    exact (key χ y J J' hJ hJ').2 (H _ y J' hJ')

end End

set_option maxHeartbeats 800000 in

theorem exists_end {I : Ideal R} {I' : Ideal R'} {φ : R →+* R'} {D : DegData R I} {D' : DegData R' I'}
    (hD : IsPullDeg φ D.toPre D'.toPre) {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G} {U : Unif I D A G} {U' : Unif I' D' A' G'}
    (hU : IsPullUnif φ hD bc U U') (E : EndU U.toUnifPre) (aG : G' ⟶ G') [haG : IsMonHom aG]
    (hG : aG ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf φ)).map E.aG) :
    ∃ E' : EndU U'.toUnifPre, E'.aG = aG ∧ (∀ χ, hD.xe (E'.h χ) = E.h (hD.xe χ)) ∧
      ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] g₁ g₂ g₁' g₂',
        IsPullGtF φ hD F g₁ g₁' → IsPullGtF φ hD F g₂ g₂' → (E.Act g₁ g₂ ↔ E'.Act g₁' g₂') := by
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  choose h hf hpt _hw using H
  have := E.homB
  have := hD.e_hom
  have := U'.gen_hom
  obtain ⟨aB, homB, hB⟩ : ∃ aB : D'.toPre.P.A ⟶ D'.toPre.P.A, IsMonHom aB ∧
      aB ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map E.aB :=
    ⟨hD.e.hom ≫ (Over.pullback (specOf φ)).map E.aB ≫ hD.e.inv, inferInstance, by simp⟩
  have hB' : aB.left ≫ proj hD = proj hD ≫ E.aB.left := act_proj _ hD.e.hom hB
  obtain ⟨h', hx⟩ : ∃ h' : D'.toPre.X →+ D'.toPre.X, ∀ χ, hD.xe (h' χ) = E.h (hD.xe χ) :=
    ⟨hD.xe.symm.toAddMonoidHom.comp (E.h.comp hD.xe.toAddMonoidHom), fun χ => hD.xe.apply_symm_apply _⟩
  choose u hu vu using fun χ => exists_u hD hB' (h' χ) χ (hx χ) (E.u (hD.xe χ)) (E.u_norm _)
  have hact : ∀ e : ℕ, ((Over.pullback (thick R' I' e)).map aG).left ≫ h e =
      h e ≫ ((Over.pullback (thick R I e)).map E.aG).left := by
    intro e
    have hf' : h e ≫ pullback.fst G.hom (thick R I e) = pullback.fst G'.hom (thick R' I' e) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ) := hf e
    have : IsClosedImmersion (thick R I e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have hmono : Mono (pullback.fst G.hom (thick R I e)) := inferInstance
    rw [← cancel_mono (pullback.fst G.hom (thick R I e)), Category.assoc, Category.assoc, map_left_fst,
      ← Category.assoc (h e), hf', ← Category.assoc, map_left_fst, Category.assoc,
      act_proj _ bc.hom hG, Category.assoc, Category.assoc, Category.assoc]
  have k : ∀ {S : Type} [CommRing S] [IsDomain S] {J : Ideal S} {E : DegPre S} {e : ℕ}
      {K : Over (Spec (CommRingCat.of S))} [GrpObj K] [IsCommMonObj K] (g : GtCoord J E e K)
      (u : E.P.A ⟶ E.P.A), (g.q ≫ (Over.pullback (thick S J e)).map u).left ≫
        pullback.fst E.P.A.hom (thick S J e) = g.pG.left ≫ u.left := by
    intro S _ _ J E e K _ _ g u
    rw [Over.comp_left, Category.assoc, map_left_fst, pG_left, Category.assoc]
  have k₂ : ∀ e, (Over.map (thick R' I' e)).map ((Over.pullback (thick R' I' e)).map aG) ≫
      (U'.gt e).pG = (U'.gt e).pG ≫ aB := by
    intro e
    have k₁ : ((Over.pullback (thick R I e)).map E.aG).left ≫ (U.gt e).pG.left =
        (U.gt e).pG.left ≫ E.aB.left := by
      rw [← k, ← E.q_lin e]
      exact (Category.assoc _ _ _).symm
    refine ext_of_iso_pullback _ hD.e ?_
    change (((Over.pullback (thick R' I' e)).map aG).left ≫ (U'.gt e).pG.left) ≫ _ =
      ((U'.gt e).pG.left ≫ aB.left) ≫ _
    rw [Category.assoc, Category.assoc, act_proj _ hD.e.hom hB, (hpt e).1,
      ← Category.assoc (U'.gt e).pG.left, (hpt e).1, ← Category.assoc, hact, Category.assoc,
      Category.assoc, k₁]
  have hq : ∀ e : ℕ, (Over.pullback (thick R' I' e)).map aG ≫ (U'.gt e).q =
      (U'.gt e).q ≫ (Over.pullback (thick R' I' e)).map aB := by
    intro e
    refine ext_of_pullback _ ?_
    rw [k, Over.comp_left, Category.assoc]
    exact congrArg (·.left) (k₂ e)
  refine ⟨{ aG := aG, aA := U'.gen.inv ≫ (Over.pullback (jK R')).map aG ≫ U'.gen.hom, aB := aB, homG := haG,
            homA := inferInstance, homB := homB, h := h', ext := by simp, q_lin := hq, i_lin := fun e => ?_,
            u := u, u_norm := hu, t_lin := fun e χ Z x z J' hJ' => ?_ }, rfl, hx,
    fun F _ _ _ g₁ g₂ g₁' g₂' h₁ h₂ => act_iff hD hB' hx E.u u vu h₁ h₂⟩
  · obtain ⟨t, ht, hi⟩ := E.i_lin e
    have hk : ((U'.gt e).i ≫ (Over.pullback (thick R' I' e)).map aG) ≫ (U'.gt e).q =
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
    have e₂ := char_eq (U.gt e) (U'.gt e) hD.w ((hpt e).2 (h' χ)).1 ((hpt e).2 (h' χ)).2 (𝟙 _) τ hτ z
    have e₃ := (torusEndOf_iff _ _ t).1 ht _ τ.left z (hD.xe χ)
    rw [hx] at e₂
    refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t'.left z ⊤ trivial _)).trans ?_
    rw [Category.id_comp]
    exact e₁.symm.trans (e₃.trans e₂)
  · obtain ⟨J, hJ⟩ := DegPull.exists_good' D.toPre.P.isLB z
    have e₁ := pmaps_om ((hpt e).2 χ).1 ((hpt e).2 χ).2 (x ≫ ((Over.pullback (thick R' I' e)).map aG).left) z hJ hJ'
    have e₂ := pmaps_om ((hpt e).2 (h' χ)).1 ((hpt e).2 (h' χ)).2 x z hJ hJ'
    have e₃ := vu χ _ (U'.gt e).pG Z x z J J' hJ hJ'
    have e₄ := E.t_lin e (hD.xe χ) Z (x ≫ h e) z J hJ
    have a₁ : (x ≫ h e) ≫ ((Over.pullback (thick R I e)).map E.aG).left =
        (x ≫ ((Over.pullback (thick R' I' e)).map aG).left) ≫ h e := by
      rw [Category.assoc, Category.assoc, hact]
    have a₂ : (x ≫ h e) ≫ (U.gt e).pG.left = (x ≫ (U'.gt e).pG.left) ≫ proj hD :=
      (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) (hpt e).1.symm).trans (Category.assoc _ _ _).symm)
    have a₃ : ∀ κ, (x ≫ ((Over.pullback (thick R' I' e)).map aG).left) ≫ D'.toPre.Oφ (U'.gt e).pG χ κ =
        x ≫ D'.toPre.Oφ ((U'.gt e).pG ≫ aB) χ κ := fun κ => (Category.assoc _ _ _).trans (congrArg (x ≫ ·)
      ((WeightPf.Oφ_comp ((Over.map (thick R' I' e)).map ((Over.pullback (thick R' I' e)).map aG)) (U'.gt e).pG χ κ).trans
        (congrArg (D'.toPre.Oφ · χ κ) (k₂ e))))
    rw [hx] at e₂
    refine (cancel_iff _ _ _ _ _).1 (Eq.trans (Eq.trans ?_ e₄) (congrArg₂ (· * ·) e₂
      ((congrArg (fun q => val (E.u (hD.xe χ)) q z J) a₂).trans e₃)))
    refine Eq.trans ?_ (e₁.symm.trans (congrArg (fun q => val ((U.gt e).t (hD.xe χ)) q z J) a₁.symm))
    exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun κ _ => congrArg (om hD.w z J J' · ^ Oinvε κ) (a₃ κ).symm) rfl

theorem main : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (φ : R →+* V), IsAdicComplete (maximalIdeal V) V → Function.Injective φ → I.map φ ≤ maximalIdeal V → ∃ (D' : DegData V (maximalIdeal V)) (hD : IsPullDeg φ D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (U' : Unif (maximalIdeal V) D' A' ((Over.pullback (specOf φ)).obj G)), IsSemiAbelian ((Over.pullback (specOf φ)).obj G) ∧ IsPullUnif φ hD (Iso.refl _) U U' ∧ (∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing V) F (algebraMap V _ (φ r))) → (∀ g, ∃! g', IsPullGtF φ hD F g g') ∧ (∀ g', ∃! g, IsPullGtF φ hD F g g') ∧ (∀ g g' y, IsPullGtF φ hD F g g' → (GtPtF.IsIota (hD.xe y) g ↔ GtPtF.IsIota y g')) ∧ ∀ k g g' h h', IsPullGtF φ hD F g g' → IsPullGtF φ hD F h h' → (GtPtF.IsNsmul k g h ↔ GtPtF.IsNsmul k g' h')) ∧ ∀ E : EndU U.toUnifPre, ∃ E' : EndU U'.toUnifPre, E'.aG = (Over.pullback (specOf φ)).map E.aG ∧ (∀ χ, hD.xe (E'.h χ) = E.h (hD.xe χ)) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing V) F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing V) F (algebraMap V _ (φ r))) → ∀ g₁ g₂ g₁' g₂', IsPullGtF φ hD F g₁ g₁' → IsPullGtF φ hD F g₂ g₂' → (E.Act g₁ g₂ ↔ E'.Act g₁' g₂') := by
  intro hL R _ _ _ I hR D A G _ _ hG U V _ _ _ φ hV hφ hI
  have hV' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨D', hD, A', U', hU⟩ := exists_pull hL.1.polBaseChange hL.2.2.2.1.unifBaseChange hL.2.2.2.2.psiOnExists
    hR hV' φ hφ hI hG U
  refine ⟨D', hD, A', U', IsSemiAbelian.pullback _ G hG, hU,
    fun F _ _ _ hF => points hL.1.globalFns hD D.tau_bimult D'.tau_bimult F hF, fun E => ?_⟩
  have := E.homG
  obtain ⟨E', h₁, h₂, h₃⟩ := exists_end hD hU E ((Over.pullback (specOf φ)).map E.aG)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  exact ⟨E', h₁, h₂, fun F _ _ _ _ => h₃ F⟩

end GlobalTheory.UT.EndBaseChange

end
