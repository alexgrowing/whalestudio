import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDomainLiftPolarizedVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOverFiniteExt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.SiegelOfPolarised GlobalTheory.PrimNorm
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelAfterExt

theorem weilIs_of_ext {O C : Type} [Field O] [Field C] (β : O →+* C) {Q : PolAV (Sp O)}
    {Q' : PolAV (Sp C)} {ψ : Q'.A.left ⟶ Q.A.left} (hQ : IsPolFibre β Q Q' ψ)
    (n : ℕ) (x y : 𝟙_ (Over (Sp O)) ⟶ Q.A) (u : Oˣ) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (hw : WeilIs Q'.A Q'.L n (ObjPull.secPull hQ.2.1 x) (ObjPull.secPull hQ.2.1 y)
      (unitOn (Units.map β.toMonoidHom u))) : WeilIs Q.A Q.L n x y (unitOn u) := by
  have H := hQ.2.1
  have := Q.isAb.comm
  have hG : GlobalFnsSt := GlobalTheory.laws_without_cohomology.1
  let e : Over.mk (spMap β) ⟶ 𝟙_ (Over (Sp O)) := Over.homMk (spMap β) (Category.comp_id _)
  obtain ⟨c, hc, -⟩ := LevelCompare.weil_existsUnique Q n x y hx hy
  have h₁ := CommPairing.weilIs_pull hG Q.isAb Q.isLB e hc
  have h₂ := (weilIs_grpPullback_of_comm _ _ Q.A Q'.A _ ψ Q.L Q'.L Q.isLB Q'.isLB H hQ.2.2.symm _ n _ _
    (pushPt H.1.w _) (pushPt H.1.w _) _ rfl rfl).1 hw
  have h₃ : WeilIs Q.A Q.L n (e ≫ x) (e ≫ y) (unitOn (Units.map β.toMonoidHom u)) :=
    UnifPoint.weilIs_congr (Category.id_comp _) (ObjPull.secPull_left H x) (ObjPull.secPull_left H y) h₂
  have h₄ := CommutatorPairing.weilIs_unique hG Q.isAb Q.isLB h₁ h₃
  obtain ⟨w, rfl⟩ : ∃ w : Oˣ, unitOn w = c :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom.toMonoidHom c,
      Units.ext (CommRingCat.inv_hom_apply (Scheme.ΓSpecIso (CommRingCat.of O)) c.val)⟩
  have e' : Units.map e.left.appTop.hom.toMonoidHom (unitOn w) = unitOn (Units.map β.toMonoidHom w) :=
    Units.ext (congrArg (fun q => q.hom w.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  have inj : Function.Injective (unitOn (R := C)) :=
    Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.injective
  have h₅ := congrArg Units.val (inj (e'.symm.trans h₄))
  obtain rfl : w = u := Units.ext (β.injective h₅)
  exact hc

theorem exists_ext_torsion (K : Type) [Field K] (P₀ : PolAV (Sp K)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' Ω : Type) [Field K''] [Field Ω] (i : K' →+* K'') (f : K →+* K''), i.comp (algebraMap K K') = f →
      ∀ (P : PolAV (Sp K'')) (ψ : P.A.left ⟶ P₀.A.left), IsPolFibre f P₀ P ψ →
      ∀ (σ : K'' →+* Ω) (Q : PolAV (Sp Ω)) (ψσ : Q.A.left ⟶ P.A.left) (hQ : IsPolFibre σ P Q ψσ),
        ∀ y, y ^ N = 1 → ∃ x, ObjPull.secPull hQ.2.1 x = y := by
  obtain ⟨K', _, _, hfin, H⟩ := TorsRational.exists_ext_points K (torsion P₀.A N)
    (AbTorsionAnyBase.isFinite_and_flat_torsion (Sp K) P₀.A P₀.isAb N hN).1
  refine ⟨K', inferInstance, inferInstance, hfin, ?_⟩
  intro K'' Ω _ _ i f hf P ψ hP σ Q ψσ hQ y hy
  letI : Algebra K' K'' := i.toAlgebra
  letI : Algebra K K'' := f.toAlgebra
  haveI : IsScalarTower K K' K'' := IsScalarTower.of_algebraMap_eq' hf.symm
  have hPg : IsGrpPullback P.A P₀.A (spMap f) ψ := hP.2.1
  have hQg : IsGrpPullback Q.A P.A (spMap σ) ψσ := hQ.2.1
  let x0 := ObjPull.pushEquiv hPg _ (ObjPull.pushEquiv hQg (𝟙_ _) y)
  have hx0 : x0 ^ N = 1 := by simp only [x0, ← map_pow, hy, map_one]
  have hx0l : x0.left = (y.left ≫ ψσ) ≫ ψ := rfl
  have hmul : x0 ≫ mulN P₀.A N = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx0, Hom.one_def]
  let t0 : _ ⟶ torsion P₀.A N := pullback.lift x0 (toUnit _) hmul
  have ht0 : t0 ≫ torsion.ι P₀.A N = x0 := pullback.lift_fst _ _ _
  have hs : ((𝟙_ (Over (Sp Ω))).hom ≫ spMap σ) ≫ spMap f = spMap (σ.comp f) := by
    rw [Category.assoc, spMap_comp_spMap]
    exact Category.id_comp _
  obtain ⟨w, hw⟩ := H K'' Ω σ t0.left ((Over.w t0).trans hs)
  have hw2 : w ≫ (torsion P₀.A N).hom = (𝟙_ (Over (Sp K''))).hom ≫ spMap f := by
    refine spec_map_field_cancel σ _ _ ?_
    rw [← Category.assoc, hw, Over.w t0]
    refine hs.trans ?_
    rw [← spMap_comp_spMap]
    exact congrArg (spMap σ ≫ ·) (Category.id_comp _).symm
  let w1 : Over.mk ((𝟙_ (Over (Sp K''))).hom ≫ spMap f) ⟶ P₀.A :=
    Over.homMk (w ≫ (torsion.ι P₀.A N).left) (by rw [Category.assoc, Over.w, hw2]; rfl)
  let x := (ObjPull.pushEquiv hPg (𝟙_ _)).symm w1
  have hxl : x.left ≫ ψ = w ≫ (torsion.ι P₀.A N).left := ObjPull.pushEquiv_symm_left hPg _ w1
  refine ⟨x, ?_⟩
  apply Over.OverMorphism.ext
  refine hQg.1.hom_ext ?_ ?_
  · rw [ObjPull.secPull_left]
    refine hPg.1.hom_ext ?_ ?_
    · rw [Category.assoc, hxl, ← Category.assoc, hw, ← Over.comp_left, ht0, hx0l]
    · rw [Category.assoc, Over.w x, Category.assoc, hQg.1.w, ← Category.assoc, Over.w y]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [Over.w, Over.w]

theorem exists_ext_level (K : Type) [Field K] [CharZero K] (P₀ : PolAV (Sp K)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), Module.Finite K K' ∧
      ∀ (K'' : Type) [Field K''] (i : K' →+* K'') (f : K →+* K''), i.comp (algebraMap K K') = f →
      ∀ (P : PolAV (Sp K'')) (ψ : P.A.left ⟶ P₀.A.left), IsPolFibre f P₀ P ψ →
      ∀ (g : ℕ), P.g = g → ∀ ze : K''ˣ, IsPrimitiveRoot (ze : K'') N →
      ∃ lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp K'')) ⟶ P.A), (∀ x y, lev (x + y) = lev x * lev y) ∧
        (∀ x, lev x ^ N = 1) ∧ ∀ x y, WeilIs P.A P.L N (lev x) (lev y) (unitOn (ze ^ omegaStd x y)) := by
  obtain ⟨K', _, _, hfin, H⟩ := exists_ext_torsion K P₀ N hN
  refine ⟨K', inferInstance, inferInstance, hfin, fun K'' _ i f hf P ψ hP g hg ze hze => ?_⟩
  let Ω := AlgebraicClosure K''
  let σ : K'' →+* Ω := algebraMap K'' Ω
  haveI : CharZero Ω := (σ.comp f).charZero_iff (σ.comp f).injective |>.1 inferInstance
  obtain ⟨Q, φ, hQ⟩ := exists_isPolFibre GlobalTheory.laws_without_cohomology.2.2.1 σ P
  obtain ⟨l, h₁, h₂, h₃⟩ := SiegPt.exists_level (O := Ω) (C := Ω) Q g N (Units.map σ.toMonoidHom ze) (hQ.1.trans hg)
    (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (by omega))) (hze.map_of_injective σ.injective)
  have hinj : Function.Injective (ObjPull.secPull hQ.2.1) := fun a b h =>
    Over.OverMorphism.ext (spec_map_field_cancel σ _ _ (by
      rw [← ObjPull.secPull_left hQ.2.1, ← ObjPull.secPull_left hQ.2.1, h]))
  choose t ht using fun a => H K'' Ω i f hf P ψ hP σ Q φ hQ (l a) (h₂ a)
  have tors : ∀ a, t a ^ N = 1 := fun a => hinj (by rw [map_pow, ht, map_one, h₂])
  refine ⟨t, fun a b => hinj ?_, tors, fun a b => weilIs_of_ext σ hQ N _ _ _ (tors a) (tors b) ?_⟩
  · rw [map_mul, ht, ht, ht, h₁]
  · rw [ht, ht, map_zpow]
    exact h₃ a b

open GlobalTheory.ArcPull ReciprocityTheory.ChartRestriction.G.DVR in

theorem exists_pull {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I')
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) (A' : PolAV (Sp (FractionRing R')))
    (gA : A'.A.left ⟶ A.A.left) (hA : IsPolFibre (fracMap hg) A A' gA) :
    ∃ (D' : DegData R' I') (_ : IsPullDeg g D.toPre D'.toPre),
      Nonempty (Unif I' D' A' ((Over.pullback (specOf g)).obj G)) := by
  obtain ⟨-, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨dA, gpA, tA⟩ := hA
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
      ((LBIso.symm tA).chartPull (Geo.Tor.chartPullPull A'.L _ _ rfl) (Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
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
  obtain ⟨Wo, hWo, hψ⟩ := h5.psiOnExists R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, -, -⟩ := h4.unifBaseChange R R' I I' hR hR' g hI D A G hG U Wo hψ hgen
    ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨D', hD, ⟨U'⟩⟩

end GlobalTheory.LevelAfterExt
