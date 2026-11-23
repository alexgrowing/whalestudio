import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIffValEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveLabelHomLatticeModLevelThetaMember
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.RankOneModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.TorTrans

theorem exists_trait_pull {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (hR : AdmBase R (maximalIdeal R)) {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W) (φ : R →+* W)
      (ga : FractionRing R →+* FractionRing W) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W)))
      (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal W) D' A' G')
      (a : A'.A.left ⟶ A.A.left) (xe : D'.toPre.X ≃+ D.toPre.X)
      (em : AlgebraicClosure (FractionRing R) →+* AlgebraicClosure (FractionRing W)),
      IsAdicComplete (maximalIdeal W) W ∧ IsLocalHom φ ∧ (∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r)) ∧
      IsSemiAbelian G' ∧ IsGrpPullback A'.A A.A (spMap ga) a ∧ LBIso A'.L (A.L.pull a) ∧
      em.comp (algebraMap (FractionRing R) _) = (algebraMap (FractionRing W) _).comp ga ∧
      ∀ k, 1 ≤ k → ∀ (p : QkPt D.toPre (AlgebraicClosure (FractionRing R)) k)
        (x : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ A.A),
        QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing R)) k p x →
        ∃ (p' : QkPt D'.toPre (AlgebraicClosure (FractionRing W)) k)
          (x' : TFK (R := W) (AlgebraicClosure (FractionRing W)) ⟶ A'.A), p'.y = xe.symm p.y ∧
          QkToAkU U'.toUnifPre (AlgebraicClosure (FractionRing W)) k p' x' ∧ x'.left ≫ a = spMap em ≫ x.left := by
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  haveI := hR.1
  obtain ⟨W, _, _, _, φ, hW, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)
  have hloc : IsLocalHom φ := ⟨fun r hr => by
    by_contra h
    have : r ∈ (maximalIdeal W).comap φ := hc.symm ▸ (mem_maximalIdeal r).2 h
    exact (mem_maximalIdeal _).1 this hr⟩
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨D', hD, A', U', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR hW' φ hφ (Ideal.map_le_iff_le_comap.2 hc.ge) hG U
  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp φ) := (IsFractionRing.injective W _).comp hφ
  let ga : FractionRing R →+* FractionRing W := IsFractionRing.lift hinj
  have hga : ∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r) := fun r => IsFractionRing.lift_algebraMap hinj r
  have hsq : jK W ≫ spMap φ = spMap ga ≫ jK R := by
    rw [← Spec.map_comp, ← Spec.map_comp]; congr 1; ext1; exact RingHom.ext fun r => (hga r).symm
  have g₁ := GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have g₂ := ((GlobalTheory.ThetaBaseChange.grp_generic U'.toUnifPre).comp (isGrpPullback_pullback G (spMap φ))).congr hsq rfl
  let a : A'.A.left ⟶ A.A.left := g₁.1.lift _ (A'.A.hom ≫ spMap ga) (g₂.1.w.trans (Category.assoc _ _ _).symm)
  have ha : a ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = _ := g₁.1.lift_fst _ _ _
  have hb : (Iso.refl ((Over.pullback (specOf φ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf φ) =
      pullback.fst G.hom (specOf φ) := Category.id_comp _
  have gp : IsGrpPullback A'.A A.A (spMap ga) a := g₁.cancel (g₂.congr rfl ha.symm) (g₁.1.lift_snd _ _ _)
  letI : Algebra (FractionRing R) (AlgebraicClosure (FractionRing W)) :=
    ((algebraMap (FractionRing W) (AlgebraicClosure (FractionRing W))).comp ga).toAlgebra
  obtain ⟨em⟩ : Nonempty (AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] AlgebraicClosure (FractionRing W)) :=
    ⟨IsAlgClosed.lift⟩
  have hF : GlobalTheory.ArcPull.Compat φ (AlgebraicClosure (FractionRing W)) := fun r =>
    congrArg (algebraMap (FractionRing W) (AlgebraicClosure (FractionRing W))) (hga r)
  refine ⟨W, _, _, hW.1, hW.2.2, φ, ga, D', A', _, _, _, U', a, hD.xe, em.toRingHom, hW.2.1, hloc, hga,
    IsSemiAbelian.pullback _ G hG, gp, ?_, em.comp_algebraMap, fun k hk p x hpx => ?_⟩
  · have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    have hgi' : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    have H₀ : LBIso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R))) :=
      LBIso.chartPull (h := U.gen.inv.left) (chartPullSec A.L _ _ hgi)
        (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => rfl) U.ext
    have H₁ : LBIso A'.L (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst _ (jK W))) :=
      LBIso.chartPull (h := U'.gen.inv.left) (chartPullSec A'.L _ _ hgi')
        (chartPullSame U'.LG.L _ (fun _ => pullback.fst _ (jK W)) _ _ fun _ => rfl) U'.ext
    have H₂ : LBIso (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst _ (jK W)))
        (U.LG.L.pull (a ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) :=
      LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullSame U.LG.L _ (fun _ => _) _ _ fun _ => ha.trans (congrArg (_ ≫ ·) hb.symm))
        ⟨hP.lg.choose, hP.lg.choose_spec.1⟩
    have H₃ : LBIso (A.L.pull a) (U.LG.L.pull (a ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R))) :=
      LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSame U.LG.L _ (fun _ => _) _ _ fun _ => rfl) H₀
    exact (H₁.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB U.LG.isLB _) H₂).trans A'.isLB (pull_isLB U.LG.isLB _)
      (pull_isLB A.isLB _) H₃.symm
  · obtain ⟨⟨p₁, h₁⟩, hx, hgal⟩ := GlobalTheory.UT.ClModel.galois_all R _ hR D A G hG U _ _ em k hk p
    obtain ⟨x₁, hx₁⟩ := hx x
    have hw : x₁.left ≫ A.A.hom = jFK (R := W) (AlgebraicClosure (FractionRing W)) ≫ spMap ga :=
      (Over.w x₁).trans (Spec.map_comp (CommRingCat.ofHom ga) (CommRingCat.ofHom (algebraMap _ _)))
    let x' : TFK (R := W) (AlgebraicClosure (FractionRing W)) ⟶ A'.A :=
      Over.homMk (gp.1.lift x₁.left _ hw) (gp.1.lift_snd _ _ _)
    have h₄ : x'.left ≫ a = x₁.left := gp.1.lift_fst _ _ _
    obtain ⟨h₂, h₃⟩ := (GlobalTheory.ArcPull.eq_pullQk_iff hD hL.globalFns hF D.tau_bimult D'.tau_bimult p₁ _).1 rfl
    refine ⟨_, x', h₂.trans (congrArg _ h₁.1), ?_, h₄.trans hx₁⟩
    refine h5.qkBaseChange R W _ _ hR hW' φ D A G U _ (Iso.refl _) (by show IsMonHom (𝟙 _); infer_instance) A' D' hD U' hP
      _ hF k hk p₁ x₁ _ x' h₂ h₃ ?_ ((hgal p₁ x x₁ h₁ hx₁).1 hpx)
    rw [← h₄, Category.assoc, ha, hb, Category.assoc]

theorem div_and_translate {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {V : Type}
    [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X]
    {t : X → V} {δ : I → X → X} (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) {x₀ : X₁.S.Gam}
    (hx₀ : X₁.M.Div X₁.S.th x₀ z₁) (a₀ : X₁.S.Gam) (ha₀ : 𝔪.YY a₀ 0) (a : X₁.S.Gam) (mu : X) (ha : 𝔪.YY a mu) :
    (a ∈ X₁.S.supI X₁.M z₁ → ∃ w, mu = (X₁.S.r * X₁.S.N) • w) ∧
      ((∃ w, mu = (X₁.S.r * X₁.S.N) • w) → ∃ b : X₁.S.Gam, X₁.ρ.n • b = 0 ∧ a + b ∈ X₁.S.supI X₁.M z₁) := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI := 𝔪.loc
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨T, _, _, _, _, φ, ga, D', A', G', _, _, U', α, xe, em, hc, hloc, hga, hG', gp, lb, hem, hmove⟩ :=
    exists_trait_pull hA 𝔪.semi 𝔪.U
  let ξ : Sp V ⟶ X₁.M.Z := spMap ev ≫ X₁.M.Z.fromSpecStalk z₁
  have hx : ξ (closedPoint V) = z₁ := by
    show X₁.M.Z.fromSpecStalk z₁ (spMap ev (closedPoint V)) = z₁
    rw [show spMap ev (closedPoint V) = closedPoint _ from IsLocalRing.comap_closedPoint ev]
    exact Scheme.fromSpecStalk_closedPoint
  have hU : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : T) := by
    have := (X₁.S.unit.map (Spec.preimage (ξ ≫ X₁.M.s)).hom).map φ
    rwa [map_natCast, map_natCast] at this
  haveI : CharZero (FractionRing T) := charZero_of_injective_algebraMap (IsFractionRing.injective T (FractionRing T))
  have cart : IsGrpPullback A'.A X₁.ρ.P.A (spMap (ga.comp 𝔪.yK)) (α ≫ 𝔪.φ) :=
    (gp.comp 𝔪.cart).congr (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom ga)).symm rfl
  have lb' : LBIso A'.L (X₁.ρ.P.L.pull (α ≫ 𝔪.φ)) :=
    LBIso.trans A'.isLB (pull_isLB 𝔪.A.isLB _) (pull_isLB X₁.ρ.P.isLB _) lb (lbIso_pull_comp ⟨𝔪.wl, 𝔪.wl_gen⟩ α)
  obtain ⟨s, v, hs, hsv, -, hcl⟩ := GlobalTheory.Poinc.ScaleAtModel.scale_at_model _ _ X₁.S X₁.ρ T hc hU (ga.comp 𝔪.yK) A' _
    cart lb' G' hG' D' U' (GlobalTheory.ThetaGeneric.exists_th_ne_zero GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 _ _ _ X₁.ρ _ _)
  have tr : ∀ a mu, 𝔪.YY a mu → (IsUnit (v a) → ∃ w, mu = (X₁.S.r * X₁.S.N) • w) ∧
      ((∃ w, mu = (X₁.S.r * X₁.S.N) • w) → ∃ b : X₁.S.Gam, X₁.ρ.n • b = 0 ∧ IsUnit (v (a + b))) := by
    rintro a mu ⟨p, x, hp, hq, hxa⟩
    obtain ⟨p', x', hp', hq', hx'⟩ := hmove _ hk p x hq
    obtain ⟨h₁, h₂⟩ := hcl a p' x' hq' (by
      rw [← Category.assoc, hx', Category.assoc, hxa, ← Category.assoc, ← RingHom.comp_assoc, ← hem, RingHom.comp_assoc]
      exact congrArg (· ≫ _) (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom em)).symm)
    rw [hp] at hp'
    refine ⟨fun h => ?_, fun ⟨w, hw⟩ => h₂ ⟨xe.symm (𝔪.e₈ w), by rw [hp', hw, map_nsmul, map_nsmul]⟩⟩
    obtain ⟨z, hz⟩ := h₁ h
    refine ⟨𝔪.e₈.symm (xe z), ?_⟩
    rw [← map_nsmul, ← map_nsmul, ← hz, hp', AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  have hsp : ∀ w, (jK V ≫ ξ) w ⤳ (jK V ≫ ξ) (closedPoint (FractionRing V)) := fun w => by
    rw [Subsingleton.elim w (closedPoint (FractionRing V))]
  have hsx : ξ (closedPoint V) ⤳ z₁ := hx ▸ specializes_rfl
  let wv : X₁.S.Gam → V := fun b => RatModel.valLoc ξ z₁ hsx ⟨X₁.S.th b / X₁.S.th x₀, hx₀.2 b⟩
  have hw : ∀ b, φ (wv b) * v x₀ = v b := fun b => by
    have e1 : X₁.M.val (jK V ≫ ξ) (X₁.S.th b / X₁.S.th x₀) = algebraMap V (FractionRing V) (wv b) :=
      RatModel.val_spMap_comp (algebraMap V (FractionRing V)) ξ hsx ⟨X₁.S.th b / X₁.S.th x₀, hx₀.2 b⟩
    have e2 := RatModel.val_mul hsp (RatModel.O_le_of_specializes (hx ▸ (IsLocalRing.specializes_closedPoint
      (jK V (closedPoint (FractionRing V)))).map ξ.continuous) (hx₀.2 b)) (𝔪.reg _ (X₁.S.th_mem x₀))
    rw [div_mul_cancel₀ _ hx₀.1, e1] at e2
    have e3 : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ =
        algebraMap V (FractionRing V) (wv b) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
      rw [𝔪.yK_eq, 𝔪.yK_eq]; exact e2
    have e4 := congrArg ga e3
    rw [map_mul, hga] at e4
    have e5 := hsv b
    have e6 := hsv x₀
    rw [RingHom.comp_apply] at e5 e6
    rw [e5, e6, ← _root_.mul_assoc, mul_comm _ s, _root_.mul_assoc, ← map_mul] at e4
    exact IsFractionRing.injective T (FractionRing T) (mul_left_cancel₀ hs e4).symm
  obtain ⟨b₀, -, hb₀⟩ := (tr a₀ 0 ha₀).2 ⟨0, (nsmul_zero _).symm⟩
  have hv0 : IsUnit (v x₀) := isUnit_of_mul_isUnit_right (show IsUnit (φ (wv (a₀ + b₀)) * v x₀) by rw [hw]; exact hb₀)
  have hset : ∀ b, b ∈ X₁.S.supI X₁.M z₁ ↔ IsUnit (v b) := fun b => by
    show X₁.M.Div X₁.S.th b z₁ ↔ IsUnit (v b)
    rw [hx₀.div_iff_isUnit b, ← RatModel.isUnit_valLoc_iff ξ hx, ← hw b, IsUnit.mul_iff, and_iff_left hv0,
      isUnit_map_iff φ]
  simp only [hset]
  exact tr a mu ha

theorem exists_translate_mem_supI : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ a, 𝔪.YY a 0 → ∃ b : X₁.S.Gam, X₁.ρ.n • b = 0 ∧ a + b ∈ X₁.S.supI X₁.M z₁ := by
  intro I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 x₀ hx₀ a ha
  exact (div_and_translate 𝔪 hx₀ a ha a 0 ha).2 ⟨0, (nsmul_zero _).symm⟩

end GlobalTheory.GSep.TorTrans
