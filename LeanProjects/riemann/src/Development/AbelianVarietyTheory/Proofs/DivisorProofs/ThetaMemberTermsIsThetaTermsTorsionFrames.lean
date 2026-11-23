import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThNeZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExhaustOfLabels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDividingLabelsIffClassZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFramedPointLiesOverTorusExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameAbelianPartTorsionFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRenormalizationRigidificationMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointExtendsOverNormalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustGeometricFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.GSep.ThetaTerms

theorem yK_ne_zero {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
    (hd : X₁.M.Div X₁.S.th x₀ z₁) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X] {t : X → V}
    {δ : I → X → X} (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) :
    𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  obtain ⟨a, ha⟩ := GlobalTheory.ThetaGeneric.exists_th_ne_zero hL.1 hL.2.1 _ _ X₁.S X₁.ρ (FractionRing V) 𝔪.yK
  intro h0
  apply ha
  set y := jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy
  have hs : y (closedPoint (FractionRing V)) ⤳ z₁ := by
    have : y (closedPoint (FractionRing V)) ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hw : ∀ w, y w ⤳ y (closedPoint (FractionRing V)) := fun w => by
    rw [Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) w (closedPoint _)]
  have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hd.1).symm
  rw [𝔪.yK_eq] at h0 ⊢
  change X₁.M.val y (X₁.S.th a) = 0
  change X₁.M.val y (X₁.S.th x₀) = 0 at h0
  rw [e, RatModel.val_mul hw ((hd.of_specializes hs).2 a) (𝔪.reg _ (X₁.S.th_mem x₀)), h0, mul_zero]

theorem isThetaTerms₀_of_terms : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → IsThetaTerms₀ 𝔪.D.toPre (X₁.S.r * X₁.S.N) 𝔪.e₈ T := by
  intro I X₁ z₁ act x₀ hd V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, -, hw₀, -, hg, hT⟩ := hT
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) := by
    have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  have h0 := yK_ne_zero hd 𝔪

  obtain ⟨ρ, hρ, Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔪.A.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔪.yK) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB
    (fun _ => PolBaseChange.eSec_comm 𝔪.cart) X₁.ρ.rig X₁.ρ.rig_gen
  have htf : ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := fun a =>
    GlobalTheory.FrameMove.isTorsFrame_move (T := baseOver (Sp X₁.S.R)) (T' := TFK (R := V) (FractionRing V)) (w := 𝔪.wl)
      (h := spMap 𝔪.yK) 𝔪.cart 𝔪.wl_gen
      (fun Z r z J J' hJ hJ' =>
        (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _))))
      (hx a) (X₁.ρ.fr_tors a) (hfr a).1 (fun z J J' hJ hJ' => ((hfr a).2 z J J' hJ hJ').symm)
  obtain ⟨ρ', c, hc, hN, hmove⟩ := GlobalTheory.T.exists_renormalization_rigidification_multiple V _ 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre w₀ hw₀ ρ hρ
  choose w' fr' hw' hfr' hov hco hval using fun a : C => liesOver_scale V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre (FractionRing V) w₀
    (g' a) (w a) (x (lab a)) (fr (lab a)) (hg a).2.1 (hfr _).1 (hg a).2.2 c hc
  have htors : ∀ a, (g' a).b ^ (X₁.S.r * X₁.S.N) = 1 := fun a => by
    obtain ⟨o, h₁, h₂⟩ := (hg a).1
    letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
    have e := congrArg (GlobalTheory.TorusExt.gtProj 𝔪.D.toPre (FractionRing V)) ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 h₁)
    rw [map_nsmul] at e
    exact (congrArg Additive.toMul e).symm.trans ((isZero_iff o).1 h₂).1
  choose b hb₁ hb₂ using fun a => GlobalTheory.T.torsionPoint_extends_over_normal_domain hL.1 V 𝔪.cn.1 𝔪.cn.2.1 𝔪.D.toPre.P _ hk (g' a).b (htors a)
  refine ⟨(c / 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) • s + 0, g', b, w', hb₂, fun a => (hg a).1, ?_, fun a => ⟨hw' a, ?_⟩,
    fun mu a => ?_⟩
  · refine GlobalTheory.T.torsion_sections_exhaust_geometric_fibres hL.1 V 𝔪.cn.1 𝔪.D.toPre.P _ hk hu C b hb₁ fun p hp => ?_
    obtain ⟨a, ha⟩ := exhaust_of_labels hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hk C g' (fun a => x (lab a)) (fun a => (hg a).1)
      (fun a a' e => by
        have h₁ := hg a
        have h₂ := hg a'
        generalize w a' = om at h₂
        generalize g' a' = ga at e om h₂
        subst e
        exact GlobalTheory.T.eq_of_framedPoint_lies_over_torus_extension hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ w₀ hw₀ _ _ _ _ _ _ _ h₁.2.1 h₂.2.1 (hfr _).1 (hfr _).1
          h₁.2.2 h₂.2.2)
      (fun q y hq hy => by
        have hyN : y ^ (X₁.S.r * X₁.S.N) = 1 := (hy w₀ hw₀).1
        have e : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK =
            spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) :=
          (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom (algebraMap _ _))).symm
        obtain ⟨l, hl, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ (Geo.Tor.pushHom 𝔪.cart _ y)
          (by rw [← map_pow, hyN, map_one])
        have hl' : y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
            (X₁.ρ.pt l).left := by
          rw [← e]
          exact (congrArg (fun q => q.left) hl).symm
        have hH : l ∈ X₁.S.HH X₁.M z₁ := (GlobalTheory.T.mem_dividingLabels_iff_class_zero I X₁ z₁ act x₀ hd V ev X t δ 𝔪 l).2
          ⟨q, y, by rw [hq, map_zero], hy, hl'⟩
        obtain ⟨a, rfl⟩ : l ∈ Set.range lab := by rw [hlab]; exact hH
        refine ⟨a, 𝔪.cart.1.hom_ext ?_ ?_⟩
        · rw [hl', ← e]
          exact ((Category.assoc _ _ _).trans ((congrArg _ (hx _)).trans (Category.assoc _ _ _).symm)).symm
        · refine (Over.w y).trans (Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg _ (Over.w (x (lab a))))).symm)
          exact (Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) p hp
    refine ⟨a, Over.OverMorphism.ext ?_⟩
    rw [ha, hb₂ a, Over.comp_left, Over.comp_left, ← Category.assoc]
    congr 1
    change spMap _ ≫ spMap _ ≫ jK V = spMap _ ≫ jK V
    rw [Algebra.algebraMap_self, show spMap (RingHom.id (FractionRing V)) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  · obtain ⟨o, h₁, h₂⟩ := (hg a).1
    exact GlobalTheory.T.torsion_frame_abelian_part_torsion_frame hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ w₀ ρ' hN _ hk _ o h₁ h₂ _ _ _ (hw' a) (hov a)
      (hmove _ _ _ _ _ (htf _) (hfr' a) (hval a))
  · have h₁ := ((CoefBasic.coef_basic V 𝔪.D.toPre (FractionRing V) 1 (g' a)).2.2 (w' a) (hw' a)).2.1
    have h₂ : coef (0 : Fam 𝔪.D.toPre (FractionRing V) 1) (g' a) (w' a) (𝔪.e₈ mu) = 0 := by
      have := h₁ 0 0 1 (𝔪.e₈ mu)
      rw [one_smul, add_zero, _root_.one_mul] at this
      exact left_eq_add.1 this
    have h₃ : algebraMap V (FractionRing V) (T mu a) =
        coef ((c / 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) • s + 0) (g' a) (w' a) (𝔪.e₈ mu) := by
      rw [h₁, h₂, add_zero, div_mul_eq_mul_div, hco, ← hT, mul_div_cancel_right₀ _ h0]
    rw [h₃]
    exact CoefBasic.isCoef_coef _ (hw' a) _ _

end GlobalTheory.GSep.ThetaTerms
end
