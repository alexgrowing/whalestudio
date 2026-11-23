import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionToG
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUOfIntegralTorsionPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel GlobalTheory.ConstLin GlobalTheory.FinitePartGeneric

noncomputable section
namespace GlobalTheory.ToricTorsionSpec

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (k : ℕ), 1 ≤ k → ∀ τ : Multiplicative D.toPre.X →* Rˣ, τ ^ k = 1 → ∃ s : 𝟙_ (Over (Sp R)) ⟶ G, s ^ k = 1 ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ev₀ : R →+* V), IsLocalHom ev₀ → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf ev₀)).obj G), IsMonHom bc.hom → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (hD : IsPullDeg ev₀ D.toPre D'.toPre) (U' : Unif (maximalIdeal V) D' A' G'), IsPullUnif ev₀ hD bc U U' → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (τ' : Multiplicative D'.toPre.X →* Kˣ), (∀ χ', ((τ' χ' : Kˣ) : K) = algebraMap (FractionRing V) K (algebraMap V (FractionRing V) (ev₀ ((τ (Multiplicative.ofAdd (hD.xe (Multiplicative.toAdd χ'))) : Rˣ) : R)))) → ∀ (q : QkPt D'.toPre K k) (x' : TFK (R := V) K ⟶ A'.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU U'.toUnifPre K k q x' → x'.left ≫ genMap U' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) = spMap ((algebraMap (FractionRing V) K).comp ((algebraMap V (FractionRing V)).comp ev₀)) ≫ s.left := by
  intro R _ _ _ hB G _ _ hG D A U k hk τ hτ
  obtain ⟨hR, hC⟩ := hB
  haveI := hC
  obtain ⟨N, g₀, x₀, hfin, -, -, hU, htors, hform⟩ := GlobalTheory.ToricTorsionSecUnif.exists_torsion_toG R hR G D A U k hk
  let u : D.toPre.X →+ Additive Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ :=
    AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ (Multiplicative.ofAdd χ)))) (fun χ χ' => by
      simp only [ofAdd_add, map_mul, unitOn, ofMul_mul])
  have hu : k • u = 0 := by
    refine AddMonoidHom.ext fun χ => Additive.toMul.injective ?_
    have e : (τ (Multiplicative.ofAdd χ)) ^ k = 1 := by rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    simp only [u, AddMonoidHom.nsmul_apply, AddMonoidHom.mk'_apply, toMul_nsmul, toMul_ofMul, unitOn, ← map_pow, e,
      map_one, AddMonoidHom.zero_apply, toMul_zero]
  obtain ⟨gT, hgT⟩ := GlobalTheory.TorusTorsion.exists_torusPt (D := D.toPre) (T := 𝟙_ (Over (Sp R))) u
  obtain ⟨g', h₁, h₂⟩ := GlobalTheory.TorusTorsion.exists_nsmul_zero k u hu hgT
  obtain ⟨h, hh, -⟩ := hU _ _ ⟨g', h₁, h₂⟩
  refine ⟨h ≫ x₀, by rw [← MonObj.comp_pow, htors, MonObj.comp_one], ?_⟩
  intro V _ _ _ _ hVc ev₀ hev G' _ _ bc hbc D' A' hD U' hUU' K _ _ _ τ' hτ' q x' hq htor hqx'
  have hV : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hVc⟩
  have hG' : IsSemiAbelian G' := GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (specOf ev₀) G hG)
  have hL := firstFiveLaws
  have hL2 := abelianSchemeLaws_all
  let ξ : Sp V ⟶ N.left := spMap ev₀ ≫ h.left
  have hh' : ξ ≫ N.hom = (𝟙_ (Over (Sp V))).hom ≫ spMap ev₀ := by
    simp only [ξ, Category.assoc, Over.w h]
    rfl
  obtain ⟨gp, hgp⟩ : ∃ gp : GtPt D'.toPre (𝟙_ (Over (Sp V))), ConstLin.Thru hD.w hD.xe (T' := 𝟙_ _) ξ g₀ gp :=
    ConstPoint.exists_gtPt_through hL.1.globalFns (pull_grp hD) hD.w_gen hD.xe.toAddMonoidHom hD.c_pr
      (T' := 𝟙_ _) ξ hh' g₀
  let x₁' : 𝟙_ (Over (Sp V)) ⟶ (Over.pullback (specOf ev₀)).obj G :=
    Over.homMk (pullback.lift (ξ ≫ x₀.left) (𝟙_ (Over (Sp V))).hom (by rw [Category.assoc, Over.w]; exact hh'))
      (pullback.lift_snd _ _ _)
  let x₁ : 𝟙_ (Over (Sp V)) ⟶ G' := x₁' ≫ bc.inv
  have e₁ : x₁'.left ≫ pullback.fst G.hom (specOf ev₀) = ξ ≫ x₀.left := pullback.lift_fst _ _ _
  have e₂ : x₁.left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) = ξ ≫ x₀.left := by
    rw [Over.comp_left, Category.assoc, ← Category.assoc bc.inv.left, ← Over.comp_left, Iso.inv_hom_id, Over.id_left,
      Category.id_comp, e₁]
  have gG := isGrpPullback_pullback G (spMap ev₀)
  have hk₁' : x₁' ^ k = 1 := ConstGrp.push_injective gG _ (by
    let ρ : Over.mk ((𝟙_ (Over (Sp V))).hom ≫ spMap ev₀) ⟶ N := Over.homMk ξ hh'
    have e : pushHom gG _ x₁' = ρ ≫ x₀ := Over.OverMorphism.ext e₁
    rw [map_pow, map_one, e, ← MonObj.comp_pow, htors, MonObj.comp_one])
  haveI : IsMonHom bc.inv := inferInstance
  have hk₁ : x₁ ^ k = 1 := by
    show (x₁' ≫ bc.inv) ^ k = 1
    rw [← MonObj.pow_comp, hk₁', MonObj.one_comp]
  have hp := isPointOf_thru hUU' hgp e₂ ((TorsionFormCompare.formalEq_iff _ _ _).1 hform)
  have gpg := pull_grp hD
  have hb : gp.b = 1 := Over.OverMorphism.ext (gpg.1.hom_ext (((hgp 0).1 2).trans (Eq.trans ?_ ((hgp 0).1 3).symm))
    ((Over.w _).trans (Over.w _).symm))
  swap
  · show ξ ≫ g₀.b.left = ξ ≫ (1 : N ⟶ D.toPre.P.A).left
    have e1 : h.left ≫ g₀.b.left = h.left ≫ (1 : N ⟶ D.toPre.P.A).left := by
      have t1 : gT.b.left = h.left ≫ g₀.b.left := hh.1
      have t2 : gT.b = 1 := (hgT 0).1
      have t3 : h ≫ (1 : N ⟶ D.toPre.P.A) = 1 := MonObj.comp_one h
      rw [← t1, t2, ← t3]
      rfl
    simp only [ξ, Category.assoc, e1]
  let uV : D'.toPre.X → Γ((𝟙_ (Over (Sp V))).left, ⊤)ˣ := fun y =>
    unitOn (Units.map ev₀.toMonoidHom (τ (Multiplicative.ofAdd (hD.xe y))))
  have hgpT : ∀ y, TorusVal gp y (uV y) := by
    intro y
    refine ⟨hb, corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_⟩
    obtain ⟨J, hJ⟩ := ConstFam.exists_good' D.toPre.P.isLB z
    have v := hgp.val_id y z hJ hJ'
    rw [GlobalTheory.TorusTorsion.val_unitGen _ _ hJ']
    generalize Geo.Tor.val (gp.s y) (𝟙 _) z J' = s at v ⊢
    rw [hb, _root_.mul_one, inv_mul_cancel, _root_.one_mul, mul_inv_cancel, _root_.one_mul] at v
    rw [← v]
    have c := val_corr hJ (hh.2 (hD.xe y)) (spMap ev₀)
    have c2 := GlobalTheory.TorusTorsion.TorusVal.val_eq (hgT (hD.xe y)) (spMap ev₀) hJ
    have c3 : Geo.Tor.val (g₀.s (hD.xe y)) ξ z J = gm (spMap ev₀) z ⊤ (Additive.toMul (u (hD.xe y))) := by
      first
      | exact ((val_pull hJ _ _ _).symm.trans (c.symm.trans c2))
      | exact ((val_pull hJ _ _ _).symm.trans (c.trans c2))
      | exact (c.symm.trans c2)
      | exact (c.trans c2)
    rw [c3]
    refine Units.ext ?_
    rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial]
    have e := GlobalTheory.ToricTorsionSec.appTop_unitOn ev₀ (τ (Multiplicative.ofAdd (hD.xe y)))
    first
    | (simp only [uV]; rw [← e]; rfl)
    | (rw [show (uV y).val = _ from e.symm]; rfl)
    | (erw [← e]; rfl)
  let fK : V →+* K := (algebraMap (FractionRing V) K).comp (algebraMap V (FractionRing V))
  let uK : D'.toPre.X →+ Additive Γ((Over.mk (spMap fK)).left, ⊤)ˣ :=
    AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ' (Multiplicative.ofAdd χ)))) (fun χ χ' => by
      simp only [ofAdd_add, map_mul, unitOn, ofMul_mul])
  obtain ⟨gK, hgK⟩ := GlobalTheory.TorusTorsion.exists_torusPt (D := D'.toPre) (T := Over.mk (spMap fK)) uK
  have hpK := GlobalTheory.ToricTorsionSec.isPullF_torusPt τ' gK hgK q.g htor
  let ρ : Over.mk (spMap fK) ⟶ 𝟙_ (Over (Sp V)) := toUnit _
  have hρ : GtPt.IsPull ρ.left gp gK := GlobalTheory.TorusTorsion.isPull_of_units ρ hgpT hgK fun χ => by
    refine (GlobalTheory.ToricTorsionSec.appTop_unitOn fK _).trans ?_
    congr 2
    refine Units.ext ?_
    have := hτ' (Multiplicative.ofAdd χ)
    simp only [toAdd_ofAdd] at this
    exact this.symm
  have hpF := GlobalTheory.ToricTorsionSec.isPullF_trans hρ hpK
  have hTF : (toUnit (TF (R := V) K)).left = 𝟙 _ ≫ ρ.left := by
    rw [Category.id_comp]
    have e₁ := Over.w (toUnit (TF (R := V) K))
    have e₂ := Over.w ρ
    simp only [Over.mk_hom] at e₁ e₂
    rw [← Category.comp_id (toUnit (TF (R := V) K)).left, ← Category.comp_id ρ.left]
    exact e₁.trans ((GlobalTheory.ToricTorsionSec.spMap_comp _ _).symm.trans e₂.symm)
  have hpF' : GtPt.IsPullF K (toUnit (TF (R := V) K)).left gp q.g := by
    rw [hTF]; exact hpF
  let yK : TFK (R := V) K ⟶ (Over.pullback (jK V)).obj G' :=
    Over.homMk (pullback.lift ((toUnit (TF (R := V) K)).left ≫ x₁.left) (jFK (R := V) K)
      (by rw [Category.assoc, Over.w x₁]; exact Over.w (toUnit (TF (R := V) K)))) (pullback.lift_snd _ _ _)
  let xF : TFK (R := V) K ⟶ A'.A := yK ≫ U'.gen.hom
  have hxF : xF.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK V) = (toUnit (TF (R := V) K) ≫ x₁).left := by
    rw [← Category.assoc, ← Over.comp_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  have hQ := qkToAkU_of_integral_torsion hL.1 V (maximalIdeal V) hV (maximalIdeal.isMaximal V).ne_top D' A' G' U' k hk
    x₁ gp hk₁ (fun e => ?_) K q xF hq hpF' hxF
  · have hEq := GlobalTheory.TorsionImage.qkToAkU_unique hL2.1 hL2.2 V (maximalIdeal V) hV D' A' G' hG' U' K k hk q x' xF hqx' hQ
    subst hEq
    have hρl : ρ.left = spMap fK := by
      have e₂ := Over.w ρ
      rw [← Category.comp_id ρ.left]
      exact e₂
    show xF.left ≫ (U'.gen.inv.left ≫ pullback.fst G'.hom (jK V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf ev₀) = _
    rw [← Category.assoc, hxF, Over.comp_left, Category.assoc, e₂, hTF, Category.id_comp, hρl, Over.comp_left]
    simp only [ξ, ← Category.assoc]
    congr 1
    rw [← GlobalTheory.ToricTorsionSec.spMap_comp]
  · let xe : Over.mk (thick V (maximalIdeal V) e) ⟶ (Over.map (thick V (maximalIdeal V) e)).obj
        (thickObj V (maximalIdeal V) e G') :=
      Over.homMk (pullback.lift (toUnit (Over.mk (thick V (maximalIdeal V) e)) ≫ x₁).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm))
        (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))).trans (Category.id_comp _))
    have hxe : xe ≫ fstG _ e _ = toUnit _ ≫ x₁ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have c := hp e _ (toUnit (Over.mk (thick V (maximalIdeal V) e))).left xe.left (congrArg (·.left) hxe)
    exact ⟨xe, hxe, Over.OverMorphism.ext c.1, c.2⟩

end GlobalTheory.ToricTorsionSpec
