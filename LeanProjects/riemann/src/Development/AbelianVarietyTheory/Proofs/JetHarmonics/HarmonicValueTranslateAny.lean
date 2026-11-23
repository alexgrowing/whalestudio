import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GCorCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvA
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlphaFormHarmonicValueAtFramedPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueConnectionIntegralChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslateThetaFrameGermEqUnitMulBoxProduct
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OneColumnTranslateSectionRootOfUnityMul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleValueIntegralFramedPointExtensionField
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.JetDUnique
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetFramesDifferByUnitEachOrder
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndTop

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.OneOrder

section Basic

variable {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {D : DegData V I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]

def JetAt (U : UnifPre I D A G) {κ : Type} (m : ℕ) (x : overAt (𝟙 (Sp V)) (Jet V κ m) ⟶ G)
    (τ : LB.Gen (LB.LinComb U.LG.L (Y := Sp (Jet V κ m)) (K := Fin 1) (fun _ => x.left) (fun _ => (1 : ℤ))))
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] (q : ℕ) (σ : U.SecGF F q) (a : Jet F κ m) : Prop :=
  ∃ zF : Sp (Jet F κ m) ⟶ (UnifPre.GF (R := V) (G := G) F).left,
    zF ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left =
      spMap (algebraMap F (Jet F κ m)) ∧
    zF ≫ UnifPre.gFK (R := V) (G := G) F = spMap (jetCoef (algebraMap V F) κ m) ≫ x.left ∧
    ∀ (y : Sp (Jet F κ m)) (J : (Sp (Jet F κ m) ⟶ G.left) → U.LG.L.ι), Good U.LG.L y J →
      sval σ zF y J = gs (𝟙 _) y ⊤ (toΓ _ a) * (val τ (spMap (jetCoef (algebraMap V F) κ m)) y J ^ q).val

variable (U : UnifPre I D A G) {κ : Type} [Fintype κ] [DecidableEq κ]
  (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F]

theorem exists_jetAt [IsScalarTower V (FractionRing V) F] (z : JetPts G κ) (m : ℕ)
    (τ : LB.Gen (LB.LinComb U.LG.L (Y := Sp (Jet V κ m)) (K := Fin 1) (fun _ => (z m).left) (fun _ => (1 : ℤ))))
    (hτ : τ.IsGen) (q : ℕ) (σ : U.SecGF F q) : ∃ a, JetAt U m (z m) τ F q σ a := by
  have hL := U.LG.isLB
  obtain ⟨a, a₁, a₂⟩ := GermBasic.exists_jetPt (F := F) z m
  obtain ⟨v, hv⟩ := ExpansionValueZero.exists_coeff (A := Jet F κ m) hL σ a
    (GeneratorPullback.powGen U.LG.L _ _ (LB.pullGen U.LG.L _ _ τ (spMap (jetCoef (algebraMap V F) κ m))) q)
    (powGen_isGen_of_isGen _ (pullGen_isGen _ _ _ _ hτ _) q) (fun W _ h => by simp only [a₂, _root_.mul_one])
  refine ⟨v, a, a₁, a₂, fun y J hJ => ?_⟩
  have e := hv _ (𝟙 _) y J hJ
  rw [Category.id_comp] at e
  refine e.trans ?_
  have e' := val_pull (φ := fun _ : Fin 1 => (z m).left) (ε := fun _ => (1 : ℤ)) hJ τ (spMap (jetCoef (algebraMap V F) κ m)) (𝟙 _)
  rw [Category.id_comp] at e'
  rw [← e']
  exact congrArg (fun u => cst (𝟙 _) y v * Units.val u) (map_pow _ _ _)

theorem jetAt_smul (m : ℕ) (x : overAt (𝟙 (Sp V)) (Jet V κ m) ⟶ G)
    (τ : LB.Gen (LB.LinComb U.LG.L (Y := Sp (Jet V κ m)) (K := Fin 1) (fun _ => x.left) (fun _ => (1 : ℤ))))
    (q : ℕ) (σ σ' : U.SecGF F q) (c : F) (a a' : Jet F κ m)
    (hσ : ∀ jj, σ'.f jj = resTop _ (scal (CartesianMonoidalCategory.fst (TFK (R := V) F)
      ((Over.pullback (jK V)).obj G)).left c) * σ.f jj)
    (h : JetAt U m x τ F q σ a) (h' : JetAt U m x τ F q σ' a') : a' = algebraMap F _ c * a := by
  have hL := U.LG.isLB
  obtain ⟨z, a₁, a₂, ha⟩ := h
  obtain ⟨b, b₁, b₂, hb⟩ := h'
  obtain rfl : z = b := GermBasic.gf_ext (a₁.trans b₁.symm) (a₂.trans b₂.symm)
  refine H1.cst_ext fun y => ?_
  obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hL y (K := PEmpty) PEmpty.elim PEmpty.elim (fun k => k.elim) (fun k => k.elim)
  have e := SectionScalarValuation.sval_lin (fun _ : Fin 1 => scal (CartesianMonoidalCategory.fst (TFK (R := V) F)
      ((Over.pullback (jK V)).obj G)).left c) (fun _ => σ) (s := σ') (fun jj => by rw [Fin.sum_univ_one]; exact hσ jj) z y hJ
  rw [Fin.sum_univ_one, ha y J hJ, hb y J hJ, ← _root_.mul_assoc] at e
  refine ((Units.mul_left_inj _).1 e).trans (Eq.trans ?_ (H1.cst_mul _ _ _ _).symm)
  refine congrArg₂ (· * ·) ?_ rfl
  refine (gs_pull z _ y ⊤ trivial _).trans ?_
  rw [a₁, ← ExpansionValueZero.cst_comp, Category.id_comp]
  rfl

end Basic

section Box
open GlobalTheory.BoxFamily FrameN BoxGerm

set_option maxHeartbeats 1000000 in

theorem psJet_of_box {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] {t : SAB H (Sp V)} (P : PELUnif (maximalIdeal V) t)
    {d : ℕ} (act : 𝓞 E → Fin d → PS V 1 d) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
    (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t)
    (τ₁ : Frames P.U.LG.L (κ := Fin 1 × Fin d) xT) (g₁ : τ₁.Gen) (el : IsEL P xT act eT wPT τ₁)
    (n : ℕ) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V))
    [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' t.G n)
    (U' : Unif (maximalIdeal V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (q : ℕ)
    (hq : 1 ≤ q) (m : ℕ) (σ : Fin n → P.U.toUnifPre.SecGF F q) (s : Fin n → Fam P.D.toPre F q)
    (a : Fin n → Jet F (Fin 1 × Fin d) m) (σ' : U'.toUnifPre.SecGF F q) (S : Fam D'.toPre F q) (c : F) (h : PS F n d)
    (hσ : ∀ i, P.U.toUnifPre.ExpandsG F q (σ i) (s i))
    (ha : ∀ i, JetAt P.U.toUnifPre m (xT m) (τ₁ m) F q (σ i) (a i))
    (hS : IsBoxFam pD F q S s) (hE' : U'.toUnifPre.ExpandsG F q σ' (c • S))
    (hh : IsGermN P xT act eT wPT pG PU.toUnifPowOf F q σ' h) :
    psJet m h = algebraMap F _ c * ∏ i, jetCopy (S := F) d m i (a i) := by
  obtain ⟨h₁, h₂, -, h₄, -⟩ := GlobalTheory.firstFiveLaws
  have hT := GlobalTheory.twistBaseChange_and_valuation_statements.1
  have hM : P.U.LG.L.IsLB := P.U.LG.isLB
  have hM' : U'.LG.L.IsLB := U'.LG.isLB
  obtain ⟨τ, hτ, hv₀⟩ := exists_boxPull_gen (pr := fun i => (pG.pr i).left) PU.wL PU.wL_gen hM hM' (K := Fin 1)
      (φ' := fun _ => (zV pG xT m).left) (φ := fun _ _ => (xT m).left) (ε := fun _ => 1) (cpy V n d m)
      (fun i _ => zV_pr pG xT m i) (fun _ => τ₁ m) (fun _ => g₁ m)
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V (Fin n × Fin d) m)) (y : Z) (J J'), Good P.U.LG.L y J →
      Good U'.LG.L y J' →
      om PU.wL y J J' (r ≫ (zV pG xT m).left) * val τ r y J' = ∏ i, val (τ₁ m) (r ≫ cpy V n d m i) y J := by
    intro Z r y J J' hJ hJ'
    have := hv₀ Z r y J J' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_one] at this
  obtain ⟨z, a', b', h₀, hp, k₂, k₃, k₄⟩ := hh m
  have hzg : z ≫ UnifPre.gFK (R := V) (G := G') F =
      spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m) ≫ (zV pG xT m).left := by
    refine pow_ext pG _ _ ?_ fun i => ?_
    · have hg : UnifPre.gFK (R := V) (G := G') F ≫ G'.hom =
          (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left ≫
            (TFK (R := V) F).hom ≫ jK V := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, Over.w]
        exact congrArg (· ≫ jK V) (Over.w (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G')))
      rw [Category.assoc, hg, ← Category.assoc, h₀, Category.assoc _ (zV pG xT m).left, Over.w (zV pG xT m)]
      show spMap _ ≫ spMap (algebraMap (FractionRing V) F) ≫ spMap (algebraMap V (FractionRing V)) =
        spMap _ ≫ spMap (algebraMap V (Jet V (Fin n × Fin d) m)) ≫ 𝟙 _
      simp only [spMap, Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [JetTr.jetCoef_alg, ← IsScalarTower.algebraMap_eq]
    · rw [Category.assoc, hp, Category.assoc, zV_pr, ← Category.assoc, coef_cpy, jptN]
  obtain ⟨σb, hσb, -⟩ := (GlobalTheory.expandsG_bijective_of_dvr h₁ h₂ h₄ hT V D' A' G' U' F q hq).2 S
  obtain ⟨σc, -, hu⟩ := (GlobalTheory.expandsG_bijective_of_dvr h₁ h₂ h₄ hT V D' A' G' U' F q hq).2 (c • S)
  have hsc := GlobalTheory.GroupExpansionLinear.expandsG_sum V D' A' G' U' F q 1 (fun _ => c) (fun _ => σb) (fun _ => S)
    (GlobalTheory.ExpansionLinear.secComb (fun _ : Fin 1 => scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left c)
      (fun _ => σb)) (fun _ => hσb) (fun _ => rfl)
  rw [Fin.sum_univ_one] at hsc
  have hσ' := (hu _ hE').trans (hu _ hsc).symm
  choose zi hz₀ hz₁ hz₂ using ha
  have hc : ∀ i, cpy F n d m i ≫ spMap (jetCoef (algebraMap V F) (Fin 1 × Fin d) m) = jcN V F d n m i := fun i => by
    rw [jcN]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have main := GlobalTheory.BoxSectionValues.main h₁ h₂ h₄ hT V n P.D D' P.A A' t.G G' pD pA pG U' P.U PU F q hq σ s σb S
    hσ hS hσb _ z (fun i => cpy F n d m i ≫ zi i)
    (fun i => by rw [hp, Category.assoc, hz₁, ← Category.assoc, hc, jptN])
    (fun i => by
      rw [h₀, Category.assoc, hz₀]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [AlgHom.comp_algebraMap])
  have core := (core_iff (pr := fun i => (pG.pr i).left) hM hM' PU.wL PU.wL_gen (τ₁ m) (g₁ m) (cpy V n d m)
      (zV_pr pG xT m) τ hτ hv (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m))
      (UnifPre.gFK (R := V) (G := G') F) z hzg q
      (genCast (congrArg RigLB.L P.bundle).symm _ _ (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
        LB.pullGen t.PP.L _ _ (genPowG t _ _ (eLG t (𝟙 (Sp V)) d xT act eT wPT m) q) (jcN V F d n m i)))
      (fun y J hJ => (val_cast_prod t _ _ _ _ _ q _ y J hJ).trans (Finset.prod_congr rfl fun i _ => by
        rw [coef_cpy]
        have := val_along hM _ _ _ _ (el m) (jcN V F d n m i) y J hJ
        rw [Category.comp_id] at this
        exact congrArg (· ^ q) this.symm)) σ' (toΓ _ (psJet m h))).1 ⟨a', b', k₂, (corr_genCast _ _ _).1 k₃, k₄⟩
  refine jetAt_smul U'.toUnifPre F m (zV pG xT m) τ q σb σ' c _ _ (fun jj => ?_) ⟨z, h₀, hzg, fun y J' hJ' => ?_⟩
    ⟨z, h₀, hzg, core⟩
  · have e : σ'.f jj = ∑ _i : Fin 1, resTop _ (scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left c) *
        σb.f jj := by rw [hσ']; rfl
    rwa [Fin.sum_univ_one] at e
  · obtain ⟨J, hJ⟩ := exists_good_at hM y
    have e₁ : (om PU.wL y J J' (z ≫ UnifPre.gFK (R := V) (G := G') F) ^ q).val * sval σb z y J' =
        ∏ i, sval (σ i) (cpy F n d m i ≫ zi i) y J := main y J J' hJ hJ'
    have e₂ : ∀ i, sval (σ i) (cpy F n d m i ≫ zi i) y J =
        gs (𝟙 _) y ⊤ (toΓ _ (jetCopy (S := F) d m i (a i))) *
          (val (τ₁ m) (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m) ≫ cpy V n d m i) y J ^ q).val := fun i => by
      rw [sval_along hM _ (zi i) _ _ (hz₁ i) q (σ i) (τ₁ m) _ (hz₂ i) (cpy F n d m i) y J hJ, hc, coef_cpy, gs_spMap]
      rfl
    have e₃ := hv _ (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m)) y J J' hJ hJ'
    rw [← hzg] at e₃
    rw [Finset.prod_congr rfl fun i _ => e₂ i, Finset.prod_mul_distrib, ← Units.coe_prod, Finset.prod_pow, ← e₃,
      mul_pow, Units.val_mul, mul_left_comm, ← gs_prod _ y ⊤ trivial, ← map_prod] at e₁
    exact (Units.mul_right_inj _).1 e₁

end Box

section Ord
open GlobalTheory.GermValuationJetHarmonics GlobalTheory.ChartPush

theorem jet_of_val {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
    {S : Type} [CommRing S] {x0 : Sp S ⟶ X} {d : ℕ}
    {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
    {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
    (hc : IsChartG t x0 d F act tg uvec x) {e : ∀ m, FrTyG t x0 d x m} {wP : PrimTyG t}
    (hg : ∀ m, (e m).IsGen) (hP : wP.IsGen) {k : ℕ} {s : LB.Sec (LPow t.G t.PP.L k (Over.mk x0))} (m : ℕ)
    {f : Jet S (Fin 1 × Fin d) m}
    (h : ∀ (z : (jOG x0 d m 1).left) (J), Good t.PP.L z J →
      sv t s ((ptSecT t.G (x m)).left ≫ (jBaseG x0 d m 1 ▷ t.G).left) z J =
        gs (𝟙 _) z ⊤ (toΓ _ f) * (val (eLG t x0 d x act e wP m) (𝟙 _) z J ^ k).val) :
    ∃ (F' : LB.Sec (LPow t.G t.PP.L k (jOG x0 d m 1)))
      (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 1) (fun _ => (x m).left) fun _ => (k : ℤ))),
      IsPullSec t.G t.PP.L k (jBaseG x0 d m 1 ▷ t.G) (whiskerRight_snd _ _) s F' ∧
      LB.Gen.Corr t.PP.L _ _ _ _ τ (genPowG t _ _ (eLG t x0 d x act e wP m) k) ∧
      IsValueAt t.G t.PP.L k F' (x m) τ (toΓ _ f) := by
  have heL : (eLG t x0 d x act e wP m).IsGen :=
    DVR.mulGen_isGen t.PP.L _ _ _ _ _ _ (DVR.pullGen_isGen t.PP.L _ _ _ hP _) (DVR.pullGen_isGen t.PP.L _ _ _ (hg m) _)
  obtain ⟨τ, -, hτ⟩ : ∃ τ : LB.Gen (LB.LinComb t.PP.L (Y := (jOG x0 d m 1).left) (K := Fin 1) (fun _ => (x m).left)
      fun _ => (k : ℤ)), τ.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG x0 d m 1).left) (z : Z)
        (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
          val τ r z J = val (genPowG t _ _ (eLG t x0 d x act e wP m) k) r z J := by
    refine exists_gen t.PP.isLB ?_ _ (GermD.genPowG_isGen t _ _ _ heL k)
    intro U _ hU
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, _root_.mul_one,
      GermD.formEq_eL hc m]
    rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
    simp only [← zpow_add, _root_.mul_neg, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]
  obtain ⟨s₁, hp⟩ := GermD.exists_pullSec t.G t.PP.L (k : ℤ) (jBaseG x0 d m 1 ▷ t.G) (whiskerRight_snd _ _) s
  refine ⟨s₁, τ, hp, corr_of_val t.PP.isLB fun y J hJ => hτ _ _ y J hJ, fun j => fn_ext fun y hy => ?_⟩
  obtain ⟨J, hJ, e₀⟩ := exists_good t.PP.L t.PP.isLB y (fun _ : Fin 1 => (x m).left) j
    (fun a b _ => congrArg j (Subsingleton.elim a b)) (fun k => Set.mem_iInter.1 hy k)
  have q : sv t s₁ (𝟙 _ ≫ (ptSecT t.G (x m)).left) y J = gs (𝟙 _) y ⊤ (toΓ _ f) * (val τ (𝟙 _) y J).val := by
    rw [sv_pullSec hp _ y hJ, Category.id_comp, h y J hJ, hτ _ _ y J hJ, GermD.val_genPowG]
  rw [val_of τ _ y J j (fun k => by rw [Category.id_comp]; exact e₀ k)] at q
  have q' := (sval_of (φ := fun _ : Fin 1 => (snd _ t.G).left) (ε := fun _ => (k : ℤ)) s₁
    (𝟙 _ ≫ (ptSecT t.G (x m)).left) y J j
    (fun k => by rw [Category.id_comp, ptSecT_snd]; exact e₀ k)).symm.trans q
  exact ((gs_res _ y _ hy _).trans (gs_pull _ (ptSecT t.G (x m)).left y _ (val_le t.G t.PP.L (x m) _ hy) _)).trans
    (q'.trans ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y le_top hy _) (gs_unit _ y _ hy _))).symm)

set_option maxHeartbeats 800000 in

theorem sv_of_tie_at {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
    {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G) (τ : Frames P.U.LG.L (κ := Fin 1 × Fin (chD C.ch)) C.xT)
    (hτ : IsEL P C.xT C.actT C.eT C.wPT τ) (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F]
    [IsScalarTower T.V T.Fr F] (xF : Sp F ⟶ Xo.X) (q : ℕ) (σ : P.U.toUnifPre.SecGF F q)
    (hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))) (m : ℕ) (f : Jet F (Fin 1 × Fin (chD C.ch)) m)
    (ht : SecTieF C.I P F xF q σ hh) (hf : JetAt P.U.toUnifPre m (C.xT m) (τ m) F q σ f)
    (a : jOG xF (chD C.ch) m 1 ⟶ Xo.univ.t.G)
    (ha : letI := io.toAlgebra; a.left = spMap (jetCoef (algebraMap T.Fr F) _ m) ≫ (C.ch.x m).left)
    (z : Sp (Jet F (Fin 1 × Fin (chD C.ch)) m)) (J) (hJ : Good Xo.univ.t.PP.L z J) :
    letI := io.toAlgebra
    sv Xo.univ.t hh ((ptSecT Xo.univ.t.G a).left ≫ (jBaseG xF (chD C.ch) m 1 ▷ Xo.univ.t.G).left) z J =
      gs (𝟙 _) z ⊤ (toΓ _ f) * (val (eL y.1 C.ch.d C.ch.x C.ch.B.A.act C.ch.e C.ch.wP m)
        (spMap (jetCoef (algebraMap T.Fr F) _ m)) z J ^ q).val := by
  letI := io.toAlgebra
  obtain ⟨p, p₀, p₁, p₂, hp⟩ := frames_tied C m (spMap (jetCoef (algebraMap T.Fr F) (Fin 1 × Fin (chD C.ch)) m))
  obtain ⟨zF, z₁, z₂, hz⟩ := hf
  have hLG : P.U.LG.L.IsLB := P.U.LG.isLB
  obtain ⟨J₂, hJ₂⟩ := DegPull.exists_good' hLG z
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' C.I.t'.PP.isLB z
  obtain ⟨J₃, hJ₃, hv, hw⟩ := exists_good_cast (L' := C.I.t'.PP.L) (Φ := C.I.m2.φ)
    (congrArg RigLB.L P.bundle).symm z J₂ hJ₂
  obtain ⟨A, k₁, k₂⟩ := hp z J J₃ J' hJ hJ₃ hJ'
  have ec : spMap (jetCoef (algebraMap T.Fr F) (Fin 1 × Fin (chD C.ch)) m) ≫
      spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin (chD C.ch)) m) =
      spMap (jetCoef (algebraMap T.V F) (Fin 1 × Fin (chD C.ch)) m) := by
    rw [spMap_spMap, jetCoef_comp, ← IsScalarTower.algebraMap_eq]
  rw [ec] at p₂ k₂
  obtain ⟨b₁, b₂⟩ := ptSec_base (t := Xo.univ.t) m a
  have key := ht.2 _ p zF _ (z₂.trans p₂.symm) (b₁.trans (ha.trans p₁.symm)) (z₁.trans b₂.symm) (by
      rw [← Category.assoc, p₀]
      refine (congrArg (· ≫ spMap (algebraMap T.Fr F)) b₂).trans ?_
      exact RawChartGermBC.spMap_comp_eq _ _ _ _
        (RingHom.ext fun s => (jetBC_algebraMap (algebraMap T.Fr F) _ m s).symm))
    z J J₂ (J' p) hJ hJ₂ (hJ' p)
  rw [hw] at key
  have k₃ := (val_corr hJ₂ (corr_of_val hLG (hτ m))
    (spMap (jetCoef (algebraMap T.V F) (Fin 1 × Fin (chD C.ch)) m))).trans ((hv _ _ _ _).trans k₂)
  exact alg_tie key (hz z J₂ hJ₂) k₁ k₃

set_option maxHeartbeats 800000 in

theorem harmonic_value_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (τ : Frames P.U.LG.L (κ := Fin 1 × Fin (chD C.ch)) C.xT), IsEL P C.xT C.actT C.eT C.wPT τ → ∀ (F : Type) [Field F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F], letI := io.toAlgebra; letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra; ∀ (φ : T.Fr →ₐ[c.F] F), φ.toRingHom = algebraMap T.Fr F → ∀ (yF : FrPt Xo c F), FrMap φ y.1 yF → ∀ (q n m : ℕ) (σ : Fin n → P.U.toUnifPre.SecGF F q) (hh : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo yF.x))) (f : Fin n → PS F 1 (chD C.ch)), (∀ i, SecTieF C.I P F yF.x q (σ i) (hh i)) → (∀ i, JetAt P.U.toUnifPre m (C.xT m) (τ m) F q (σ i) (psJet m (f i))) → ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → Pp.totalDegree ≤ m → ∑ m ∈ Pp.support, algebraMap c.F F (Pp.coeff m) * ∏ i, nab yF (q : ℤ) (hh i) (colOf m i) = nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 q (boxSer f) (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map (algebraMap c.F F) Pp) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C P τ hτ F _ _ _ _ _
  letI := io.toAlgebra
  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  intro φ hφ yF hy q n m σ hh f ht hf a Pp hP hdeg
  obtain ⟨x', e', h₁, h₂, h₃, h₄, h₅⟩ := exists_chart_baseChange φ hy C.ch
  rw [hφ] at h₁ h₂ h₃ h₄ h₅
  have hg := RawChartBaseChange.isCanonGauge_mapFB (algebraMap T.Fr F) C.ch.B C.ch.h C.ch.gauge
  let CF : ChartAt Xo c yF := ⟨C.ch.d, FBMap.mapFB (algebraMap T.Fr F) C.ch.B, fun ℓ j => algebraMap T.Fr F (C.ch.uvec ℓ j),
    x', e', C.ch.wP, MvPowerSeries.map (algebraMap T.Fr F) C.ch.h, h₁, h₂, C.ch.prim, hg, h₃⟩
  have hG : ∀ i, JetD yF CF.d CF.x CF.B.A.act CF.e CF.wP q (hh i) m (f i) := fun i =>
    jet_of_val ((isChart_iff yF _ _ _ _ _).1 h₁) h₂.gen C.ch.prim.1 m
      fun z J hJ => (sv_of_tie_at C P τ hτ F yF.x q (σ i) (hh i) m _ (ht i) (hf i) (x' m) (h₄ m) z J hJ).trans
        (congrArg (fun v => gs (𝟙 _) z ⊤ (toΓ _ (psJet m (f i))) * (v ^ q).val) (h₅ m z J hJ).symm)
  have h := GlobalTheory.OrderGerm.ord_holds E H Dw l Xo c nab hnab F yF CF q n m hh f hG a Pp hP
    (fun e he => (MvPolynomial.le_totalDegree he).trans hdeg)
  refine h.symm.trans ?_
  exact (nabValN_columns (algebraMap c.F F) C.ch.B _ (HarmCopies.const_eq_zero hg) q n f
    (fun ℓ j => algebraMap T.Fr F (C.ch.uvec ℓ j)) Pp).symm

end Ord

set_option maxHeartbeats 800000 in

theorem translate_eq_box : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (_PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → ∀ (θ₁ : Fam P.D.toPre F 1) (θα₁ : Fam P.D.toPre F (1 * N)), ThFrame P.D ϖ F θ₁ → PullAl P.D F P.oD α 1 N θ₁ θα₁ → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (q : ℕ) (e : 1 * N = q), w.IsGen → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → ∃ (u : F) (p₁ : Fin n → QkPt P.D.toPre F (1 * N)) (w₁ : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p₁ i).g.b) (DegPre.lineε (1 * N)))) (ζ₁ : Fin n → F) (r₀ r : Fin n → Fam P.D.toPre F (1 * N)) (σ₁ : Fin n → P.U.toUnifPre.SecGF F q) (S : Fam D'.toPre F q), v u = 0 ∧ IsBoxFam pD F q S (fun i => PowGerm.famCast (Dp := P.D.toPre) (F := F) e (r i)) ∧ PowGerm.famCast (Dp := D'.toPre) (F := F) e t = u • S ∧ ∀ i, (w₁ i).IsGen ∧ FinOrd P.D F (1 * N) (p₁ i) (w₁ i) (ζ₁ i) ∧ P.ToA F (1 * N) (p₁ i) (x ≫ pA.pr i) ∧ PhiRel P.D.toPre F (1 * N) (p₁ i) (w₁ i) θα₁ (r₀ i) ∧ Fam.IsSmul P.D.toPre F (ζ₁ i) (r₀ i) (r i) ∧ P.U.toUnifPre.ExpandsG F q (σ₁ i) (PowGerm.famCast (Dp := P.D.toPre) (F := F) e (r i)) := by
  obtain ⟨hL, hL2, -, hL4, -⟩ := GlobalTheory.firstFiveLaws
  have hT := GlobalTheory.twistBaseChange_and_valuation_statements.1
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P hTor ϖ hϖ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG U' PU _ oD' hx hact
    α N hN hα θ₁ θα₁ hθ₁ hθα₁ θ θα hθ hθα p w ζ x t₀ t q e hw hfin hpx hΦt hsm
  subst e
  have hG := hL.globalFns
  have hk : 1 ≤ 1 * N := by omega
  haveI : CharZero T.V := (algebraMap T.V F).charZero
  obtain ⟨p₁, hp, hp₁⟩ := UnboxQk.exists_isBoxQk_toA hL hL2 hL4 hT T.V E H C.I.G P hTor n D' A' G' pD pA pG U' PU F
    (1 * N) hk p
  have hw₁ : ∀ i, ∃ w₁ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p₁ i).g.b)
      (DegPre.lineε (1 * N))), w₁.IsGen := fun i =>
    H1.ClosedPointWeilPower.gen_local_linComb P.D.toPre.P.L P.D.toPre.P.isLB _ _
  choose w₁ hw₁ using hw₁
  choose ζ₁ _ hζ₁ using fun i => H1.finOrdExists_of (phiFun_of hL) (H1.phiPow_of hL) T.V P.D F (1 * N) hk (p₁ i) (w₁ i)
    (hw₁ i)
  choose Φ₁ hΦ₁ using fun i => phiFun_of hL T.V _ P.D F (1 * N) hk (p₁ i) (w₁ i) (hw₁ i)
  choose σ₁ hσ₁ using fun i => ((GlobalTheory.expandsG_bijective_of_dvr hL hL2 hL4 hT T.V P.D P.A C.I.G.G P.U F (1 * N) hk).2
    (ζ₁ i • Φ₁ i θα₁)).exists
  obtain ⟨bx₁, hbx₁⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F 1
  obtain ⟨bx, hbx⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F (1 * N)
  obtain ⟨u₀, hu₀, hθu⟩ := GlobalTheory.T.thetaFrameFamilies_differ_by_valuationZero_unit T.V ϖ hϖ D' F v hv _ θ
    (BoxFrame.main T.V ϖ hϖ n P.D D' pD F θ₁ _ hθ₁ ((hbx₁ _ _).2 rfl)) hθ
  have hw0 : TraceFormTwistIso D'.toPre oD' H.w0 := GlobalTheory.PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E)
    (fun a x => funext fun i => hx a x i) P.oD oD' hact H.w0 P.w0
  obtain ⟨pl, -, hpl⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 α N 1 hN le_rfl hα
  have hpull := BoxPull.main hL hL2 hL4 hT T.V n P.D D' pD F (𝓞 E) hx P.oD oD' hact α N 1 hN le_rfl hα
    (fun _ => θ₁) (fun _ => θα₁) _ _ (fun _ => hθα₁) ((hbx₁ _ _).2 rfl) ((hbx _ _).2 rfl)
  have hθα' : θα = u₀ • bx fun _ => θα₁ := by
    rw [(hpl _ _).1 hθα, (hpl _ _).1 hpull, (isSmul_iff _ _ _).1 hθu, map_smul]
  obtain ⟨w', hw', hΦ⟩ := BoxPhi.phiRel_box hG T.V n P.D.toPre D'.toPre pD F (1 * N) p p₁ hp w₁ hw₁
  have hfin' := finOrd_box hL hL2 hL4 hT T.V n P.D D' pD F (1 * N) hk p p₁ hp w₁ w' hw₁ hw' hΦ ζ₁ hζ₁
  obtain ⟨u₁, ⟨m, hm, hum⟩, hu₁⟩ := GlobalTheory.T.finiteOrder_thetaOperators_ratio_rootOfUnity T.V ϖ hϖ D' F (1 * N) hk p w' w (∏ i, ζ₁ i) ζ hw' hw hfin' hfin
  obtain ⟨Φ', hΦ'⟩ := phiFun_of hL T.V _ D' F (1 * N) hk p w' hw'
  have hbΦ : bx (fun i => Φ₁ i θα₁) = Φ' (bx fun _ => θα₁) :=
    (hΦ' _ _).1 (hΦ _ _ _ _ (fun i => (hΦ₁ i _ _).2 rfl) ((hbx _ _).2 rfl) ((hbx _ _).2 rfl))
  have ht : t = (u₁ * u₀) • bx fun i => ζ₁ i • Φ₁ i θα₁ := by
    rw [(isSmul_iff _ _ _).1 (hu₁ θα _ _ t₀ t ((hΦ' _ _).2 rfl) ((isSmul_iff _ _ _).2 rfl) hΦt hsm), hθα', map_smul,
      MultilinearMap.map_smul_univ, hbΦ, smul_comm (∏ i, ζ₁ i) u₀, smul_smul]
  refine ⟨u₁ * u₀, p₁, w₁, ζ₁, fun i => Φ₁ i θα₁, fun i => ζ₁ i • Φ₁ i θα₁, σ₁, _, ?_, (hbx _ _).2 rfl, ht,
    fun i => ⟨hw₁ i, hζ₁ i, hp₁ x hpx i, (hΦ₁ i _ _).2 rfl, (isSmul_iff _ _ _).2 rfl, hσ₁ i⟩⟩
  rw [AddValuation.map_mul, hu₀, ColumnSplit.val_eq_zero_of_pow_eq_one v hm hum, add_zero]

theorem val_prod_eq_zero {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {K : Type} (s : Finset K) (u : K → F)
    (hu : ∀ i, v (u i) = 0) : v (∏ i ∈ s, u i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, v.map_mul, hu, ih, add_zero]

end GlobalTheory.OneOrder
