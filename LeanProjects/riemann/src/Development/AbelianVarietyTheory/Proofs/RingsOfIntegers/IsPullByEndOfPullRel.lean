import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NuChain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NuChainPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtDone
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Imports
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PullbackValuationNormPel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntOfVgeZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescrip
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PremisesMetRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.PullbackSections IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndPullNu

section Classes

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.ZH.CubeRootAut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

theorem act_zero (t : SAB H S) : t.act.act 0 = 1 := by
  have h := t.act.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem act_natCast (t : SAB H S) (n : ℕ) : t.act.act n = mulA t.G n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero]; exact (pow_zero _).symm
  | succ n ih => rw [Nat.cast_succ, t.act.add, ih, t.act.one]; exact (pow_succ _ _).symm

theorem act_eq_one_of_gen (t : SAB H S) (hK : KTriv t.G t.PP.L) (π : 𝓞 E) (a b : ℕ)
    (α₀ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![𝟙 t.G.left, (t.act.act π).left] ![(a : ℤ), -(b : ℤ)]))
    (hα : α₀.IsGen) : t.act.act ((a : 𝓞 E) - b * (π * H.bar π)) = 1 := by
  have hL := t.PP.isLB
  have := t.act.hom
  set c := cls t.PP.L hL with hc
  have q1 : ∀ T : Over S, pull (1 : T ⟶ t.G).left c = 0 := fun T => by
    have e : pull (η[t.G]).left c = 0 := (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨t.PP.rig, t.PP.rigGen⟩
    rw [Hom.one_def, Over.comp_left, pull_comp, e, map_zero]
  have cube : ∀ {T : Over S} (x y z : T ⟶ t.G), cubeCls ![x, y, z] c = 0 := fun x y z => by
    have h : cubeCls (x3 t.G) c = 0 := (cls_cubeLB _ hL).symm.trans ((cls_eq_zero_iff _).2 ⟨t.cub.t, t.cub.isGen⟩)
    rw [pull_cubeCls (lift x (lift y z)) (x3 t.G) _ _ (fun i => by fin_cases i <;> simp [x3]), h, map_zero]
  let B : ∀ {T : Over S}, (T ⟶ t.G) → (T ⟶ t.G) → CechPic.Pic T.left := fun x y =>
    pull (x * y).left c - pull x.left c - pull y.left c
  have Badd : ∀ {T : Over S} (x y z : T ⟶ t.G), B x (y * z) = B x y + B x z := fun x y z => by
    have h := cube x y z
    rw [cubeCls_triple, q1, _root_.mul_assoc] at h
    simp only [B]
    rw [← sub_eq_zero, ← h]
    abel
  have Bpow : ∀ {T : Over S} (x y : T ⟶ t.G) (n : ℕ), B x (y ^ n) = n • B x y := fun x y n => by
    induction n with
    | zero => simp only [B, pow_zero, _root_.mul_one, q1, zero_smul]; abel
    | succ n ih => rw [pow_succ, Badd, ih, succ_nsmul]
  have Badj : ∀ {T : Over S} (x y : T ⟶ t.G), B (x ≫ t.act.act π) y = B x (y ≫ t.act.act (H.bar π)) := fun x y => by
    have h := (cls_cubeLB _ hL).symm.trans (((cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2
      (t.adj π)).trans (cls_cubeLB _ hL))
    have h₁ := pull_cubeCls (lift x y) ![fst t.G t.G ≫ t.act.act π, snd t.G t.G] c ![x ≫ t.act.act π, y]
      (fun i => by fin_cases i <;> simp)
    have h₂ := pull_cubeCls (lift x y) ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar π)] c
      ![x, y ≫ t.act.act (H.bar π)] (fun i => by fin_cases i <;> simp)
    rw [h, ← h₂, cubeCls_pair, cubeCls_pair, q1, add_zero, add_zero] at h₁
    exact h₁
  have hab : ∀ {T : Over S} (x : T ⟶ t.G), a • pull x.left c = b • pull (x ≫ t.act.act π).left c := fun x => by
    have h := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨α₀, hα⟩
    rw [cls_linComb hL, Fin.sum_univ_two] at h
    have h' := congrArg (pull x.left) h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_zsmul, map_zero, ← pull_comp, Category.comp_id,
      ← Over.comp_left, neg_smul, natCast_zsmul, map_neg, map_nsmul] at h'
    exact add_neg_eq_zero.1 h'
  have Bab : ∀ {T : Over S} (x y : T ⟶ t.G), a • B x y = b • B (x ≫ t.act.act π) (y ≫ t.act.act π) := fun x y => by
    simp only [B, smul_sub, hab, MonObj.mul_comp]
  set d : 𝓞 E := (a : 𝓞 E) - b * (π * H.bar π) with hd
  have key : ∀ {T : Over S} (x y : T ⟶ t.G), B x (y ≫ t.act.act d) = 0 := fun x y => by
    have e : (y ≫ t.act.act d) * ((y ≫ t.act.act π) ≫ t.act.act (H.bar π)) ^ b = y ^ a := by
      have e₁ : ∀ {T : Over S} (z : T ⟶ t.G) (n : ℕ), z ^ n = z ≫ t.act.act n := fun z n => by
        rw [act_natCast, MonObj.comp_pow, Category.comp_id]
      rw [e₁, e₁ y, Category.assoc, Category.assoc, ← t.act.mul, ← t.act.mul, ← MonObj.comp_mul, ← t.act.add]
      congr 2
      rw [hd]; ring
    have h := Badd x (y ≫ t.act.act d) (((y ≫ t.act.act π) ≫ t.act.act (H.bar π)) ^ b)
    rw [e, Bpow, Bpow, Bab, Badj] at h
    exact left_eq_add.1 (h.trans (add_comm _ _))
  refine GlobalTheory.PowBalanceProbe.eq_one_of_cls hL hK (t.act.act d) (pull (t.act.act d).left c) ?_
  have h := key (snd t.G t.G) (fst t.G t.G)
  simp only [B] at h
  rw [← pull_comp, ← Over.comp_left, _root_.mul_comm, ← sub_eq_zero]
  exact h

end Classes

section Comparison₂

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

def PullRel {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (f : G ⟶ G) (a b : ℕ)
    (s : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => pullback.fst G.hom (Out.jK V)) (fun _ => (b : ℤ))))
    (s' : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => pullback.fst G.hom (Out.jK V)) (fun _ => (a : ℤ)))) : Prop :=
  ∃ u : LB.Gen (LB.LinComb L.L (K := Fin 2) ![gK, endK f ≫ gK] ![(a : ℤ), -(b : ℤ)]), u.IsGen ∧
    (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (FractionRing V)) (z : Z) (J), Good L.L z J → val u (r ≫ unitK) z J =
      val (L := L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) L.rig (r ≫ Out.jK V) z J ^ ((a : ℤ) - b)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G.hom (Out.jK V)) (z : Z) (J), Good L.L z J →
      sval s' r z J = sval s (r ≫ endK f) z J * (val u r z J).val

theorem pullRel_cast {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] {L₁ L₂ : RigLB G} (e : L₁ = L₂) (f : G ⟶ G)
    (a b : ℕ)
    (s : LB.Sec (LB.LinComb L₁.L (K := Fin 1) (fun _ => pullback.fst G.hom (Out.jK V)) (fun _ => (b : ℤ))))
    (s' : LB.Sec (LB.LinComb L₂.L (K := Fin 1) (fun _ => pullback.fst G.hom (Out.jK V)) (fun _ => (a : ℤ))))
    (h : PullRel L₂ f a b (e ▸ s) s') :
    ∃ s'' : LB.Sec (LB.LinComb L₁.L (K := Fin 1) (fun _ => pullback.fst G.hom (Out.jK V)) (fun _ => (a : ℤ))),
      e ▸ s'' = s' ∧ PullRel L₁ f a b s s'' := by
  subst e
  exact ⟨s', rfl, h⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V))

omit [IsDiscreteValuationRing V] in
theorem iotaK_fst : iotaK m ≫ pullback.fst t.G.hom (Out.jK V) = m.φ := pullback.lift_fst _ _ _

omit [IsDiscreteValuationRing V] in
theorem iotaK_snd : iotaK m ≫ pullback.snd t.G.hom (Out.jK V) = tK.G.hom := pullback.lift_snd _ _ _

omit [IsDiscreteValuationRing V] in
theorem isIso_iotaK : IsIso (iotaK m) := by
  have e : iotaK m = m.cart.1.isoPullback.hom := pullback.hom_ext
    ((iotaK_fst m).trans m.cart.1.isoPullback_hom_fst.symm) ((iotaK_snd m).trans m.cart.1.isoPullback_hom_snd.symm)
  rw [e]
  infer_instance

theorem iotaK_endK (π : 𝓞 E) : iotaK m ≫ endK (t.act.act π) = (tK.act.act π).left ≫ iotaK m := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, iotaK_fst, m.act, endK, pullback.lift_fst, ← Category.assoc, iotaK_fst]
  · rw [Category.assoc, Category.assoc, iotaK_snd, Over.w, endK, pullback.lift_snd, ← Category.assoc, iotaK_snd,
      Category.comp_id]

omit [IsDiscreteValuationRing V] in
theorem eSec_comm : eSec tK.G ≫ m.φ = Out.jK V ≫ eSec t.G :=
  m.cm.e_comm.trans (congrArg (· ≫ eSec t.G) m.base)

theorem eSec_iotaK : eSec tK.G ≫ iotaK m = unitK := by
  apply pullback.hom_ext
  · rw [Category.assoc, iotaK_fst, unitK, pullback.lift_fst]
    exact eSec_comm m
  · rw [Category.assoc, iotaK_snd, unitK, pullback.lift_snd]
    exact Over.w η[tK.G]

theorem exists_pullRel_tie (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (hw : RigIso m w)
    (P : PELUnif (maximalIdeal V) t) (π : 𝓞 E) (a b : ℕ)
    (F₁ : LB.Sec (LPow tK.G tK.PP.L (b : ℤ) (𝟙_ (Over (Sp (FractionRing V))))))
    (h₁ : LB.Sec (LPow tK.G tK.PP.L (a : ℤ) (𝟙_ (Over (Sp (FractionRing V))))))
    (α₀ : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![𝟙 tK.G.left, (tK.act.act π).left] ![(a : ℤ), -(b : ℤ)]))
    (α : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![(snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left,
      (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ≫ tK.act.act π).left] ![(a : ℤ), -(b : ℤ)]))
    (hα : α₀.IsGen) (hn : IsNormEnd tK.G tK.PP (tK.act.act π) a b α₀)
    (hc : LB.Gen.Corr tK.PP.L _ _ _ _ α
      (LB.pullGen tK.PP.L _ _ α₀ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left))
    (htw : IsTwistPull tK.G tK.PP.L (endT tK.G (𝟙_ (Over (Sp (FractionRing V)))) (tK.act.act π))
      (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G ≫ tK.act.act π) (lift_snd _ _) a b α F₁ h₁)
    (s : P.U.SecK b) (hs : SecTieGK m w P b F₁ s) :
    ∃ s' : P.U.SecK a, SecTieGK m w P a h₁ s' ∧ PullRel P.U.LG (t.act.act π) a b s s' := by
  have hL := t.PP.isLB
  have hL' := tK.PP.isLB
  have := isIso_iotaK m
  have := tK.act.hom π
  obtain ⟨t₀, ht₀, hv₀⟩ := exists_up ((isGen_iff w).1 hw.1) hL hL' α₀ hα
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (z : Z) J J', Good t.PP.L z J → Good tK.PP.L z J' →
      val t₀ r z J = gw w r z (J (r ≫ m.φ)) (J' r) ^ (a : ℤ) *
        gw w (r ≫ (tK.act.act π).left) z (J ((r ≫ (tK.act.act π).left) ≫ m.φ)) (J' (r ≫ (tK.act.act π).left)) ^ (-(b : ℤ)) *
        val α₀ r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv₀ Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) ?_ rfl)
    rw [pw, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, Category.id_comp, Category.assoc]
  have i₁ : inv (iotaK m) ≫ m.φ = gK := by rw [← iotaK_fst, IsIso.inv_hom_id_assoc]
  have i₂ : inv (iotaK m) ≫ (tK.act.act π).left ≫ m.φ = endK (t.act.act π) ≫ gK := by
    rw [← iotaK_fst, ← Category.assoc _ (iotaK m), ← iotaK_endK, Category.assoc, IsIso.inv_hom_id_assoc]
  obtain ⟨u, hu, huv⟩ := exists_gen hL (φ' := ![gK, endK (t.act.act π) ≫ gK]) (ε' := ![(a : ℤ), -(b : ℤ)])
    (fun W _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp, i₁, i₂])
    (LB.pullGen t.PP.L _ _ t₀ (inv (iotaK m))) (pullGen_isGen _ _ _ _ ht₀ _)
  obtain ⟨s₂, hs₂⟩ := exists_sec hL (φ' := fun _ : Fin 1 => gK) (ε' := fun _ => (a : ℤ))
    (fun W _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
    (pullMulSec (secU P s) (endK (t.act.act π)) u hu)
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback t.G.hom (Out.jK V)) (z : Z) (J), Good t.PP.L z J →
      sval s₂ r z J = sval (secU P s) (r ≫ endK (t.act.act π)) z J * (val u r z J).val := fun Z r z J hJ => by
    rw [hs₂ _ _ z J hJ, sval_pullMulSec _ _ _ _ _ z hJ]
  have uι : ∀ (Z : Scheme.{0}) (r : Z ⟶ tK.G.left) (z : Z) (J), Good t.PP.L z J →
      val u (r ≫ iotaK m) z J = val t₀ r z J := fun Z r z J hJ => by
    rw [huv _ _ z J hJ, val_pull hJ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hrel : PullRel t.PP (t.act.act π) a b (secU P s) s₂ := by
    refine ⟨u, hu, fun Z r z J hJ => ?_, key⟩
    choose J' hJ' using fun χ : Z ⟶ tK.G.left => exists_chart hL' (χ z)
    have hJ'' : Good tK.PP.L z J' := hJ'
    have e : (r ≫ eSec tK.G) ≫ (tK.act.act π).left = r ≫ eSec tK.G :=
      (Category.assoc _ _ _).trans (congrArg (fun x : 𝟙_ (Over (Sp (FractionRing V))) ⟶ tK.G => r ≫ x.left)
        (IsMonHom.one_hom (tK.act.act π)))
    have rp : ∀ k : ℤ, val (rigPow tK.G tK.PP.L tK.PP.rig k) r z J' =
        val (L := tK.PP.L) (φ := fun _ : PUnit => eSec tK.G) (ε := fun _ => 1) tK.PP.rig r z J' ^ k :=
      fun k => map_zpow _ _ _
    have b₁ := (val_pull hJ'' _ _ _).symm.trans ((val_corr hJ'' hn r).trans ((val_mul hJ'' _ _ _).trans
      (congrArg₂ (· * ·) (rp _) (rp _))))
    have hm := (maps_iff w _ (fun _ => eSec t.G) _ tK.PP.rig t.PP.rig m.cm.e _
      (rigPull_le m.cm.F m.cm.e m.cm.e_comm t.PP.L) (fun _ => rfl)).1 hw.2 Z r z
      (fun _ => J ((r ≫ eSec tK.G) ≫ m.φ)) (fun _ => J' (r ≫ eSec tK.G)) (fun _ => hJ _) (fun _ => hJ' _)
    rw [Fintype.prod_unique, zpow_one, m.base] at hm
    have b₂ : val (L := t.PP.L) (φ := fun _ : PUnit => eSec t.G) (ε := fun _ => 1) t.PP.rig (r ≫ Out.jK V) z J =
        gw w (r ≫ eSec tK.G) z (J ((r ≫ eSec tK.G) ≫ m.φ)) (J' (r ≫ eSec tK.G)) *
        val (L := tK.PP.L) (φ := fun _ : PUnit => eSec tK.G) (ε := fun _ => 1) tK.PP.rig r z J' := by
      refine (val_of _ _ z J _ fun _ => congrArg J ?_).trans hm
      rw [Category.assoc, Category.assoc]
      exact congrArg (r ≫ ·) (eSec_comm m).symm
    rw [← eSec_iotaK m, ← Category.assoc, uι _ _ z J hJ, hv _ _ z J J' hJ hJ'', e, b₁, b₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    module
  obtain ⟨s', es, hs'⟩ := pullRel_cast P.bundle (t.act.act π) a b s s₂ hrel
  refine ⟨s', fun Z r zp hzp z J J' hJ hJ' => ?_, hs'⟩
  have e₀ : secU P s' = s₂ := es
  have e₁ := hs Z (r ≫ (tK.act.act π).left) (zp ≫ (endT tK.G (𝟙_ (Over (Sp (FractionRing V)))) (tK.act.act π)).left)
    (by rw [Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, ← Category.assoc, hzp]) z J J' hJ hJ'
  have e₂ := twist_val htw zp z hJ'
  rw [val_corr hJ' hc, val_pull hJ', hzp] at e₂
  rw [e₀, key _ _ z J hJ, uι _ _ z J hJ, hv _ _ z J J' hJ hJ', Category.assoc, iotaK_endK, ← Category.assoc, e₁]
  refine Eq.trans ?_ (congrArg (_ * ·) e₂).symm
  rw [Category.comp_id, Category.comp_id, zpow_neg, zpow_natCast, zpow_natCast]
  show (gw w _ z _ _).val ^ b * _ * _ = (gw w _ z _ _).val ^ a * _
  rw [Units.val_mul, Units.val_mul, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
  set x := gw w (r ≫ (tK.act.act π).left) z (J ((r ≫ (tK.act.act π).left) ≫ m.φ)) (J' (r ≫ (tK.act.act π).left)) ^ b
  have hx := x.mul_inv
  linear_combination (exp := 1) ((gw w r z (J (r ≫ m.φ)) (J' r) ^ a).val * (val α₀ r z J').val *
    sval (L := tK.PP.L) (φ := fun _ : Fin 1 => (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left) (ε := fun _ => (b : ℤ)) F₁
      (zp ≫ (endT tK.G (𝟙_ (Over (Sp (FractionRing V)))) (tK.act.act π)).left) z J') * hx

end Comparison₂

section Dichotomy

open GlobalTheory.CechPic

theorem natCast_dvd_of_dvd {E : Type} [Field E] [NumberField E] {a b : ℕ} (h : (b : 𝓞 E) ∣ (a : 𝓞 E)) : b ∣ a := by
  have h₁ : (a : ℤ) ∈ ((Ideal.span {(b : ℤ)}).map (algebraMap ℤ (𝓞 E))).comap (algebraMap ℤ (𝓞 E)) := by
    rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    simpa using h
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat, Ideal.mem_span_singleton] at h₁
  exact_mod_cast h₁

theorem trivial_of_mulA {K : Type} [Field K] [CharZero K] (A : PolAV (Sp K)) {M : ℕ} (hM : 1 ≤ M)
    (h : mulA A.A M = 1) : 𝟙 A.A = 1 ∧ A.g = 0 := by
  have hN := GlobalTheory.abelianSchemeLaws_all.1.mulN
  obtain ⟨_, _, _, -, -⟩ := hN _ A M hM
  have := Flat.epi_of_flat_of_surjective (mulA A.A M).left
  have h1 : 𝟙 A.A = 1 := by
    apply Over.OverMorphism.ext
    rw [← cancel_epi (mulA A.A M).left, ← Over.comp_left, ← Over.comp_left, Category.comp_id, MonObj.comp_one, h]
  refine ⟨h1, ?_⟩
  obtain ⟨-, -, -, -, hc⟩ := hN _ A 2 (by norm_num)
  have hc' := hc (AlgebraicClosure K) (spMap (algebraMap K (AlgebraicClosure K))) (by norm_num)
  have hx : ∀ x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ A.A, x = 1 := fun x => by
    rw [← Category.comp_id x, h1, MonObj.comp_one]
  have : Unique {x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ A.A // x ^ 2 = 1} :=
    ⟨⟨⟨1, one_pow _⟩⟩, fun x => Subtype.ext (hx _)⟩
  rw [Nat.card_unique] at hc'
  have := (Nat.pow_eq_one.1 hc'.symm).resolve_left (by norm_num)
  omega

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {t : SAB H (Sp V)} {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V))

theorem exists_iso_kTriv (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (hw : w.IsGen) (P : PELUnif (maximalIdeal V) t) :
    (∃ e : tK.G ≅ P.A.A, IsMonHom e.hom) ∧ KTriv tK.G tK.PP.L := by
  obtain ⟨e₀, he₀, hφ⟩ := grpPullback_iso m.cart (isGrpPullback_pullback t.G (Out.jK V))
  have := P.U.gen_hom
  have he : IsMonHom (e₀ ≪≫ P.U.gen).hom := by
    rw [Iso.trans_hom]
    infer_instance
  refine ⟨⟨e₀ ≪≫ P.U.gen, he⟩, ?_⟩
  have c₁ : ∀ L₁ L₂ : RigLB t.G, L₁ = L₂ → cls L₁.L L₁.isLB = cls L₂.L L₂.isLB := by
    rintro _ _ rfl
    rfl
  have c₂ := (cls_eq_iff (pull_isLB P.A.isLB _) (pull_isLB P.U.LG.isLB _)).2 P.U.ext
  rw [cls_pull P.A.isLB, cls_pull P.U.LG.isLB, c₁ _ _ P.bundle] at c₂
  have c₃ := (cls_eq_iff tK.PP.isLB (pull_isLB t.PP.isLB _)).2 ⟨w, hw⟩
  rw [cls_pull t.PP.isLB] at c₃
  obtain ⟨v, hv⟩ := (cls_eq_iff tK.PP.isLB (pull_isLB P.A.isLB (e₀ ≪≫ P.U.gen).hom.left)).1 (by
    rw [cls_pull P.A.isLB, Iso.trans_hom, Over.comp_left, pull_comp, c₂, c₃]
    exact (congrArg (fun q => pull q _) hφ.symm).trans (pull_comp _ _ _))
  exact kTriv_pull (isGrpPullback_of_iso (e₀ ≪≫ P.U.gen)) P.A.isLB tK.PP.isLB ((isGen_iff v).1 hv) P.A.ktriv

theorem norm_or_trivial [CharZero V] (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (hw : w.IsGen)
    (P : PELUnif (maximalIdeal V) t) (π : 𝓞 E) (a b : ℕ) (ha : 0 < a)
    (α₀ : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![𝟙 tK.G.left, (tK.act.act π).left] ![(a : ℤ), -(b : ℤ)]))
    (hα : α₀.IsGen) :
    (∃ N : ℕ, 0 < N ∧ 0 < b ∧ π * H.bar π = N ∧ a = b * N) ∨
      (t.G.hom ≫ eSec t.G = 𝟙 _ ∧ Subsingleton P.D.toPre.X) := by
  obtain ⟨⟨e, he⟩, hK⟩ := exists_iso_kTriv m w hw P
  have h := act_eq_one_of_gen tK hK π a b α₀ hα
  by_cases hd : (a : 𝓞 E) - b * (π * H.bar π) = 0
  · left
    have hd' := sub_eq_zero.1 hd
    obtain ⟨N, rfl⟩ := natCast_dvd_of_dvd (E := E) ⟨_, hd'⟩
    have hb : 0 < b := Nat.pos_of_mul_pos_right ha
    refine ⟨N, Nat.pos_of_mul_pos_left ha, hb, ?_, rfl⟩
    rw [Nat.cast_mul] at hd'
    exact (mul_left_cancel₀ (Nat.cast_ne_zero.2 hb.ne') hd').symm
  right
  set d : 𝓞 E := (a : 𝓞 E) - b * (π * H.bar π)
  have hM : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd
  obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton.1 (Ideal.absNorm_mem (Ideal.span {d}))
  have := tK.act.hom d'
  have h₁ : mulA tK.G (Ideal.absNorm (Ideal.span {d})) = 1 := by
    rw [← act_natCast, hd', tK.act.mul, h, MonObj.one_comp]
  have h₂ : mulA P.A.A (Ideal.absNorm (Ideal.span {d})) = 1 := by
    rw [← cancel_epi e.hom, MonObj.comp_one, mulA, MonObj.comp_pow, Category.comp_id, ← Category.id_comp e.hom,
      ← MonObj.pow_comp]
    exact (congrArg (· ≫ e.hom) h₁).trans (MonObj.one_comp _)
  have : CharZero (FractionRing V) := IsFractionRing.charZero_of_isFractionRing V
  obtain ⟨h₃, hg⟩ := trivial_of_mulA P.A (Nat.one_le_iff_ne_zero.2 hM) h₂
  have h₄ : 𝟙 tK.G = 1 := by
    rw [← cancel_mono e.hom, Category.id_comp, MonObj.one_comp, ← Category.comp_id e.hom, h₃, MonObj.comp_one]
  constructor
  · have := t.semi.smooth
    have := t.semi.separated
    have : IsDominant (Out.jK V) := isDominant_jK
    have := IsSchemeTheoreticallyDominant.of_isDominant (Out.jK V)
    have : IsSchemeTheoreticallyDominant m.φ := IsSchemeTheoreticallyDominant.of_isPullback m.cart.1.flip
    have e₀ : eSec t.G ≫ t.G.hom = 𝟙 _ := Over.w η[t.G]
    refine ext_of_schDom t.G.hom (by rw [Category.assoc, e₀, Category.id_comp]; exact Category.comp_id _) m.φ ?_
    have e₁ : tK.G.hom ≫ eSec tK.G = 𝟙 tK.G.left := by
      have := congrArg (fun q => q.left) h₄
      rw [Hom.one_def] at this
      exact this.symm
    have e₂ : Out.jK V ≫ eSec t.G = eSec tK.G ≫ m.φ := (eSec_comm m).symm
    rw [Category.comp_id, ← Category.assoc, m.cart.1.w, Category.assoc]
    exact (congrArg (tK.G.hom ≫ ·) e₂).trans (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ m.φ) e₁)).trans
      (Category.id_comp _))
  · have := H1.dimSplit E H V t P
    exact (Module.finrank_eq_zero_iff_of_free ℤ _).1 (by omega)

end Dichotomy

section Main

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem isPullByEnd_of_pullRel {D : DegData V (maximalIdeal V)} {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)}
    [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (f : G ⟶ G) (b N : ℕ) (hN : 0 < N) (s : U.SecK b)
    (s' : U.SecK (b * N)) (h : PullRel U.LG f (b * N) b s s') : IsPullByEnd U f b N s s' := by
  obtain ⟨u, hu, hn, hs⟩ := h
  have hL := U.LG.isLB
  refine ⟨u, hu, corr_of_val hL fun z J hJ => ?_, (secRel_iff hL _ _ _ _ _ _ _ _ _ _).2 fun y J hJ => hs _ _ y J hJ⟩
  rw [val_pull hJ, val_pull hJ, val_pow, hn _ _ z J hJ, ← zpow_natCast]
  congr 1
  obtain ⟨N, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  push_cast
  ring

theorem regular_of_pullRel {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (hG : G.hom ≫ eSec G = 𝟙 _) (L : RigLB G)
    (f : G ⟶ G) (a b : ℕ)
    (s : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => pullback.fst G.hom (Out.jK V)) (fun _ => (b : ℤ))))
    (s' : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => pullback.fst G.hom (Out.jK V)) (fun _ => (a : ℤ))))
    (h : PullRel L f a b s s') (σ : H0 L.L b)
    (hσ : GeneratorPullback.SecScal L.L (fun _ : Fin 1 => pullback.fst G.hom (Out.jK V)) (fun _ => (b : ℤ)) s
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (b : ℤ)) σ (pullback.fst G.hom (Out.jK V)) 1) :
    ∃ σ' : H0 L.L a, GeneratorPullback.SecScal L.L (fun _ : Fin 1 => pullback.fst G.hom (Out.jK V)) (fun _ => (a : ℤ)) s'
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (a : ℤ)) σ' (pullback.fst G.hom (Out.jK V)) 1 := by
  obtain ⟨u, hu, hn, hs⟩ := h
  have hL := L.isLB
  have hr : (rigPow G L.L L.rig ((a : ℤ) - b)).IsGen := isGen_of_gm _ fun y j j' hj hj' => by
    have e := gen_trans (L := L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) L.rigGen (𝟙 _) y hj hj'
    refine (map_zpow _ _ _).trans ((congrArg (· ^ ((a : ℤ) - b)) e).trans ((mul_zpow _ _ _).trans
      (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)))
    rw [trF, trF, Fintype.prod_unique, Fintype.prod_unique, zpow_one]
  obtain ⟨σ', hσ'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => 𝟙 G.left) (ε' := fun _ => (a : ℤ))
    (fun W _ h => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Category.comp_id]
      refine (congrArg (fun q => _ * h q ^ ((a : ℤ) - b)) hG).trans ?_
      rw [← zpow_add, add_sub_cancel])
    (pullMulSec σ (𝟙 G.left) (LB.pullGen L.L _ _ (rigPow G L.L L.rig ((a : ℤ) - b)) G.hom)
      (pullGen_isGen _ _ _ _ hr _))
  refine ⟨σ', SectionScalarValuation.secScal_of_sval hL fun y J hJ => ?_⟩
  have e₁ : pullback.snd G.hom (Out.jK V) ≫ unitK = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, unitK, pullback.lift_fst, Category.id_comp, ← Category.assoc, ← pullback.condition,
        Category.assoc]
      exact (congrArg (_ ≫ ·) hG).trans (Category.comp_id _)
    · rw [Category.assoc, unitK, pullback.lift_snd, Category.id_comp, Category.comp_id]
  have e₂ : endK f = 𝟙 _ := by
    rw [← Category.comp_id (endK f), ← e₁, ← Category.assoc, endK, pullback.lift_snd, Category.comp_id]
  have v₁ := hn _ (pullback.snd G.hom (Out.jK V)) y J hJ
  rw [e₁, ← pullback.condition] at v₁
  have v₂ := hs _ (𝟙 _) y J hJ
  rw [v₁] at v₂
  have v₃ : sval s (𝟙 _ ≫ endK f) y J = sval σ (𝟙 _ ≫ pullback.fst G.hom (Out.jK V)) y J := by
    rw [e₂, Category.comp_id]
    exact (SectionScalarValuation.secScal_sval hσ (𝟙 _) y hJ).symm
  rw [hσ' _ _ y J hJ, sval_pullMulSec _ _ _ _ _ y hJ, val_pull hJ, v₂, v₃, Category.comp_id, Category.id_comp]
  exact congrArg (_ * ·) (congrArg Units.val (map_zpow _ _ _))

theorem nuK_pull [IsAdicComplete (maximalIdeal V) V] [CharZero V]
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {t : SAB H (Sp V)} (P : PELUnif (maximalIdeal V) t) {ϖ : V} (hϖ : Irreducible ϖ) {Q : P.D.toPre.X → ℤ}
    (hQ : QForm.IsQ P.D.toPre ϖ Q) {vK : AddValuation (FractionRing V) (WithTop ℚ)}
    (hv : ValOver ϖ (FractionRing V) vK) {tK : SAB H (Sp (FractionRing V))} (m : SABMap tK t (Out.jK V))
    (w : LB.Iso tK.PP.L (t.PP.L.pull m.φ)) (hw : RigIso m w) (π : 𝓞 E) (a b : ℕ) (ha : 0 < a)
    {a' b' : ℤ} (ea : a' = a) (eb : b' = b) {f : tK.G ⟶ tK.G} (ef : f = tK.act.act π)
    {μ' : 𝟙_ (Over (Sp (FractionRing V))) ⊗ tK.G ⟶ tK.G} (eμ : μ' = snd _ _ ≫ f)
    (F₁ : LB.Sec (LPow tK.G tK.PP.L b' (𝟙_ (Over (Sp (FractionRing V))))))
    (h₁ : LB.Sec (LPow tK.G tK.PP.L a' (𝟙_ (Over (Sp (FractionRing V))))))
    (α₀ : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![𝟙 tK.G.left, f.left] ![a', -b']))
    (α : LB.Gen (LB.LinComb tK.PP.L (K := Fin 2) ![(snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left, μ'.left]
      ![a', -b']))
    (h0 : NuK P Q vK m w b (zCast tK.G eb F₁)) (hα : α₀.IsGen) (hn : IsNormEnd tK.G tK.PP f a' b' α₀)
    (hc : LB.Gen.Corr tK.PP.L _ _ _ _ α
      (LB.pullGen tK.PP.L _ _ α₀ (snd (𝟙_ (Over (Sp (FractionRing V)))) tK.G).left))
    (htw : IsTwistPull tK.G tK.PP.L (lift (fst _ _) μ') μ' (lift_snd _ _) a' b' α F₁ h₁) :
    NuK P Q vK m w a (zCast tK.G ea h₁) := by
  subst ea eb ef eμ
  letI := H.starRing
  obtain ⟨s, F, hs, hF, hν⟩ := h0
  obtain ⟨s', hs', hrel⟩ := exists_pullRel_tie m w hw P π a b F₁ h₁ α₀ α hα hn hc htw s hs
  obtain ⟨F', hF', huniq⟩ := (P.U.expand a ha).1 s'
  refine ⟨s', F', hs', hF', ?_⟩
  rcases norm_or_trivial m w hw.1 P π a b ha α₀ hα with ⟨N, hN, hb, hπ, rfl⟩ | ⟨hG, hX⟩
  · have hπ' : π * star π = (N : 𝓞 E) := hπ
    obtain ⟨F'', h₁, h₂⟩ := GlobalTheory.PullEveryLevel.expands_pull_every_level GlobalTheory.abelianSchemeLaws_all.1 P π N hπ' hN hb
      s F hF s' (isPullByEnd_of_pullRel P.U _ b N hN s s' hrel)
    rw [← huniq F'' h₁]
    exact (GlobalTheory.pullbackValuation_norm_pel V ϖ hϖ P.D Q hQ _ vK hv (𝓞 E) P.oD H.w0 P.w0 π N hN hπ'
      (by rw [_root_.mul_comm]; exact hπ') b hb F F'' h₂ 0).1 hν
  · obtain ⟨σ, hσ⟩ := GlobalTheory.IntegralSection.main V ϖ hϖ P.D vK hv P.A t.G P.U.toUnifPre b s F hF
      (n1e V ϖ hϖ P.D Q hQ _ vK b F hν)
    obtain ⟨σ', hσ'⟩ := regular_of_pullRel hG P.U.LG _ a b s s' hrel σ hσ
    obtain ⟨g, -, hg⟩ := GlobalTheory.ExpInt.main V ϖ hϖ P.D P.A t.G P.U.toUnifPre a σ' s' hσ' F' hF'
    intro χ
    obtain rfl : χ = 0 := Subsingleton.elim _ _
    rw [QForm.Q_zero hϖ P.D hQ]
    simp only [Int.cast_zero, zero_div, add_zero]
    refine ⟨1, fun _ => 1, fun _ => g 0, fun _ => F'.s 0, fun _ => hg 0, fun _ => by simp, fun j => ?_⟩
    simp [DegPre.constBF]

end Main

theorem main : PullbackSections.EndNuSt ∧ PullbackSections.MulNuSt := by
  constructor
  · intro E _ _ _ H V _ _ _ _ _ t P _ ϖ hϖ Q hQ vK hv tK m w hw π n k hk F₁ α₀ α h₁ h0 hα hn hc htw
    exact nuK_pull P hϖ hQ hv m w hw π k (n ^ 2) hk rfl (natCast_sq n) rfl rfl F₁ h₁ α₀ α h0 hα hn hc htw
  · intro E _ _ _ H V _ _ _ _ _ t P _ ϖ hϖ Q hQ vK hv tK m w hw N hN s α₀ α s₁ h0 hα hn hc htw
    exact nuK_pull P hϖ hQ hv m w hw (N : 𝓞 E) (N ^ 2) 1 (pow_pos hN 2) (natCast_sq N) Nat.cast_one.symm
      (act_natCast tK N).symm (by rw [MonObj.comp_pow, Category.comp_id]) s s₁ α₀ α h0 hα
      ((GlobalTheory.PlaceInt.TwoLifts.normEnd_iff tK.G tK.PP N α₀).2 hn) hc htw

end GlobalTheory.EndPullNu
