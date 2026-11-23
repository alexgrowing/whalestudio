import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullbackValuationInvarianceOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NuGeIffOfIsActOfOfQkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamEqOfCoefEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphism
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsSymmetricFrameAndTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactTermAfterTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCoset

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.PrimPull
open GlobalTheory.TorusExt
attribute [local instance] gtGroup

theorem sec_eq_of_points {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] {k : ℕ} {χ : D.X}
    {s s' : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε k))}
    (H : ∀ (b : TF (R := R) F ⟶ D.P.A) z J, Good D.P.L z J →
      sval s (lift (𝟙 (TF (R := R) F)) b).left z J = sval s' (lift (𝟙 (TF (R := R) F)) b).left z J) (j) :
    s.f j = s'.f j := by
  have hsm := D.P.isAb.smooth
  let p : (DegPre.BF D F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) D.P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst (TF (R := R) F).hom D.P.A.hom))
  have : IsReduced (DegPre.BF D F).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  refine CoefDet.fn_ext_of_points p fun r hr z hz => ?_
  let r' : TF (R := R) F ⟶ DegPre.BF D F := Over.homMk r (by
    rw [← Over.w (fst (TF (R := R) F) D.P.A), ← Category.assoc]
    exact (congrArg (· ≫ (TF (R := R) F).hom) hr).trans (Category.id_comp _))
  have er : lift (𝟙 (TF (R := R) F)) (r' ≫ snd _ _) = r' := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)
    rw [lift_fst]
    exact Over.OverMorphism.ext hr.symm
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TF (R := R) F).left) D.P.isLB z
  have a := H (r' ≫ snd _ _) z J hJ
  rw [er] at a
  exact (sec_trans s r z hz (hJ.mem _ r)).trans ((congrArg _ a).trans (sec_trans s' r z hz (hJ.mem _ r)).symm)

theorem exists_cmp {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (m : ℕ) (hm : 1 ≤ m) (χ : D.X)
    (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ m) (m ^ 2) 1)) (hκ : κ.IsGen) :
    ∃ (K : Type) (_ : Fintype K) (ψ : K → (D.P.A.left ⟶ D.P.A.left)) (δ : K → ℤ) (e : LB.Gen (LB.LinComb D.P.L ψ δ)),
      e.IsGen ∧ FormEq (Sum.elim (fun i => (𝟙 D.P.A ^ m).left ≫ D.famφB χ i) ψ) (Sum.elim (DegPre.famε 1) δ)
        (D.famφB (m • χ)) (DegPre.famε (m ^ 2)) ∧
      ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g : GtPtF D F) z J, Good D.P.L z J →
        val e g.b.left z J * val (g.s (m • χ)) (𝟙 _) z J * rigV D (TF (R := R) F).hom z J =
          val ((m • g).s χ) (𝟙 _) z J * val κ g.b.left z J * rigV D (TF (R := R) F).hom z J ^ (m ^ 2) := by
  obtain ⟨u, hu⟩ := IntEnd.exists_isCmp D (m : ℤ) χ
  obtain ⟨N, hN⟩ : ∃ N, m ^ 2 = N + 1 := ⟨m ^ 2 - 1, by have := Nat.one_le_pow 2 m hm; omega⟩
  let ρ := LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.P.A.hom
  have hρ : ρ.IsGen := pullGen_isGen _ _ _ _ D.rig_gen _
  refine ⟨_, _, _, _, LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ u κ) (GeneratorPullback.powGen D.P.L _ _ ρ N),
    mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hu.1 hκ) (powGen_isGen _ _ _ _ hρ N),
    fun U _ h => ?_, fun F _ _ g z J hJ => ?_⟩
  · have p₁ := SectionScalarValuation.prod_famB D (𝟙 D.P.A ^ m) χ 1 h
    have p₂ := IntEnd.prod_end D (m : ℤ) χ h
    have p₃ := SectionScalarValuation.prod_famB D (𝟙 D.P.A) (m • χ) (m ^ 2) h
    have e₃ : ∀ i, Over.Hom.left (𝟙 D.P.A) ≫ D.famφB (m • χ) i = D.famφB (m • χ) i := fun i => by simp
    simp only [e₃] at p₃
    have p₄ : ∏ i : Fin 3, h ((![𝟙 _, (𝟙 D.P.A ^ m).left, (1 : D.P.A ⟶ D.P.A).left] : Fin 3 → _) i) ^
        (![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - (m ^ 2 : ℕ)] : Fin 3 → ℤ) i =
        h (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ ((m ^ 2 : ℕ) : ℤ) * h (𝟙 D.P.A ^ m).left ^ (-((1 : ℕ) : ℤ)) *
          h (1 : D.P.A ⟶ D.P.A).left ^ (((1 : ℕ) : ℤ) - (m ^ 2 : ℕ)) := by
      rw [Fin.prod_univ_three]; rfl
    have p₅ : ∏ _i : PUnit.{1}, h (D.P.A.hom ≫ eSec D.P.A) ^ ((N : ℤ) * 1) = h (1 : D.P.A ⟶ D.P.A).left ^ (N : ℤ) := by
      rw [Fintype.prod_unique, _root_.mul_one]; rfl
    refine (prod_sum₂ (U := U) _ p₁ (prod_sum₂ (U := U) _ (prod_sum₂ (U := U) _ p₂ p₄) p₅)).trans (Eq.trans ?_ p₃.symm)
    have c : ∀ a, SectionScalarValuation.cQ D D.P.A a = cP D D.P.A a := fun _ => rfl
    rw [SectionScalarValuation.cQ_nsmul, c, zpow_natCast, zpow_natCast, mul_comm (𝟙 D.P.A ^ m), mul_comm (𝟙 D.P.A), hN]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    push_cast
    module
  · have a := IntEnd.charVal_zsmul hu g hJ
    rw [natCast_zsmul g] at a
    have a' : val ((m • g).s χ) (𝟙 _) z J = val (g.s (m • χ)) (𝟙 _) z J * val u g.b.left z J :=
      a.trans (congrArg (fun w => charVal g w z J * val u g.b.left z J) (natCast_zsmul χ m))
    have b : val ρ g.b.left z J = rigV D (TF (R := R) F).hom z J := by
      refine (val_pull hJ _ _ _).trans ?_
      rw [Over.w g.b]; rfl
    have pw : rigV D (TF (R := R) F).hom z J ^ (m ^ 2) = rigV D (TF (R := R) F).hom z J ^ (N + 1) := by rw [hN]
    rw [val_mul hJ, val_mul hJ, val_pow, b, a', pw]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow]
    module

def CoefPull {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] (m : ℕ)
    (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ m) (m ^ 2) 1)) (ϑ : Fam D F 1) (s : Fam D F (m ^ 2)) : Prop :=
  ∀ (g : GtPtF D F) (w' : Frm D F (m ^ 2) g.b) (w : Frm D F 1 (m • g).b), w'.IsGen → w.IsGen →
    (∀ z J, Good D.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J) →
    (∀ χ, coef s g w' (m • χ) = coef ϑ (m • g) w χ) ∧ ∀ β, (∀ χ, m • χ ≠ β) → coef s g w' β = 0

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
  {m : ℕ} {κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ m) (m ^ 2) 1)} {ϑ : Fam D.toPre F 1} {s : Fam D.toPre F (m ^ 2)}

theorem CoefPull.off (H : CoefPull m κ ϑ s) (hκ : κ.IsGen) {β : D.toPre.X} (hβ : ∀ χ, m • χ ≠ β) (j) :
    (s.s β).f j = 0 := by
  refine sec_eq_of_points (s' := (0 : Fam D.toPre F (m ^ 2)).s β) (fun b z J hJ => ?_) j
  obtain ⟨g, rfl⟩ := exists_lift (D := D.toPre) (F := F) b
  obtain ⟨w', hw'⟩ := (CoefBasic.coef_basic V D.toPre F (m ^ 2) g).1
  obtain ⟨w, hw, e⟩ := ThetaConstVal.exists_frm D.toPre m g.b (m • g).b (nsmul_b m g) w' hw' κ hκ
  have a := CoefBasic.isCoef_coef g hw' β s z J hJ
  rw [(H g w' w hw' hw e).2 β hβ, CoefBasic.cst_eq, map_zero, MulZeroClass.zero_mul, eq_comm,
    Units.mul_left_eq_zero, Units.mul_left_eq_zero] at a
  have hm := hJ.mem (DegPre.famφ D.toPre F β) (lift (𝟙 (TF (R := V) F)) g.b).left
  exact a.trans ((gs_eq _ z _ hm _).trans ((congrArg _ (map_zero _)).trans (map_zero _))).symm

theorem CoefPull.vge (H : CoefPull m κ ϑ s) (hκ : κ.IsGen) (hm : 1 ≤ m) (χ : D.toPre.X) {r : ℚ}
    (h : VGe D F v 1 χ (ϑ.s χ) r) : VGe D F v (m ^ 2) (m • χ) (s.s (m • χ)) r := by
  have hL := D.toPre.P.isLB
  obtain ⟨K, _, ψ, δ, e, he, hf, ve⟩ := exists_cmp D.toPre m hm χ κ hκ
  let a : DegPre.BF D.toPre F ⟶ DegPre.BF D.toPre F := lift (fst _ _) (DegPre.prB D.toPre F ≫ 𝟙 D.toPre.P.A ^ m)
  have hfst : a.left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left := by
    rw [← Over.comp_left, lift_fst]
  have hh : a.left ≫ (DegPre.prB D.toPre F).left = (DegPre.prB D.toPre F).left ≫ (𝟙 D.toPre.P.A ^ m).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_snd]
  let u := LB.pullGen D.toPre.P.L _ _ e (DegPre.prB D.toPre F).left
  have hu : u.IsGen := pullGen_isGen _ _ _ _ he _
  obtain ⟨t, ht⟩ := exists_sec hL (φ' := DegPre.famφ D.toPre F (m • χ)) (ε' := DegPre.famε (m ^ 2)) (fun U _ k => by
    have := hf U fun q => k ((DegPre.prB D.toPre F).left ≫ q)
    refine (Finset.prod_congr rfl ?_).trans (this.trans (Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]))
    rintro (i | i) -
    · simp only [Sum.elim_inl]
      rw [GC.famφ_eq, ← Category.assoc, hh, Category.assoc]
    · rfl) (pullMulSec (ϑ.s χ) a.left u hu)
  have E : ∀ j, (s.s (m • χ)).f j = t.f j := sec_eq_of_points fun b z J hJ => by
    obtain ⟨g, rfl⟩ := exists_lift (D := D.toPre) (F := F) b
    obtain ⟨w', hw'⟩ := (CoefBasic.coef_basic V D.toPre F (m ^ 2) g).1
    obtain ⟨w, hw, ew⟩ := ThetaConstVal.exists_frm D.toPre m g.b (m • g).b (nsmul_b m g) w' hw' κ hκ
    have a₁ := CoefBasic.isCoef_coef g hw' (m • χ) s z J hJ
    have a₂ := CoefBasic.isCoef_coef (m • g) hw χ ϑ z J hJ
    have l₁ : (lift (𝟙 (TF (R := V) F)) g.b).left ≫ a.left = (lift (𝟙 (TF (R := V) F)) (m • g).b).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, ← Category.assoc, lift_snd, MonObj.comp_pow, Category.comp_id, nsmul_b]
    have l₂ : (lift (𝟙 (TF (R := V) F)) g.b).left ≫ (DegPre.prB D.toPre F).left = g.b.left := by
      rw [← Over.comp_left, lift_snd]
    have a₃ := congrArg Units.val (ve F g z J hJ)
    have a₄ := congrArg Units.val (ew z J hJ)
    rw [(H g w' w hw' hw ew).1 χ] at a₁
    rw [ht _ _ z J hJ, sval_pullMulSec _ _ _ hu _ z hJ, val_pull hJ, l₁, l₂]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, pow_one] at a₂ a₃ a₄
    refine (val (g.s (m • χ)) (𝟙 _) z J * val w' (𝟙 _) z J * rigV D.toPre (TF (R := V) F).hom z J).mul_left_inj.1 ?_
    simp only [Units.val_mul]
    linear_combination (-(rigV D.toPre (TF (R := V) F).hom z J).val) * a₁ +
      (rigV D.toPre (TF (R := V) F).hom z J).val ^ (m ^ 2) * a₂ -
      sval (ϑ.s χ) (lift (𝟙 (TF (R := V) F)) (m • g).b).left z J * (val w' (𝟙 _) z J).val * a₃ -
      sval (ϑ.s χ) (lift (𝟙 (TF (R := V) F)) (m • g).b).left z J * (val ((m • g).s χ) (𝟙 _) z J).val *
        (rigV D.toPre (TF (R := V) F).hom z J).val ^ (m ^ 2) * a₄
  have hrel := (secRel_iff hL _ _ (s.s (m • χ)) _ _ (ϑ.s χ) a.left _ _ u).2 fun y J hJ => by
    rw [NormTheta.sec_ext E, ht _ _ y J hJ, sval_pullMulSec _ _ _ hu _ y hJ]
  have := SectionScalarValuation.vge_move₂ hfst hh u hrel e he hf 1 (fun y J hJ => by
    rw [val_pull hJ, Category.id_comp, map_one, gs_eq _ y ⊤ trivial, map_one, map_one, _root_.one_mul])
    (q := 0) (by simp) h
  rwa [add_zero] at this

end

theorem exists_unit (V : Type) [CommRing V] [IsLocalRing V] : ∃ n : ℕ, 2 ≤ n ∧ IsUnit (n : V) := by
  have h : IsUnit (((3 : ℕ) : V) + -((2 : ℕ) : V)) := by
    rw [show ((3 : ℕ) : V) + -((2 : ℕ) : V) = 1 by push_cast; ring]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  exacts [⟨3, by omega, h⟩, ⟨2, le_rfl, (IsUnit.neg_iff _).1 h⟩]

theorem prim_of_coefPull : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement →
    AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (m : ℕ), 1 ≤ m →
      ∀ (κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ m) (m ^ 2) 1)), κ.IsGen →
      ∀ (ϑ : Fam D.toPre F 1) (s : Fam D.toPre F (m ^ 2)), CoefPull m κ ϑ s → Prim D Q v ϑ → Prim D Q v s := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv m hm κ hκ ϑ s H hP
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have CV := GlobalTheory.UT.CoefVal.main hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  refine ⟨fun β => ?_, fun r hr hs => ?_⟩
  · by_cases hβ : ∃ χ, m • χ = β
    · obtain ⟨χ, rfl⟩ := hβ
      refine (H.vge hκ hm χ (hP.1 χ)).mono (le_of_eq ?_)
      rw [Q_nsmul hϖ hQ]
      push_cast
      field_simp
    · exact vge_of_zero (H.off hκ fun χ e => hβ ⟨χ, e⟩) _
  · obtain ⟨n, hn, hu⟩ := exists_unit V
    obtain ⟨-, -, g₂, -, -, -, hg₂⟩ := GlobalTheory.UT.ExactTerm.exact_term_after_torsion hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv
      ϑ hP n hn hu 0 0
    obtain ⟨g, hg⟩ := (gt_onto_divisible_kernel hL V _ hA D F).2.1 m hm g₂
    obtain rfl := (isNsmul_iff_eq _ _ _).1 hg
    obtain ⟨w', hw'⟩ := (CoefBasic.coef_basic V D.toPre F (m ^ 2) g).1
    obtain ⟨w, hw, ew⟩ := ThetaConstVal.exists_frm D.toPre m g.b (m • g).b (nsmul_b m g) w' hw' κ hκ
    obtain ⟨l', hl', -⟩ := (CV g).1
    obtain ⟨l, hl, -⟩ := (CV (m • g)).1
    obtain ⟨ω', hω', -⟩ := (CV g).2.1 _ w' hw'
    obtain ⟨ω, hω, -⟩ := (CV (m • g)).2.1 _ w hw
    obtain ⟨b, hb⟩ := TWM.exists_liftO hϖ hv g.b
    have e := TxVal.genV_unique D.toPre.P.isLB D.toPre.P.A.hom (fun U _ h => by
        refine (prod_sum₂ (K := Fin 2) (K' := Fin 3) (U := U) _ (TxVal.prod_line g.b (m ^ 2) h) rfl).trans
          (Eq.trans ?_ (TxVal.prod_line (m • g).b 1 h).symm)
        simp only [Sum.elim_inr, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          TxVal.comp_pow_left, TxVal.comp_one_left, Category.comp_id, nsmul_b]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow]
        module)
      (fun z J hJ => by
        rw [val_mul hJ, val_pull hJ, Category.id_comp]
        exact ew z J hJ)
      (TxVal.genV_mul hω' (TxVal.genV_pull κ hκ g.b.left b.left (congrArg (fun q => q.left) hb))) hω
    have b₁ := ((CV g).2.2.2.2.2.2 _ hm2 w' s hw').2 _ _ _ hl' hω' hs (m • 0)
    rw [(H g w' w hw' hw ew).1 0, hg₂ w _ _ hw hl hω, smul_zero, map_zero, map_zero, QForm.Q_zero hϖ D hQ,
      WithTop.coe_le_coe] at b₁
    simp only [Int.cast_zero, zero_div] at b₁
    linarith

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ (m : ℕ), Odd m → IsUnit (m : V) → ∀ x t c s, x ^ (m ^ 2) = 1 → ThC A ρ m th x t c → U.ExpandsF F (m ^ 2) w₀ t s → Prim D Q v s := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hϑ hP m hm _ x t c s hx hT hs
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨α, s₁, θ, hα, hαn, htw, hθ, hact, -⟩ := hT
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  have hB := (expBijF_and_expandsF_lin hL V _ hA D A G hG U).1
  obtain ⟨σ₁, hσ₁, -⟩ := (hB F (m ^ 2) hm2 w₀ hN.1).1 s₁
  obtain ⟨E, hEG, hEA, hEB, hEh, hEact⟩ := (IntEnd.exists_nsmul_and_neg hL V _ hA D A G hG U).1 m
  have hinj : Function.Injective E.h := fun a b h => by
    have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul, hEh] using h
    exact smul_right_injective D.toPre.X (Int.natCast_ne_zero.2 hm.pos.ne') h'
  have hpull := (GlobalTheory.UT.PullExp.main hL V _ hA D A G hG U F E hinj (m ^ 2) 1 le_rfl hm2
    (ThetaSum.exists_gen_pow U.LG U.cubG U.symG U.symG_gen m E.aG hEG)).2 w₀ ρ hN (mulT A.A _ m) (snd _ A.A ^ m)
    (lift_snd _ _) (lift_fst _ _) (by rw [hEA, MonObj.comp_pow, Category.comp_id]) α hα hαn th s₁ ϑ σ₁ hϑ hσ₁ htw
  rw [hEB] at hpull
  obtain ⟨κ, hκ⟩ := ThetaConstVal.exists_kap D.toPre hL.1.mulPull m
  have P₁ : Prim D Q v σ₁ := prim_of_coefPull hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv m hm.pos κ hκ.1 ϑ σ₁
    (fun g w' w hw' hw e => by
      obtain ⟨q₁, q₂⟩ := hpull κ hκ g (m • g) ((hEact F g _).2 ((isNsmul_iff_eq _ _ _).2 rfl)) w' w hw' hw e
      exact ⟨fun χ => hEh χ ▸ q₁ χ, fun β hβ => q₂ β fun ⟨χ, e⟩ => hβ χ ((hEh χ).symm.trans e)⟩) hP
  obtain ⟨f, f₁, f₂, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F (m ^ 2) hm2
  obtain ⟨p, hp⟩ := f₂ x hx
  have key := GlobalTheory.nuGe_iff_of_isActOf_of_qkToAkU hL.1 h₃ V ϖ hϖ D A G U hB Q hQ F v hv (m ^ 2) hm2 w₀ hN.1 θ p
    ((f₁ _ _).2 (hθ.pt_eq.trans hp.symm)) (m ^ 2) hm2 (hθ.pt_eq ▸ hx) hθ.pow_eq s₁ t σ₁ s hσ₁ hs hact
  exact ⟨(key 0).1 P₁.1, fun r hr h => P₁.2 r hr ((key r).2 h)⟩

end GlobalTheory.UT.PrimPull
end
