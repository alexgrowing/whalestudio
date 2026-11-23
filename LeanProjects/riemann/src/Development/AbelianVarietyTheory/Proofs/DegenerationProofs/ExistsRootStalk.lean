import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FurtherLawsOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormLtOneOfIrreducible
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCoset
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.TestVal

theorem hyps (h : Laws) (h₂ : Laws2) :
    LL ∧ TwistBCSpanStatement ∧ TWM.VRatioGtStatement ∧ TWStatement ∧ UUStatement := by
  obtain ⟨h₃, h₄, h₅, -⟩ := GlobalTheory.furtherLaws_of_laws h GlobalTheory.twistBaseChange
  have t := twistBCSpan_of GlobalTheory.twistBaseChange
  have r : TWM.VRatioGtStatement := GlobalTheory.RatioVal.main
  exact ⟨⟨h, h₂, h₃, h₄, h₅⟩, t, r, TWM.tw_of h.globalFns t r, GlobalTheory.UnitBallFree.main h.globalFns GlobalTheory.twistBaseChange⟩

theorem exists_rat_log (p : ℕ) [Fact p.Prime] {x : PadicAlgCl p} (hx : x ≠ 0) :
    ∃ r : ℚ, Real.log ‖x‖ = r * Real.log p := by
  have hi : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have h0 : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hi hx
  have e : ‖x‖ = ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / (minpoly ℚ_[p] x).natDegree : ℝ) :=
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[p] (PadicAlgCl p) x
  refine ⟨1 / (minpoly ℚ_[p] x).natDegree * (-((minpoly ℚ_[p] x).coeff 0).valuation : ℤ), ?_⟩
  rw [e, Real.log_rpow (norm_pos_iff.2 h0), Padic.norm_eq_zpow_neg_valuation h0, Real.log_zpow]
  push_cast
  ring

theorem exists_addVal (p : ℕ) [Fact p.Prime] {π : PadicAlgCl p} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1) :
    ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), ∀ (x : PadicAlgCl p) (r : ℚ),
      v x = (r : WithTop ℚ) ↔ ‖x‖ = Real.exp (-(-Real.log ‖π‖ * r)) := by
  classical
  have hl : Real.log ‖π‖ < 0 := Real.log_neg h0 h1
  have key : ∀ x : PadicAlgCl p, x ≠ 0 → ∃ r : ℚ, Real.log ‖x‖ = Real.log ‖π‖ * r := fun x hx => by
    obtain ⟨a, ha⟩ := exists_rat_log p hx
    obtain ⟨b, hb⟩ := exists_rat_log p (norm_pos_iff.1 h0)
    have b0 : (b : ℝ) ≠ 0 := fun h => hl.ne (by rw [hb, h, zero_mul])
    refine ⟨a / b, ?_⟩
    rw [ha, hb]; push_cast; field_simp
  choose! f hf using key
  have inj : ∀ a b : ℚ, Real.log ‖π‖ * a = Real.log ‖π‖ * b → a = b := fun a b h => by
    exact_mod_cast mul_left_cancel₀ hl.ne h
  have mono : ∀ x y, x ≠ 0 → y ≠ 0 → ‖x‖ ≤ ‖y‖ → f y ≤ f x := fun x y hx hy h => by
    have := Real.log_le_log (norm_pos_iff.2 hx) h
    rw [hf x hx, hf y hy] at this
    exact_mod_cast (mul_le_mul_left_of_neg hl).1 this
  refine ⟨AddValuation.of (fun x => if x = 0 then ⊤ else (f x : WithTop ℚ)) (if_pos rfl) ?_ ?_ ?_, fun x r => ?_⟩
  · rw [if_neg one_ne_zero, inj (f 1) 0 (by rw [← hf 1 one_ne_zero]; simp)]; rfl
  · intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    by_cases hs : x + y = 0
    · simp [hs]
    simp only [if_neg hx, if_neg hy, if_neg hs, min_le_iff, WithTop.coe_le_coe]
    exact (le_max_iff.1 (IsUltrametricDist.norm_add_le_max x y)).imp (mono _ _ hs hx) (mono _ _ hs hy)
  · intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    have hs := mul_ne_zero hx hy
    simp only [if_neg hx, if_neg hy, if_neg hs, ← WithTop.coe_add]
    refine congrArg _ (inj _ _ ?_)
    rw [← hf _ hs, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy), hf x hx, hf y hy]
    push_cast; ring
  · rw [AddValuation.of_apply, neg_mul, neg_neg]
    by_cases hx : x = 0
    · simp [hx, (Real.exp_pos _).ne]
    rw [if_neg hx, WithTop.coe_eq_coe]
    refine ⟨fun h => by rw [← h, ← hf x hx, Real.exp_log (norm_pos_iff.2 hx)], fun h => inj _ _ ?_⟩
    rw [← hf x hx, h, Real.log_exp]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem charZero : CharZero u.V :=
  ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero

theorem isUnit_level (h : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) : IsUnit ((S.r * S.N : ℕ) : u.V) := by
  obtain ⟨b, hb⟩ := S.unit.exists_right_inv
  obtain ⟨c, hc⟩ := (u.norm_le (u.yK (algebraMap o S.R b))).1 (by
    rw [← RingHom.comp_apply, u.fac]; exact h b)
  refine IsUnit.of_mul_eq_one c (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  have := congrArg (fun a => u.yK (algebraMap o S.R a)) hb
  simp only [map_mul, map_natCast, map_one] at this ⊢
  rw [hc]; simpa using this

theorem exists_val : ∃ (ϖ : u.V) (_ : Irreducible ϖ) (Q : u.D.toPre.X → ℤ) (_ : QForm.IsQ u.D.toPre ϖ Q)
    (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (_ : ValOver ϖ (PadicAlgCl p) v) (lam : ℝ), 0 < lam ∧
    (∀ (x : PadicAlgCl p) (r : ℚ), v x = (r : WithTop ℚ) ↔ ‖x‖ = Real.exp (-(lam * r))) ∧
    (∀ (x : PadicAlgCl p) (r : ℚ), (r : WithTop ℚ) ≤ v x ↔ ‖x‖ ≤ Real.exp (-(lam * r))) ∧
    ∀ (l : u.Lab) χ, l.q χ = lam * Q χ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using QForm.exists_QVal hϖ u.D
  have h0 := PsiForm.norm_pos_of_irreducible (F := PadicAlgCl p) hϖ
  have h1 := PsiForm.norm_lt_one_of_irreducible u.norm_le hϖ
  have hl := neg_pos.2 (Real.log_neg h0 h1)
  obtain ⟨v, hv⟩ := exists_addVal p h0 h1
  refine ⟨ϖ, hϖ, Q, hQ, v, fun c n hc => (hv _ _).2 ?_, _, hl, hv, fun x r => ?_, fun l χ => ?_⟩
  · rw [PsiForm.norm_of_hasVal u.norm_le hϖ hc]; simp
  · by_cases hx : x = 0
    · simp [hx, (Real.exp_pos _).le]
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hx)
    rw [(hv x s).1 hs.symm, ← hs, WithTop.coe_le_coe, Real.exp_le_exp, neg_le_neg_iff, mul_le_mul_iff_right₀ hl,
      Rat.cast_le]
  · obtain ⟨j, hj⟩ := exists_chart u.D.toPre.P.isLB ((u.D.toPre.c χ).left (IsLocalRing.closedPoint u.V))
    have hj' : ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U j :=
      ((IsLocalRing.closedPoint_mem_iff _).1 hj).ge
    have a := l.q_eq χ (fun _ => j) hj'
    have b := PsiForm.norm_of_hasVal u.norm_le hϖ
      (PsiForm.hasVal_valF u.D.toPre.P.L _ _ (QForm.ptK_eq u.D.toPre χ) (-1) _ (hQ χ) (fun _ => j) hj')
    exact neg_injective (Real.exp_injective (a.symm.trans b))

section
open GlobalTheory.ThetaCompare CommPairing

theorem exists_root_stalk {B : Scheme.{0}} (hG : GlobalFnsSt) (P : PolAV B) {T : Over B} {m : ℕ} (hm : Odd m) {k : ℤ}
    (hk : k = (m : ℤ) ^ 2) {rig : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} {τ}
    (hτ : IsTorsFrame P rig m (x ^ m) τ) {th : LB.Sec (LPow P.A P.L 1 T)} {s₁ t : LB.Sec (LPow P.A P.L k T)}
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![k, -1])}
    {θ : ThetaGrp P.A P.L k T} (hα : α.IsGen)
    (hn : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (rigT P.A P.L rig T (k - 1)))
    (h₁ : IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) k 1 α th s₁)
    (hθ : SymLift P.A P.L k (m ^ 2) x θ) (h₂ : IsActOf P.A P.L k θ s₁ t) {y : T.left} {J} (hJ : Good P.L y J)
    {c c' : T.left.presheaf.stalk y}
    (hc : sval (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => k) t (ptSecT P.A 1).left y J =
      c * (val (rigT P.A P.L rig T k) (𝟙 _) y J).val)
    (hc' : sval (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => 1) th (ptSecT P.A (x ^ m)).left y J =
      c' * (val (powFrame P.A P.L (x ^ m) τ 1) (𝟙 _) y J).val) :
    c ^ (m ^ 2) = c' ^ (m ^ 2) := by
  subst hk
  have hx : x ^ (m ^ 2) = 1 := by rw [sq, pow_mul, hτ.1]
  have a₁ := frame_pow hG P hm hα hx hθ hJ
  have a₂ := torsFrame_pow hG P hα hτ hJ
  have a₃ := val_corr hJ hn (𝟙 _)
  rw [val_pull hJ, val_rigT _ _ hJ, Category.id_comp] at a₃
  have b₂ := sval_twist h₂ (ptSecT P.A 1).left hJ
  have b₃ := sval_twist h₁ (ptSecT P.A x).left hJ
  have p₂ : val (powFrame P.A P.L (x ^ m) τ 1) (𝟙 _) y J = val τ (𝟙 _) y J :=
    (map_zpow _ _ _).trans (zpow_one _)
  rw [pt_translT, _root_.mul_one, congrArg (ptSecT P.A) hθ.pt_eq, b₃, hc, pt_mulT, hc', p₂, val_rigT _ _ hJ] at b₂
  have e : (tval θ (ptSecT P.A 1).left y J * val α (ptSecT P.A x).left y J * val τ (𝟙 _) y J *
      (val rig T.hom y J ^ ((m : ℤ) ^ 2))⁻¹) ^ (m ^ 2) = 1 := by
    apply Additive.ofMul.injective
    replace a₁ := congrArg Additive.ofMul a₁
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one] at a₁ a₂ a₃ ⊢
    linear_combination (norm := module) a₁ + a₂ + (m ^ 2) • a₃
  have e' : c = (tval θ (ptSecT P.A 1).left y J * val α (ptSecT P.A x).left y J * val τ (𝟙 _) y J *
      (val rig T.hom y J ^ ((m : ℤ) ^ 2))⁻¹).val * c' := by
    rw [(Units.eq_mul_inv_iff_mul_eq _).2 b₂]
    simp only [Units.val_mul, tval]
    ring
  rw [e', mul_pow, ← Units.val_pow_eq_pow_val, e, Units.val_one, _root_.one_mul]

theorem pow_eq_of_thC (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V]
    {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {F : Type} [Field F] [Algebra (FractionRing V) F]
    {rig : LB.Gen (A.L.pull (eSec A.A))} {m : ℕ} (hm : Odd m) {th : SecA A F 1} {x : TFK (R := V) F ⟶ A.A} {t} {c c' : F}
    (H : ThC A rig m th x t c) {e} (he : IsTorsFrame A rig m (x ^ m) e)
    (hc : (∀ z J, Good A.L z J → sA th (ptSecT A.A (x ^ m)).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c') * (val (powFrame A.A A.L (x ^ m) e ((1 : ℕ) : ℤ)) (𝟙 _) z J).val)) :
    c ^ (m ^ 2) = c' ^ (m ^ 2) := by
  obtain ⟨α, s₁, θ, hα, hn, h₁, hθ, h₂, hv⟩ := H
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := V) F).left) A.isLB z
  have := exists_root_stalk hG A hm (Nat.cast_pow m 2) he hα hn h₁ hθ h₂ hJ (hv z J hJ) (hc z J hJ)
  apply CoefBasic.cstH_inj (R := V) z
  rw [map_pow, map_pow, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq]
  exact this

end

theorem val_eq_of_pow_eq {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {n : ℕ} (hn : n ≠ 0) {c c' : F}
    (h : c ^ n = c' ^ n) : v c = v c' := by
  by_cases h0 : c' = 0
  · subst h0
    rw [zero_pow hn] at h
    rw [pow_eq_zero_iff hn |>.1 h]
  have hc : c ≠ 0 := fun e => h0 (pow_eq_zero_iff hn |>.1 (by rw [← h, e, zero_pow hn]))
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc)
  obtain ⟨r', hr'⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 h0)
  have := congrArg v h
  rw [v.map_pow, v.map_pow, ← hr, ← hr', ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, WithTop.coe_eq_coe] at this
  rw [← hr, ← hr', nsmul_right_injective hn this]

open GlobalTheory.TorusExt in
attribute [local instance] gtGroup in

theorem val_theta : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement →
    AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ rig, NormW U.toUnifPre w₀ rig →
      ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ →
      ∀ (m : ℕ), Odd m → IsUnit (m : V) → ∀ (p : QkPt D.toPre F m) x, QkToAkU U.toUnifPre F m p x →
        (∀ e (c : F), IsTorsFrame A rig m x e → (∀ z J, Good A.L z J → sA th (ptSecT A.A x).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x e ((1 : ℕ) : ℤ)) (𝟙 _) z J).val) →
          (∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c) ∧
            (v c = 0 → ∃ z, p.y = m • z)) ∧
        ∀ n, 2 ≤ n → n ∣ m → p.y = 0 → ∃ (p' : QkPt D.toPre F m) (x' : _), p'.y = 0 ∧
          QkToAkU U.toUnifPre F m p' x' ∧ (x' * x⁻¹) ^ n = 1 ∧
          ∀ e (c : F), IsTorsFrame A rig m x' e → (∀ z J, Good A.L z J → sA th (ptSecT A.A x').left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x' e ((1 : ℕ) : ℤ)) (𝟙 _) z J).val) → v c = 0 := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ rig hN th ϑ hE hP m hm hu p x hx
  have hA : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  have m2 : m ^ 2 ≠ 0 := (pow_pos hm.pos 2).ne'
  obtain ⟨ua₁, ua₂⟩ := ThetaConstVal.main hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ rig hN th ϑ hE hP m hm hu
  have up := GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D A G hG U F m m (m ^ 2) hm.pos hm.pos (sq m)
  obtain ⟨g, hg⟩ := (gt_onto_divisible_kernel hL V _ hA D F).2.1 m hm.pos p.g
  have hg' := (isNsmul_iff_eq _ _ _).1 hg
  let q : QkPt D.toPre F (m ^ 2) := qkMk hB p.y g (by rw [sq, mul_smul, ← hg', qk_nsmul hB])
  obtain ⟨f, f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F (m ^ 2) (pow_pos hm.pos 2)
  obtain ⟨f', f₁', -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F m hm.pos
  have hq : QkToAkU U.toUnifPre F (m ^ 2) q (f q) := (f₁ _ _).2 rfl
  obtain rfl : x = f q ^ m := ((f₁' _ _).1 hx).trans ((f₁' _ _).1 ((up p q _).2 rfl hg hq)).symm
  refine ⟨fun e c he hval => ?_, fun n hn hnm hy => ?_⟩
  · obtain ⟨⟨t, c₀⟩, hT, -⟩ := GlobalTheory.existsUnique_thetaConst hL V A F rig hN.2.1 m hm th (f q) (hq w₀ hN.1).1
    rw [← val_eq_of_pow_eq v m2 (pow_eq_of_thC hL.1.globalFns hm hT he hval)]
    exact ua₁ q _ t c₀ hq hT
  · obtain ⟨q', x', t, c₀, hy', hq', hpow, hT, h0⟩ := ua₂ n hn hnm q _ hy hq
    let p' : QkPt D.toPre F m := qkMk hB q'.y (m • q'.g) (by rw [← mul_smul, ← sq, qk_nsmul hB])
    refine ⟨p', x' ^ m, hy', (up p' q' x').2 rfl ((isNsmul_iff_eq _ _ _).2 rfl) hq', hpow, fun e c he hval => ?_⟩
    rw [← val_eq_of_pow_eq v m2 (pow_eq_of_thC hL.1.globalFns hm hT he hval), h0]

end GlobalTheory.ZH.TestVal
end
