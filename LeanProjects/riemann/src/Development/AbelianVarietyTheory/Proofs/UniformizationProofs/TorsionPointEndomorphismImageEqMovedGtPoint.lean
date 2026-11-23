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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaActs
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSmulEqBilinOfAnisotropic
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLeOnFinset
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossIffOfIsActOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffMapDomainMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelationStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmallTorusPointKeepingRatiosIsZeroStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.EndTors
open GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic

attribute [local instance] gtGroup

theorem eq_zero_of_sumV_zero {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix : Type} {c : F}
    (h : SumV v (0 : Ix → F) c) : c = 0 := by
  by_contra hc
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (mt (AddValuation.top_iff v).1 hc)
  obtain ⟨S, hS⟩ := h (r + 1)
  have := hS S le_rfl
  simp only [Pi.zero_apply, Finset.sum_const_zero, sub_zero, ← hr, WithTop.coe_le_coe] at this
  linarith

theorem sumV_equiv {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {Ix Ix' : Type} (e : Ix ≃ Ix') {x : Ix → F}
    {x' : Ix' → F} (hx : ∀ i, x i = x' (e i)) {c : F} (h : SumV v x c) : SumV v x' c := by
  intro q
  obtain ⟨S, hS⟩ := h q
  refine ⟨S.map e.toEmbedding, fun T hT => ?_⟩
  have := hS (T.map e.symm.toEmbedding) fun i hi => Finset.mem_map.2
    ⟨e i, hT (Finset.mem_map.2 ⟨i, hi, rfl⟩), e.symm_apply_apply i⟩
  rw [Finset.sum_map] at this
  simpa only [hx, Equiv.toEmbedding_apply, Equiv.apply_symm_apply] using this

theorem sumV_shift {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {X : Type} [AddCommGroup X] (h : X →+ X)
    (y y' : X) {B₁ B₂ C₁ C₂ b₁ b₂ c₁ c₂ : X → F} (hB₁ : ∀ α, B₁ (α + y) = b₁ α) (hB₂ : ∀ α, B₂ (α + y) = b₂ α)
    (hC₁ : ∀ α, C₁ (α + y') = c₁ α) (hC₂ : ∀ α, C₂ (α + y') = c₂ α)
    (H : ∀ α, SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => b₁ p.1.1 * c₂ p.1.2 - b₂ p.1.1 * c₁ p.1.2) 0) (α : X) :
    SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0 := by
  refine sumV_equiv v (Equiv.subtypeEquiv ((Equiv.addRight y).prodCongr (Equiv.addRight y')) fun p => ?_) (fun p => ?_)
    (H (α - h y - y'))
  · simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight, map_add]
    constructor
    · intro e; rw [show α = α - h y - y' + h y + y' by abel, ← e]; abel
    · intro e; rw [← e]; abel
  · simp only [Equiv.subtypeEquiv_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight,
      hB₁, hB₂, hC₁, hC₂]

section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_rigT (ρ : LB.Gen (A.L.pull (eSec A.A))) (k : ℤ) {z : (TFK (R := R) F).left} {J} (hJ : Good A.L z J) :
    val (rigT A.A A.L ρ (TFK (R := R) F) k) (𝟙 _) z J =
      val (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) ρ (𝟙 _ ≫ (TFK (R := R) F).hom) z J ^ k := by
  have hm := hJ.mem (fun _ : Fin 1 => (TFK (R := R) F).hom ≫ eSec A.A) (𝟙 _)
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ z _ hm _).trans ?_))
  exact gm_pull (𝟙 _) (TFK (R := R) F).hom z _ (rigT_le A.A A.L _ hm) _

theorem exists_value {ρ : LB.Gen (A.L.pull (eSec A.A))} (hρ : ρ.IsGen) {k : ℕ} (t : SecA A F k) :
    ∃ c : F, ∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J =
      @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) *
        (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' (Z := (TFK (R := R) F).left) A.isLB z
  obtain ⟨c, hc⟩ := cstH_surj z (sA t (ptSecT A.A 1).left z J' *
    ((val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J')⁻¹).val :)
  refine ⟨c, fun z' J hJ => ?_⟩
  obtain rfl := CoefBasic.pt_eq z z'
  have a₁ := sval_tr (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t
    (ptSecT A.A 1).left hJ hJ'
  have a₂ := val_tr (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) hρ
    (𝟙 _ ≫ (TFK (R := R) F).hom) hJ hJ'
  have e : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left =
      (𝟙 _ ≫ (TFK (R := R) F).hom) ≫ eSec A.A := by
    rw [← Over.comp_left, ptSecT, lift_snd, Category.id_comp]; rfl
  rw [Fin.prod_univ_one, e] at a₁
  rw [Fintype.prod_unique, zpow_one] at a₂
  have hc' : @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) = sA t (ptSecT A.A 1).left z J' *
    ((val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J')⁻¹).val := (cst_eq z c).trans hc
  rw [hc', val_rigT ρ k hJ, val_rigT ρ k hJ', a₂, mul_zpow, Units.val_mul, mul_comm (Units.val (_ ^ _)),
    ← _root_.mul_assoc, Units.inv_mul_cancel_right, mul_comm]
  exact a₁

theorem exists_act_pre (hG : GlobalFnsSt) {k : ℕ} (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (T : SecA A F k) :
    ∃ t : SecA A F k, IsActOf A.A A.L (k : ℤ) θ t T := by
  obtain ⟨ρ, hρ, -⟩ := GlobalTheory.thetaGrp_acts_linearly hG _ A (k : ℤ) (TFK (R := R) F)
  exact ⟨SecM.toSec A.A ((ρ θ).symm (SecM.ofSec A.A T)), (hρ _ _ _).2 ((ρ θ).apply_symm_apply _)⟩

theorem act_zero {I : Ideal R} {D : DegData R I} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {U : UnifPre I D A G} (E : EndU U) {o : GtPtF D.toPre F} (ho : o.IsZero) : E.Act o o := by
  obtain ⟨hb, hv⟩ := (isZero_iff o).1 ho
  have := E.homB
  refine ⟨by rw [hb, MonObj.one_comp], fun χ z J hJ => ?_⟩
  have a := val_corr hJ (E.u_norm χ).2 (TF (R := R) F).hom
  rw [val_pull hJ, val_one] at a
  rw [hv _ z J hJ, hv _ z J hJ, hb, _root_.one_mul]
  exact a.symm

end

theorem exists_pre_coef (hL : LL) {R : Type} [CommRing R] [IsDomain R] [CharZero R] {I : Ideal R} (hA : AdmBase R I)
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) {F : Type} [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] {j : ℕ} (hj : 1 ≤ j) (q : QkPt D.toPre F j) {x : TFK (R := R) F ⟶ A.A}
    (hx : QkToAkU U.toUnifPre F j q x) {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) {g₀ g₁ : GtPtF D.toPre F}
    (hg : g₀.IsAdd q.g g₁) {ω₀ : Frm D.toPre F j g₀.b} (hω₀ : ω₀.IsGen) :
    ∃ θ : ThetaGrp A.A A.L (j : ℤ) (TFK (R := R) F), θ.pt = x ∧ ∃ ω₁ : Frm D.toPre F j g₁.b, ω₁.IsGen ∧
      ∀ T S, U.ExpandsF F j w₀ T S → ∃ t s, IsActOf A.A A.L (j : ℤ) θ t T ∧ U.ExpandsF F j w₀ t s ∧
        ∀ α, coef S g₀ ω₀ (α + q.y) = coef s g₁ ω₁ α := by
  obtain ⟨hp, hθ⟩ := hx w₀ hw₀
  obtain ⟨θ, e, -⟩ := GlobalTheory.TorsionTheta.exists_theta_acts hL.1.kerPow _ A F (jFK (R := R) F) j hj x hp
  obtain ⟨w, hw, H⟩ := hθ θ e
  obtain ⟨ω₁, hω₁, -, K⟩ := GlobalTheory.UT.CoefPhi.coef_phi hL R I hA D F j hj q w hw g₀ g₁ hg ω₀ hω₀
  refine ⟨θ, e, ω₁, hω₁, fun T S hT => ?_⟩
  obtain ⟨t, ht⟩ := exists_act_pre hL.1.globalFns θ T
  obtain ⟨s, hs, -⟩ := ((expBijF_and_expandsF_lin hL R I hA D A G hG U).1 F j hj w₀ hw₀).1 t
  exact ⟨t, s, ht, hs, K 1 j le_rfl (Nat.mul_one j).symm q (one_nsmul _).symm rfl w ω₀ ω₁
    ⟨hw, fun _ _ _ => (pow_one _).symm⟩ ⟨hω₀, fun _ _ _ => (pow_one _).symm⟩ ⟨hω₁, fun _ _ _ => (pow_one _).symm⟩
    s S (H t T s S hs hT ht)⟩

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ E : EndU U.toUnifPre, Function.Injective E.h → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) x, QkToAkU U.toUnifPre F k p x → ∀ g', E.Act p.g g' → ∃ p' : QkPt D.toPre F k, p'.g = g' ∧ QkToAkU U.toUnifPre F k p' (x ≫ E.aA) := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hV ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U E hE k hk p x hx g' hg'
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  have hB := D.tau_bimult
  have := E.homA
  have CV := GlobalTheory.UT.CoefVal.main hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D Q hQ F v hv
  have EV := GlobalTheory.UT.EvalZero.value_at_origin hL V _ hA D A G hG U F
  have LU := GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D A G hG U F
  have MX := GlobalTheory.T.crossRelation_gives_convolution_relation hL V _ hA D A G hG U F E
  have BJ := (expBijF_and_expandsF_lin hL V _ hA D A G hG U).1 F
  have SV := fun Ix => AdicValSum.main V ϖ hϖ F v hv Ix
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D A G hG U F k hk
  obtain ⟨ρ, hρ⟩ := EV.1
  obtain ⟨w₀, hN⟩ := EV.2.1 ρ hρ
  have hw₀ := hN.1
  have hxk : x ^ k = 1 := (hx w₀ hw₀).1
  obtain ⟨p₀, hp₀⟩ := f₂ (x ≫ E.aA) (by rw [← MonObj.pow_comp, hxk, MonObj.one_comp])
  obtain ⟨l', hl', -⟩ := (CV g').1
  obtain ⟨z, hz⟩ := GlobalTheory.exists_rep_mod_shifted_form_small D.toPre.X Q (QForm.bHom hϖ D hQ)
    (fun a b => by rw [QForm.bHom_apply, QForm.bOf]; ring) (QForm.two_Q_eq hϖ D hQ)
    (fun a ha => QForm.Q_pos hϖ D hQ ha) (k • l') k hk p₀.y
  let p₁ : QkPt D.toPre F k := qkMk hB (p₀.y + k • z) (p₀.g + iota hB F z)
    (by rw [nsmul_add, qk_nsmul hB, map_add, map_nsmul])
  have hp₁ : QkToAkU U.toUnifPre F k p₁ (x ≫ E.aA) :=
    (f₁ _ _).2 (hp₀.symm.trans ((f₃ _ _).2 ((equiv_iff hB _ _).2 ⟨z, rfl, rfl⟩)))
  let d : GtPtF D.toPre F := g' - p₁.g
  have hd : d.IsAdd p₁.g g' := (isAdd_iff_eq _ _ _).2 (sub_add_cancel _ _).symm
  obtain ⟨l, hl, -⟩ := (CV d).1
  obtain ⟨l₁, hl₁, -⟩ := (CV p₁.g).1
  have ho : (0 : GtPtF D.toPre F).IsZero := (isZero_iff_eq _).2 rfl
  suffices H : d.IsZero from ⟨p₁, (sub_eq_zero.1 ((isZero_iff_eq _).1 H)).symm, hp₁⟩
  have gu : ∀ (g : GtPtF D.toPre F) (a b : D.toPre.X →+ ℚ), GtV hϖ hv g a → GtV hϖ hv g b → a = b := fun g a b ha hb =>
    (CV g).1.unique ha hb
  have k0 : (0 : ℚ) < k := by exact_mod_cast hk
  refine GlobalTheory.T.smallTorusPoint_keeping_ratios_isZero hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D Q hQ F v hv k hk d 0 l ho hl (fun m => ?_) fun n j hn hj w₁ hw₁ => ?_
  · have e₁ := gu g' l' (l + l₁) hl' ((CV d).2.2.2.1 p₁.g g' l l₁ hd hl hl₁)
    have e₂ := gu p₁.g l₁ ((k : ℚ)⁻¹ • (Int.castAddHom ℚ).comp (QForm.bHom hϖ D hQ p₁.y)) hl₁ (by
      have := (CV p₁.g).2.2.2.2.1 k hk p₁
      convert this using 2 with χ
      simp [QForm.bHom_apply, div_eq_inv_mul])
    have e₃ := hz m
    have e₄ : ((QForm.bHom hϖ D hQ (p₀.y + k • z) m : ℤ) : ℚ) - (k • l') m = -(k * l m) := by
      rw [e₁, e₂]
      simp only [AddMonoidHom.smul_apply, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, Int.coe_castAddHom,
        smul_eq_mul, nsmul_eq_mul]
      show _ - (k : ℚ) * (l m + (k : ℚ)⁻¹ * ((QForm.bHom hϖ D hQ (p₀.y + k • z) m : ℤ) : ℚ)) = _
      field_simp
      ring
    rw [e₄, abs_neg, abs_mul, abs_of_pos k0] at e₃
    exact le_of_mul_le_mul_left e₃ k0
  have up : ∀ (r : QkPt D.toPre F k) (n N : ℕ), N = k * n → ∃ q : QkPt D.toPre F N, q.y = n • r.y ∧ q.g = r.g :=
    fun r n N h => ⟨qkMk hB (n • r.y) r.g (by rw [h, mul_nsmul, qk_nsmul hB, map_nsmul]), rfl, rfl⟩
  have hj1 : 1 ≤ j := hj ▸ Nat.mul_pos hk hn
  obtain ⟨q₁, qy₁, qg₁⟩ := up p₁ n j hj
  obtain ⟨w, hw⟩ := (coef_basic V D.toPre F j d).1
  obtain ⟨θ, hθ, ω, hω, K⟩ := exists_pre_coef hL hA hG U hj1 q₁ (((LU k n j hk hn hj p₁ q₁ _).1 qy₁ qg₁).1 hp₁) hw₀
    (qg₁ ▸ hd) hw
  refine ⟨w, hw, fun S₁ S₂ hS => ?_⟩
  obtain ⟨T₁, hT₁, -⟩ := (BJ j hj1 w₀ hw₀).2 S₁
  obtain ⟨T₂, hT₂, -⟩ := (BJ j hj1 w₀ hw₀).2 S₂
  obtain ⟨n', hn', CR⟩ := GlobalTheory.PullPair.exists_cross hL V A F E.aA E.homA j k hk
  obtain ⟨T₁', T₂', hC, hne⟩ := CR T₁ T₂
  have hj' : 1 ≤ k * n' := Nat.mul_pos hk hn'
  obtain ⟨S₁', hT₁', -⟩ := (BJ _ hj' w₀ hw₀).1 T₁'
  obtain ⟨S₂', hT₂', -⟩ := (BJ _ hj' w₀ hw₀).1 T₂'
  obtain ⟨w₁', hw₁'⟩ := (coef_basic V D.toPre F (k * n') 0).2.1 zero_b
  obtain ⟨q, qy, qg⟩ := up p n' _ rfl
  obtain ⟨θ', hθ', ω', hω', K'⟩ := exists_pre_coef hL hA hG U hj' q (((LU k n' _ hk hn' rfl p q _).1 qy qg).1 hx) hw₀
    (g₀ := 0) (g₁ := p.g) ((isAdd_iff_eq _ _ _).2 (by rw [qg, zero_add])) hw₁'.1
  obtain ⟨t₁, s₁, a₁, e₁, c₁⟩ := K T₁ S₁ hT₁
  obtain ⟨t₂, s₂, a₂, e₂, c₂⟩ := K T₂ S₂ hT₂
  obtain ⟨t₁', s₁', a₁', e₁', c₁'⟩ := K' T₁' S₁' hT₁'
  obtain ⟨t₂', s₂', a₂', e₂', c₂'⟩ := K' T₂' S₂' hT₂'
  have hC' := (GlobalTheory.cross_iff_of_isActOf hL V A F E.aA E.homA j _ θ θ' (by rw [hθ, hθ']) _ _ _ _ _ _ _ _
    a₁ a₂ a₁' a₂').2 hC
  have nl : ∀ (g : GtPtF D.toPre F) (i : ℕ), 1 ≤ i → ∀ (u : Frm D.toPre F i g.b) (s : Fam D.toPre F i), u.IsGen →
      NullV v (coef s g u) := fun g i hi u s hu => ((CV g).2.2.2.2.2.2 i hi u s hu).1
  refine GlobalTheory.UT.sumV_cancel F v D.toPre.X E.h hE (coef S₁ 0 w₁) (coef S₂ 0 w₁) (coef S₁ d w) (coef S₂ d w)
    (coef S₁' 0 w₁') (coef S₂' 0 w₁') (nl _ _ hj1 _ _ hw₁.1) (nl _ _ hj1 _ _ hw₁.1) (nl _ _ hj1 _ _ hw)
    (nl _ _ hj1 _ _ hw) (nl _ _ hj' _ _ hw₁'.1) (nl _ _ hj' _ _ hw₁'.1)
    (fun α => (SV _ _ _ (MX w₀ hw₀ j _ hj1 hj' _ _ _ _ _ _ _ _ hT₁ hT₂ hT₁' hT₂' hC 0 0 (act_zero E ho) w₁ w₁'
      hw₁.1 hw₁'.1 α)).1)
    (sumV_shift v E.h q₁.y q.y c₁ c₂ c₁' c₂' fun α => (SV _ _ _ (MX w₀ hw₀ j _ hj1 hj' _ _ _ _ _ _ _ _ e₁ e₂ e₁' e₂'
      hC' p.g g' hg' ω ω' hω hω' α)).1) fun h0 => ?_
  obtain ⟨c, hc⟩ := exists_value hρ T₂
  obtain ⟨c', hc'⟩ := exists_value hρ T₂'
  have σ := (SV _ _ _ (EV.2.2 w₀ ρ hN j T₂ S₂ hT₂ 0 w₁ ho hw₁ c hc)).1
  have σ' := (SV _ _ _ (EV.2.2 w₀ ρ hN _ T₂' S₂' hT₂' 0 w₁' ho hw₁' c' hc')).1
  rw [h0] at σ'
  obtain rfl := eq_zero_of_sumV_zero v σ'
  obtain ⟨y⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := V) F).left) A.isLB y
  refine hne (fun y J hJ h => hS ?_) y J hJ ((hc' y J hJ).trans ?_)
  · have e : cstH (R := V) y c = 0 :=
      (cst_eq y c).symm.trans ((Units.mul_left_eq_zero _).1 ((hc y J hJ).symm.trans h))
    obtain rfl : c = 0 := cstH_inj y (e.trans (map_zero _).symm)
    exact σ
  · exact mul_eq_zero_of_left ((cst_eq y 0).trans (map_zero _)) _

end GlobalTheory.UT.EndTors
end
