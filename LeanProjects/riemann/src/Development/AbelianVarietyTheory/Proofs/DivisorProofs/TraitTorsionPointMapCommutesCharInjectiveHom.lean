import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointEndomorphismImageEqMovedGtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionMapWelldefinedAdditiveCharactersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedConvolutionCancelInjectiveLatticeHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionCrossRelationIffOfThetaActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrossRelationSectionsAmpleSourcePowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossRelationHomGivesExpansionTermConvolutionRelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.Mum.Two.KeyDvr
open GlobalTheory.TorusExt GlobalTheory.UT.CoefBasic GlobalTheory.UT.EndTors
attribute [local instance] gtGroup

theorem act_zero₂ {R : Type} [CommRing R] [IsDomain R] {D₁ D₂ : DegPre R} (b : D₁.P.A ⟶ D₂.P.A) [IsMonHom b]
    (h : D₂.X →+ D₁.X) {F : Type} [Field F] [Algebra (FractionRing R) F] {o₁ : GtPtF D₁ F} {o₂ : GtPtF D₂ F}
    (h₁ : o₁.IsZero) (h₂ : o₂.IsZero) : Act D₁ D₂ b h o₁ o₂ := by
  obtain ⟨hb₁, hv₁⟩ := (isZero_iff o₁).1 h₁
  obtain ⟨hb₂, hv₂⟩ := (isZero_iff o₂).1 h₂
  refine ⟨by rw [hb₂, hb₁, MonObj.one_comp], fun χ u hu z J hJ => ?_⟩
  rw [hv₂ _ z _ ((isPart_inr (M₁ := D₁.P.L) (M₂ := D₂.P.L)).good hJ),
    hv₁ _ z _ ((isPart_inl (M₁ := D₁.P.L) (M₂ := D₂.P.L)).good hJ), hb₁, _root_.one_mul]
  exact (hu.2 _ (TF (R := R) F).hom z J hJ).symm

theorem sumV_shift₂ {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {X X' : Type} [AddCommGroup X]
    [AddCommGroup X'] (h : X' →+ X) (y : X') (y' : X) {B₁ B₂ b₁ b₂ : X' → F} {C₁ C₂ c₁ c₂ : X → F}
    (hB₁ : ∀ α, B₁ (α + y) = b₁ α) (hB₂ : ∀ α, B₂ (α + y) = b₂ α)
    (hC₁ : ∀ α, C₁ (α + y') = c₁ α) (hC₂ : ∀ α, C₂ (α + y') = c₂ α)
    (H : ∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => b₁ p.1.1 * c₂ p.1.2 - b₂ p.1.1 * c₁ p.1.2) 0)
    (α : X) :
    SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0 := by
  refine sumV_equiv v (Equiv.subtypeEquiv ((Equiv.addRight y).prodCongr (Equiv.addRight y')) fun p => ?_) (fun p => ?_)
    (H (α - h y - y'))
  · simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight, map_add]
    constructor
    · intro e; rw [show α = α - h y - y' + h y + y' by abel, ← e]; abel
    · intro e; rw [← e]; abel
  · simp only [Equiv.subtypeEquiv_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.coe_addRight,
      hB₁, hB₂, hC₁, hC₂]

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (A₁ A₂ : PolAV (Sp (FractionRing V))) (G₁ G₂ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif (maximalIdeal V) D₁ A₁ G₁) (U₂ : Unif (maximalIdeal V) D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → Function.Injective h → Key U₁.toUnifPre U₂.toUnifPre c b h F := by
  intro V _ _ _ _ hV ϖ hϖ F _ _ _ v hv D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ hG₁ hG₂ U₁ U₂ a c b h hc hgen hlin hcoord hE
    k hk p x hx g' hg'
  have hL : LL := GlobalTheory.firstFiveLaws
  obtain ⟨-, h₁, h₂, h₃, h₄⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  choose Q hQ' using QForm.exists_QVal hϖ D₂
  have hQ : QForm.IsQ D₂.toPre ϖ Q := hQ'
  have hB := D₂.tau_bimult
  have := hc
  have := hlin.2.1
  have CV := GlobalTheory.UT.CoefVal.main hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D₂ Q hQ F v hv
  have EV₁ := GlobalTheory.UT.EvalZero.value_at_origin hL V _ hA D₁ A₁ G₁ hG₁ U₁ F
  have EV₂ := GlobalTheory.UT.EvalZero.value_at_origin hL V _ hA D₂ A₂ G₂ hG₂ U₂ F
  have LU₁ := GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D₁ A₁ G₁ hG₁ U₁ F
  have LU₂ := GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D₂ A₂ G₂ hG₂ U₂ F
  have BJ₁ := (expBijF_and_expandsF_lin hL V _ hA D₁ A₁ G₁ hG₁ U₁).1 F
  have BJ₂ := (expBijF_and_expandsF_lin hL V _ hA D₂ A₂ G₂ hG₂ U₂).1 F
  have SV := fun Ix => AdicValSum.main V ϖ hϖ F v hv Ix
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA D₂ A₂ G₂ hG₂ U₂ F k hk
  obtain ⟨ρ₁, hρ₁⟩ := EV₁.1
  obtain ⟨w₀₁, hN₁⟩ := EV₁.2.1 ρ₁ hρ₁
  obtain ⟨ρ₂, hρ₂⟩ := EV₂.1
  obtain ⟨w₀₂, hN₂⟩ := EV₂.2.1 ρ₂ hρ₂
  have hw₀₁ := hN₁.1
  have hw₀₂ := hN₂.1
  have hxk : x ^ k = 1 := (hx w₀₁ hw₀₁).1
  obtain ⟨p₀, hp₀⟩ := f₂ (x ≫ c) (by rw [← MonObj.pow_comp, hxk, MonObj.one_comp])
  obtain ⟨l', hl', -⟩ := (CV g').1
  obtain ⟨z, hz⟩ := GlobalTheory.exists_rep_mod_shifted_form_small D₂.toPre.X Q (QForm.bHom hϖ D₂ hQ)
    (fun a₀ b₀ => by rw [QForm.bHom_apply, QForm.bOf]; ring) (QForm.two_Q_eq hϖ D₂ hQ)
    (fun a ha => QForm.Q_pos hϖ D₂ hQ ha) (k • l') k hk p₀.y
  let p₁ : QkPt D₂.toPre F k := qkMk hB (p₀.y + k • z) (p₀.g + iota hB F z)
    (by rw [nsmul_add, qk_nsmul hB, map_add, map_nsmul])
  have hp₁ : QkToAkU U₂.toUnifPre F k p₁ (x ≫ c) :=
    (f₁ _ _).2 (hp₀.symm.trans ((f₃ _ _).2 ((equiv_iff hB _ _).2 ⟨z, rfl, rfl⟩)))
  let d : GtPtF D₂.toPre F := g' - p₁.g
  have hd : d.IsAdd p₁.g g' := (isAdd_iff_eq _ _ _).2 (sub_add_cancel _ _).symm
  obtain ⟨l, hl, -⟩ := (CV d).1
  obtain ⟨l₁, hl₁, -⟩ := (CV p₁.g).1
  have ho : (0 : GtPtF D₂.toPre F).IsZero := (isZero_iff_eq _).2 rfl
  have ho₁ : (0 : GtPtF D₁.toPre F).IsZero := (isZero_iff_eq _).2 rfl
  suffices H : d.IsZero from ⟨p₁, (sub_eq_zero.1 ((isZero_iff_eq _).1 H)).symm, hp₁⟩
  have gu : ∀ (g : GtPtF D₂.toPre F) (a b : D₂.toPre.X →+ ℚ), GtV hϖ hv g a → GtV hϖ hv g b → a = b :=
    fun g a b ha hb => (CV g).1.unique ha hb
  have k0 : (0 : ℚ) < k := by exact_mod_cast hk
  refine GlobalTheory.T.smallTorusPoint_keeping_ratios_isZero hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D₂ Q hQ F v hv k hk d 0 l ho hl (fun m => ?_) fun n j hn hj w₁ hw₁ => ?_
  · have e₁ := gu g' l' (l + l₁) hl' ((CV d).2.2.2.1 p₁.g g' l l₁ hd hl hl₁)
    have e₂ := gu p₁.g l₁ ((k : ℚ)⁻¹ • (Int.castAddHom ℚ).comp (QForm.bHom hϖ D₂ hQ p₁.y)) hl₁ (by
      have := (CV p₁.g).2.2.2.2.1 k hk p₁
      convert this using 2 with χ
      simp [QForm.bHom_apply, div_eq_inv_mul])
    have e₃ := hz m
    have e₄ : ((QForm.bHom hϖ D₂ hQ (p₀.y + k • z) m : ℤ) : ℚ) - (k • l') m = -(k * l m) := by
      rw [e₁, e₂]
      simp only [AddMonoidHom.smul_apply, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, Int.coe_castAddHom,
        smul_eq_mul, nsmul_eq_mul]
      show _ - (k : ℚ) * (l m + (k : ℚ)⁻¹ * ((QForm.bHom hϖ D₂ hQ (p₀.y + k • z) m : ℤ) : ℚ)) = _
      field_simp
      ring
    rw [e₄, abs_neg, abs_mul, abs_of_pos k0] at e₃
    exact le_of_mul_le_mul_left e₃ k0
  have up₂ : ∀ (r : QkPt D₂.toPre F k) (n N : ℕ), N = k * n → ∃ q : QkPt D₂.toPre F N, q.y = n • r.y ∧ q.g = r.g :=
    fun r n N h => ⟨qkMk hB (n • r.y) r.g (by rw [h, mul_nsmul, qk_nsmul hB, map_nsmul]), rfl, rfl⟩
  have hB₁ := D₁.tau_bimult
  have up₁ : ∀ (r : QkPt D₁.toPre F k) (n N : ℕ), N = k * n → ∃ q : QkPt D₁.toPre F N, q.y = n • r.y ∧ q.g = r.g :=
    fun r n N h => ⟨qkMk hB₁ (n • r.y) r.g (by rw [h, mul_nsmul, qk_nsmul hB₁, map_nsmul]), rfl, rfl⟩
  have hj1 : 1 ≤ j := hj ▸ Nat.mul_pos hk hn
  obtain ⟨q₁, qy₁, qg₁⟩ := up₂ p₁ n j hj
  obtain ⟨w, hw⟩ := (coef_basic V D₂.toPre F j d).1
  obtain ⟨θ, hθ, ω, hω, K⟩ := exists_pre_coef hL hA hG₂ U₂ hj1 q₁
    (((LU₂ k n j hk hn hj p₁ q₁ _).1 qy₁ qg₁).1 hp₁) hw₀₂ (qg₁ ▸ hd) hw
  refine ⟨w, hw, fun S₁ S₂ hS => ?_⟩
  obtain ⟨T₁, hT₁, -⟩ := (BJ₂ j hj1 w₀₂ hw₀₂).2 S₁
  obtain ⟨T₂, hT₂, -⟩ := (BJ₂ j hj1 w₀₂ hw₀₂).2 S₂
  obtain ⟨n', hn', CR⟩ := GlobalTheory.T.exists_crossRelation_sections_ample_source_power V A₁ A₂ F c hc j k hk
  obtain ⟨T₁', T₂', hC, hne⟩ := CR T₁ T₂
  have hj' : 1 ≤ k * n' := Nat.mul_pos hk hn'
  obtain ⟨S₁', hT₁', -⟩ := (BJ₁ _ hj' w₀₁ hw₀₁).1 T₁'
  obtain ⟨S₂', hT₂', -⟩ := (BJ₁ _ hj' w₀₁ hw₀₁).1 T₂'
  obtain ⟨w₁', hw₁'⟩ := (coef_basic V D₁.toPre F (k * n') 0).2.1 zero_b
  obtain ⟨q, qy, qg⟩ := up₁ p n' _ rfl
  obtain ⟨θ', hθ', ω', hω', K'⟩ := exists_pre_coef hL hA hG₁ U₁ hj' q
    (((LU₁ k n' _ hk hn' rfl p q _).1 qy qg).1 hx) hw₀₁
    (g₀ := 0) (g₁ := p.g) ((isAdd_iff_eq _ _ _).2 (by rw [qg, zero_add])) hw₁'.1
  obtain ⟨t₁, s₁, a₁, e₁, c₁⟩ := K T₁ S₁ hT₁
  obtain ⟨t₂, s₂, a₂, e₂, c₂⟩ := K T₂ S₂ hT₂
  obtain ⟨t₁', s₁', a₁', e₁', c₁'⟩ := K' T₁' S₁' hT₁'
  obtain ⟨t₂', s₂', a₂', e₂', c₂'⟩ := K' T₂' S₂' hT₂'
  have hC' := (GlobalTheory.T.thetaSectionCrossRelation_iff_of_thetaAction V A₁ A₂ F c hc j _ θ θ' (by rw [hθ, hθ']) _ _ _ _ _ _ _ _
    a₁ a₂ a₁' a₂').2 hC
  have nl₂ : ∀ (g : GtPtF D₂.toPre F) (i : ℕ), 1 ≤ i → ∀ (u : Frm D₂.toPre F i g.b) (s : Fam D₂.toPre F i), u.IsGen →
      NullV v (coef s g u) := fun g i hi u s hu => ((CV g).2.2.2.2.2.2 i hi u s hu).1
  choose Q₁ hQ₁' using QForm.exists_QVal hϖ D₁
  have hQ₁ : QForm.IsQ D₁.toPre ϖ Q₁ := hQ₁'
  have CV₁ := GlobalTheory.UT.CoefVal.main hL h₁ h₂ h₃ h₄ V hV ϖ hϖ D₁ Q₁ hQ₁ F v hv
  have nl₁ : ∀ (g : GtPtF D₁.toPre F) (i : ℕ), 1 ≤ i → ∀ (u : Frm D₁.toPre F i g.b) (s : Fam D₁.toPre F i), u.IsGen →
      NullV v (coef s g u) := fun g i hi u s hu => ((CV₁ g).2.2.2.2.2.2 i hi u s hu).1
  have MX := GlobalTheory.T.crossRelation_hom_gives_expansionTerm_convolution_rel V _ hA D₁ D₂ A₁ A₂ G₁ G₂ hG₁ hG₂ U₁ U₂ a c b h hc hgen hlin hcoord F w₀₁ w₀₂ hw₀₁ hw₀₂
  refine GlobalTheory.T.valuedConvolution_cancel_injective_latticeHom F v D₁.toPre.X D₂.toPre.X h hE (coef S₁ 0 w₁) (coef S₂ 0 w₁) (coef S₁ d w) (coef S₂ d w)
    (coef S₁' 0 w₁') (coef S₂' 0 w₁') (nl₂ _ _ hj1 _ _ hw₁.1) (nl₂ _ _ hj1 _ _ hw₁.1) (nl₂ _ _ hj1 _ _ hw)
    (nl₂ _ _ hj1 _ _ hw) (nl₁ _ _ hj' _ _ hw₁'.1) (nl₁ _ _ hj' _ _ hw₁'.1)
    (fun α => (SV _ _ _ (MX j _ hj1 hj' _ _ _ _ _ _ _ _ hT₁ hT₂ hT₁' hT₂' hC 0 0 (act_zero₂ b h ho₁ ho) w₁ w₁'
      hw₁.1 hw₁'.1 α)).1)
    (sumV_shift₂ v h q₁.y q.y c₁ c₂ c₁' c₂' fun α => (SV _ _ _ (MX j _ hj1 hj' _ _ _ _ _ _ _ _ e₁ e₂ e₁' e₂'
      hC' p.g g' hg' ω ω' hω hω' α)).1) fun h0 => ?_
  obtain ⟨cc, hcc⟩ := exists_value hρ₂ T₂
  obtain ⟨cc', hcc'⟩ := exists_value hρ₁ T₂'
  have σ := (SV _ _ _ (EV₂.2.2 w₀₂ ρ₂ hN₂ j T₂ S₂ hT₂ 0 w₁ ho hw₁ cc hcc)).1
  have σ' := (SV _ _ _ (EV₁.2.2 w₀₁ ρ₁ hN₁ _ T₂' S₂' hT₂' 0 w₁' ho₁ hw₁' cc' hcc')).1
  rw [h0] at σ'
  obtain rfl := eq_zero_of_sumV_zero v σ'
  obtain ⟨y⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := V) F).left) A₁.isLB y
  refine hne (fun y J hJ h => hS ?_) y J hJ ((hcc' y J hJ).trans ?_)
  · have e : cstH (R := V) y cc = 0 :=
      (cst_eq y cc).symm.trans ((Units.mul_left_eq_zero _).1 ((hcc y J hJ).symm.trans h))
    obtain rfl : cc = 0 := cstH_inj y (e.trans (map_zero _).symm)
    exact σ
  · exact mul_eq_zero_of_left ((cst_eq y 0).trans (map_zero _)) _

end GlobalTheory.Mum.Two.KeyDvr
