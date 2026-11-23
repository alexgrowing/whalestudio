import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConvOfCrossAny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExhaustOfLabels
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

noncomputable section

namespace GlobalTheory.Poinc.Tors.AnyField
open GlobalTheory.TorsionAnyChar

def FieldUF (p : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G],
    Unif I D A G → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], Prop) : Prop :=
  AnyU fun {R} _ _ {_} {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], p U F

def FieldD (p : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}, DegData R I →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I)
    (F : Type) [Field F] [Algebra (FractionRing R) F], p D F

section
open GlobalTheory.UT.CoefBasic GlobalTheory.UT.CoefPhi

theorem coefPhi_field : LL → FieldD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), w.IsGen → ∀ (g₀ g₁ : GtPtF D.toPre F), g₀.IsAdd p.g g₁ → ∀ ω₀ : Frm D.toPre F k g₀.b, ω₀.IsGen → ∃ ω₁ : Frm D.toPre F k g₁.b, ω₁.IsGen ∧ (g₀.IsZero → FrmOne ω₀ → ∀ z J, Good D.toPre.P.L z J → val ω₁ (𝟙 _) z J = val w (𝟙 _) z J) ∧ ∀ (n N : ℕ), 1 ≤ n → N = k * n → ∀ (q : QkPt D.toPre F N), q.y = n • p.y → q.g = p.g → ∀ (wN : Frm D.toPre F N q.g.b) (w₀ : Frm D.toPre F N g₀.b) (w₁ : Frm D.toPre F N g₁.b), (wN.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val wN (𝟙 _) z J = val w (𝟙 _) z J ^ n) → (w₀.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w₀ (𝟙 _) z J = val ω₀ (𝟙 _) z J ^ n) → (w₁.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w₁ (𝟙 _) z J = val ω₁ (𝟙 _) z J ^ n) → ∀ s s' : Fam D.toPre F N, PhiRel D.toPre F N q wN s s' → ∀ α, coef s' g₀ w₀ (α + q.y) = coef s g₁ w₁ α := by
  intro hL R _ _ I _ D F _ _ k _ p w hw g₀ g₁ hadd ω₀ h₀
  obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
  obtain ⟨ω₁, h₁, v₁⟩ := exists_frame p w hw g₀ ω₀ h₀ g₁.b hb
  refine ⟨ω₁, h₁, fun hz ho z J hJ => ?_, ?_⟩
  · have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
    obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 hz
    have c : cubN (th D.toPre z J) k 1 p.g.b g₀.b = 1 := by rw [z₁, C.N_one]
    rw [v₁ z J hJ, ho.2 z J hJ, z₂ _ z J hJ, c, _root_.one_mul, _root_.mul_one, _root_.mul_one]
  · rintro n _ _ rfl ⟨qy, qg, qe⟩ hy hg wN w₀ w₁ ⟨hN, vN⟩ ⟨-, v₀⟩ ⟨hw₁, vw₁⟩ s s' hΦ α
    dsimp only at hy hg
    subst hy hg
    have H := (phiRel_iff hL.1.globalFns _ wN hN s s').1 hΦ
    refine coef_eq fun z J hJ => ?_
    have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
    have e₁ := H α _ rfl _ (lift (𝟙 (TF (R := R) F)) g₀.b) z J hJ
    have t : lift (𝟙 (TF (R := R) F)) g₀.b ≫ DegPre.trPt D.toPre F p.g.b = lift (𝟙 (TF (R := R) F)) g₁.b := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, tr_fst, lift_fst, lift_fst]
      · rw [lift_snd, hb, Category.assoc]
        refine (congrArg (_ ≫ ·) (tr_pr D.toPre F p.g.b)).trans ?_
        rw [MonObj.comp_mul, lift_fst_assoc, Category.id_comp, lift_snd]
    dsimp only at e₁ vN
    rw [t, uVal, lift_fst_assoc, lift_fst, lift_snd, Category.id_comp, Over.id_left, val_mul hJ, vN z J hJ,
      CoefPhi.cubN_mul C] at e₁
    have e₂ := gt_nsmul (𝟙 (TF (R := R) F)) hJ g₀ α p.y n
    rw [Category.id_comp, Over.id_left, cPoint_y] at e₂
    have e₃ := hs α z J hJ
    rw [isCoef_coef g₁ hw₁ α s z J hJ]
    dsimp only
    rw [e₁, v₀ z J hJ, vw₁ z J hJ, v₁ z J hJ]
    simp only [_root_.mul_assoc, ← Units.val_mul]
    congr 2
    apply Additive.ofMul.injective
    have a₂ := congrArg Additive.ofMul e₂
    have a₃ := congrArg Additive.ofMul e₃
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at a₂ a₃ ⊢
    linear_combination (norm := module) a₃ - a₂

end

section
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw GlobalTheory.SecAdicSum

theorem sumF_field : LL → FieldD fun {R} _ _ {I} D F _ _ => ∀ (K : Type) [Fintype K] (φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) (ε : K → ℤ) (Ix : Type) (n : Ix → LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (n₀ : LB.Sec (LB.LinComb D.toPre.P.L φ ε)), (∀ e : ℕ, ∃ S : Finset Ix, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → (∀ i ∉ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J = 0) ∧ sval n₀ (r ≫ (D.toPre.prBe I e).left) z J = ∑ i ∈ S, sval (n i) (r ≫ (D.toPre.prBe I e).left) z J) → ∀ (b : TF (R := R) F ⟶ D.toPre.P.A) (τ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => b.left ≫ φ i) ε)), τ.IsGen → ∀ (x : Ix → F) (x₀ : F), (∀ z J, Good D.toPre.P.L z J → (∀ i, sval (n i) b.left z J = cst F z (x i) * (val τ (𝟙 _) z J).val) ∧ sval n₀ b.left z J = cst F z x₀ * (val τ (𝟙 _) z J).val) → SumF I F x x₀ := by
  intro _ R _ _ I hR D F _ _ K _ φ ε Ix n n₀ hS b τ _ x x₀ hx
  have := hR.1
  have := D.toPre.P.isAb.smooth
  have hL := D.toPre.P.isLB
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_noetherian R _ D.toPre.P.A.hom inferInstance
    (GlobalTheory.AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ (LB.isLB_linComb hL φ ε)
  choose v hv hv' using fun i => exists_vec P (n i)
  obtain ⟨v₀, hv₀, hv₀'⟩ := exists_vec P n₀
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' hL z
  obtain ⟨i₀, hi₀⟩ := exists_mem P (b.left z)
  let t := trF φ ε b.left z (P.ch i₀) (fun k => J (b.left ≫ φ k)) * val τ (𝟙 _) z J
  choose y hy using fun k => CoefBasic.cstH_surj z (gs b.left z _ (P.u k i₀) * (t⁻¹).val)
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  let ev : (Fin P.a → R) →ₗ[R] F := Fintype.linearCombination R y
  have key : ∀ (s : LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (w : Fin P.a → R) (c : F),
      (∀ i, AbLaw.rs _ (P.le i) (s.f (P.ch i)) = loc₀ P w i) →
      sval s b.left z J = UT.cst F z c * (val τ (𝟙 _) z J).val → c = ev w := fun s w c h₁ h₂ => by
    have e := gs_loc₀ P h₁ b.left z hi₀ hJ
    rw [h₂, mul_left_comm, ← Units.val_mul, CoefBasic.cst_eq] at e
    refine CoefBasic.cstH_inj (R := R) z ?_
    have e' : CoefBasic.cstH z c = gs b.left z _ (loc₀ P w i₀) * (t⁻¹).val :=
      (Units.eq_mul_inv_iff_mul_eq t).2 e.symm
    have hs : ∀ a : Fin P.a → Γ(D.toPre.P.A.left, P.W i₀), gs b.left z _ (∑ k, a k) = ∑ k, gs b.left z _ (a k) :=
      fun a => by simp only [gs_eq b.left z _ hi₀, map_sum]
    rw [e', loc₀, hs, Finset.sum_mul]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (map_sum _ (fun k => w k • y k) _).symm
    rw [gs_mul b.left z _ hi₀, gs_cst_point b z _ hi₀, _root_.mul_assoc, ← hy, ← map_mul, ← Algebra.smul_def]
    rfl
  obtain rfl : x = fun i => ev (v i) := funext fun i => key _ _ _ (hv' i) ((hx z J hJ).1 i)
  obtain rfl : x₀ = ev v₀ := key _ _ _ hv₀' (hx z J hJ).2
  refine sumI_of_ker I P.D₀ ev v v₀ hv hv₀ fun e => ?_
  obtain ⟨S, hS⟩ := hS e
  refine ⟨S, fun T hT k => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (comp_eq_zero P
    (IsPullback.of_hasPullback D.toPre.P.A.hom (thick R I e)) (v₀ - ∑ i ∈ T, v i) ?_ fun i p hp => ?_) k)⟩
  · simp only [Matrix.mulVec_sub, Matrix.mulVec_sum, hv, hv₀, Finset.sum_const_zero, sub_zero]
  · obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' hL p
    obtain ⟨h₁, h₂⟩ := hS _ (𝟙 _) p J' hJ'
    rw [Category.id_comp] at h₁ h₂
    have h₃ := h₂.trans (Finset.sum_subset hT fun j _ hj => h₁ j hj)
    have e₀ := gs_loc₀ P hv₀' _ p hp hJ'
    have e₁ := fun j => gs_loc₀ P (hv' j) _ p hp hJ'
    rw [gs_eq _ p _ hp] at e₀
    simp only [gs_eq _ p _ hp] at e₁
    rw [loc₀_sub_sum, gs_eq _ p _ hp, map_sub, map_sub, map_sum, map_sum, e₀, Finset.sum_congr rfl fun j _ => e₁ j,
      ← Finset.mul_sum]
    exact sub_eq_zero.2 (congrArg _ h₃)

end

section
open GlobalTheory.FieldBaseChange GlobalTheory.UT.ProdConv

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem point_field (hL : LL) (hR : AdmBase R I) {k l m : ℕ} (r : R) {σ : H0 U.LG.L k}
    {σ' : H0 U.LG.L l} {σ'' : H0 U.LG.L m} (hm : m = k + l)
    {f : ∀ α, D.toPre.SecB k α} {f' : ∀ α, D.toPre.SecB l α} {f'' : ∀ α, D.toPre.SecB m α}
    (h : ∀ e, U.ExpandsAt e k σ f) (h' : ∀ e, U.ExpandsAt e l σ' f') (h'' : ∀ e, U.ExpandsAt e m σ'' f'')
    (hσ : ∀ (Z : Scheme.{0}) (q : Z ⟶ G.left) (z : Z) (j), q z ∈ U.LG.L.U j →
      sv U m σ'' q z j = constVal (q ≫ G.hom) z r * (sv U k σ q z j * sv U l σ' q z j))
    (g : GtPtF D.toPre F) {w : Frm D.toPre F k g.b} {w' : Frm D.toPre F l g.b} {w'' : Frm D.toPre F m g.b}
    (hw : w''.IsGen) (hww : ∀ z J, Good D.toPre.P.L z J → val w'' (𝟙 _) z J = val w (𝟙 _) z J * val w' (𝟙 _) z J)
    {x x' : D.toPre.X → F} (hx : ∀ χ, IsTerm g w (f χ) (x χ)) (hx' : ∀ χ, IsTerm g w' (f' χ) (x' χ))
    (α : D.toPre.X) {x'' : F} (hx'' : IsTerm g w'' (f'' α) x'') :
    SumF I F (fun χ => algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) * (x χ * x' (α - χ))) x'' := by
  subst hm
  choose p hp using fun α β => exists_isProd r k l (add_sub_cancel β α) (f β) (f' (α - β))
  obtain ⟨τ, hτ, vτ⟩ := exists_frame g hw α
  refine sumF_field hL R I hR D F (Fin 4) (D.toPre.famφB α) (DegPre.famε (k + l)) D.toPre.X (p α) (f'' α)
    (fun e => level U e r rfl (h e) (h' e) (h'' e) hσ p hp α) g.b τ hτ _ _ fun z J hJ => ⟨fun χ => ?_, ?_⟩
  · have b := gt_mul (𝟙 (TF (R := R) F)) hJ g χ (α - χ)
    rw [add_sub_cancel, Category.id_comp, Over.id_left] at b
    rw [hp α χ _ g.b z J hJ, vτ z J hJ, constVal_TF, hww z J hJ, CoefBasic.cst_eq z (_ * _), map_mul, map_mul,
      ← CoefBasic.cst_eq, ← CoefBasic.cst_eq, ← CoefBasic.cst_eq]
    exact alg_prod _ (hx χ z J hJ) (hx' (α - χ) z J hJ) b
  · rw [vτ z J hJ]
    exact alg_term (hx'' z J hJ)

end

section
open GlobalTheory.FieldBaseChange GlobalTheory.UT.ProdConv

theorem prodConv_field : LL → FieldUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k k' k'' : ℕ), 1 ≤ k → 1 ≤ k' → k'' = k + k' → ∀ (t : SecA A F k) (t' : SecA A F k') (t'' : SecA A F k'') s s' s'', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → U.ExpandsF F k'' w₀ t'' s'' → (∀ z J, Good A.L z J → sA t'' (𝟙 _) z J = sA t (𝟙 _) z J * sA t' (𝟙 _) z J) → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b) (w' : Frm D.toPre F k' g.b) (w'' : Frm D.toPre F k'' g.b), w.IsGen → w'.IsGen → w''.IsGen → (∀ z J, Good D.toPre.P.L z J → val w'' (𝟙 _) z J = val w (𝟙 _) z J * val w' (𝟙 _) z J) → ∀ α, SumF I F (fun χ => coef s g w χ * coef s' g w' (α - χ)) (coef s'' g w'' α) := by
  intro hL R _ _ I hR D A G _ _ _ U F _ _ w₀ hw₀ k k' k'' hk hk' hm t t' t'' s s' s'' h h' h'' ht g w w' w'' hw hw' hw''
    hww α
  have hG := hL.1.globalFns
  have hk'' : 1 ≤ k'' := by omega
  obtain ⟨v, a, b⟩ := h
  obtain ⟨v', a', b'⟩ := h'
  obtain ⟨v'', a'', b''⟩ := h''
  obtain ⟨n, c, x, hx, e₁, e₂⟩ := (expandsG_iff U.toUnifPre F k v s).1 b
  obtain ⟨n', c', x', hx', e₁', e₂'⟩ := (expandsG_iff U.toUnifPre F k' v' s').1 b'
  obtain ⟨u, hu⟩ := exists_powMul A.isLB (q := (snd (TFK (R := R) F) A.A).left) hm t t'
  obtain rfl : t'' = u := sec_ext' A.isLB fun y J hJ => (ht y J hJ).trans (hu _ (𝟙 _) y _ (hJ (𝟙 _ ≫ _))).symm
  choose τ hτ using fun p : Fin n × Fin n' => exists_powMul U.LG.isLB (q := 𝟙 G.left) hm (x p.1).1 (x' p.2).1
  choose Φ hΦ using fun p => ((U.expand k'' hk'').1 (genericSec U.toUnifPre k'' (τ p))).exists
  choose r hr y hy d₁ d₂ using fun p => (expands_iff U.toUnifPre k'' _ _).1 (hΦ p)
  have hr' : ∀ p, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (r p)) ≠ 0 := fun p => by
    rw [map_ne_zero]; exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 (hr p)
  have hyτ : ∀ p, (y p).1 = r p • (show IntSec U.toUnifPre k'' from τ p) := fun p =>
    genericSec_injective U.toUnifPre k'' ((d₁ p).trans (map_smulₛₗ _ _ _).symm)
  have hv : v'' = (∑ p : Fin n × Fin n', (c p.1 * c' p.2) • extendSec U.toUnifPre F k'' (genericSec U.toUnifPre k'' (τ p)) :
      GroupSec U.toUnifPre F k'') := by
    refine powVal_ext U.LG.isLB fun z i hi => ?_
    obtain ⟨i₁, hi₁⟩ := exists_chart A.isLB
      (U.gen.hom.left ((snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left z))
    have m := (isoRelM_iff _ _ _ _ a.1 _ a.2.1 _ _).1 a _ (𝟙 _) z i i₁ hi hi₁
    have m' := (isoRelM_iff _ _ _ _ a'.1 _ a'.2.1 _ _).1 a' _ (𝟙 _) z i i₁ hi hi₁
    have m'' := (isoRelM_iff _ _ _ _ a''.1 _ a''.2.1 _ _).1 a'' _ (𝟙 _) z i i₁ hi hi₁
    have b₁ : (snd (TFK (R := R) F) A.A).left ((𝟙 _ ≫ (U.genF F).left) z) ∈ A.L.U i₁ :=
      (congrArg (fun q => q z ∈ A.L.U i₁) a.1).mpr hi₁
    have m₀ := hu _ _ z i₁ b₁
    rw [Category.comp_id] at m m' m''
    have w₁ := (congrArg (fun q => powVal q (𝟙 _) z i) e₁).trans (powVal_comb U.toUnifPre c (fun p => (x p).1) z hi)
    have w₂ := (congrArg (fun q => powVal q (𝟙 _) z i) e₁').trans (powVal_comb U.toUnifPre c' (fun p => (x' p).1) z hi)
    refine Eq.trans ?_ (powVal_comb U.toUnifPre _ τ z hi).symm
    have w₃ : powVal v'' (𝟙 _) z i = powVal v (𝟙 _) z i * powVal v' (𝟙 _) z i := by
      rw [m, m', m'', m₀, hm, Nat.cast_add, zpow_add, Units.val_mul]; ring
    rw [w₃, w₁, w₂, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have cm : constVal (groupBase G F) z (c p * c' q) = constVal (groupBase G F) z (c p) * constVal (groupBase G F) z (c' q) :=
      (congrArg (gs _ z ⊤) (map_mul _ _ _)).trans (gs_mul _ z ⊤ trivial _ _)
    rw [hτ (p, q) _ (UnifPre.gFK (G := G) F) z i hi, cm]
    ring
  have hs : ∀ β, famProj D.toPre F k'' β (∑ p : Fin n × Fin n', (c p.1 * c' p.2) • famPull D.toPre (FractionRing R) F hG k'' (Φ p)) =
      ∑ p : Fin n × Fin n', (c p.1 * c' p.2 * (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (r p)))⁻¹) •
        termPull D.toPre (FractionRing R) F k'' β (genericTerm D k'' β ((y p).2 β)) := fun β => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [d₂, map_smulₛₗ, map_smulₛₗ, smul_smul, inv_mul_cancel_right₀ (hr' p)]; rfl
  have hE := expandsG_of_fintype U.toUnifPre F k'' v'' _ _ y hy (hv.trans (Finset.sum_congr (M := GroupSec U.toUnifPre F k'') rfl fun p _ => by
    rw [d₁, map_smulₛₗ, smul_smul, inv_mul_cancel_right₀ (hr' p)])) hs
  rw [← ((expandsG_bijective U.toUnifPre F hG hk'' (U.expand k'' hk'')).1 v'').unique b'' hE] at hs
  choose z hz using fun i χ => exists_isTerm g hw ((x i).2 χ)
  choose z' hz' using fun i χ => exists_isTerm g hw' ((x' i).2 χ)
  choose z'' hz'' using fun p => exists_isTerm g hw'' ((y p).2 α)
  have key := sumF_sum hR Finset.univ (fun p : Fin n × Fin n' =>
      c p.1 * c' p.2 * (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (r p)))⁻¹)
    fun p => point_field U.toUnifPre hL hR (r p) hm (hx p.1) (hx' p.2) (hy p) (fun Z q z j hj => by
      rw [hyτ p]
      exact (powVal_smul _ _ q z hj).trans (congrArg _ (hτ p Z q z j hj))) g hw'' hww (hz p.1) (hz' p.2) α (hz'' p)
  rw [coef_eq_sum g hz'' (hs α)]
  convert key using 2 with χ
  rw [coef_eq_sum g (fun i => hz i χ) (e₂ χ), coef_eq_sum g (fun i => hz' i (α - χ)) (e₂' (α - χ)), Finset.sum_mul_sum,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have := hr' (p, q)
  field_simp

end

theorem qkToAkU_level_field : LL → FieldUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k n N : ℕ), 1 ≤ k → 1 ≤ n →
    N = k * n → ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N) x, q.y = n • p.y → q.g = p.g →
    QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F N q x := by
  intro hL R _ _ I hI D A G _ _ hG U F _ _ k n N hk hn hN p q x hy hg hx
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hn
  have hf : (algebraMap F (AlgebraicClosure F)).comp (algebraMap (FractionRing R) F) = algebraMap _ _ :=
    (IsScalarTower.algebraMap_eq _ _ _).symm
  have hp := (TorusExt.qkExt_iff D.tau_bimult _ hf p _).2 rfl
  have hq := (TorusExt.qkExt_iff D.tau_bimult _ hf q _).2 rfl
  refine (TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hN1 hq x).2 ?_
  refine DvrAnyChar.qkToAkU_level_any hL R I hI D A G hG U _ k n N hk hn hN
    (TorusExt.qkExt D.tau_bimult _ hf p) _ _ hy ?_
    ((TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hk hp x).1 hx)
  exact congrArg (TorusExt.gtExt D.toPre _ hf) hg

theorem exists_sumI_smul {R : Type} [CommRing R] {I : Ideal R} [IsAdicComplete I R] {E Ix : Type} [AddCommGroup E]
    [Module R E] {x : Ix → E} {s : E} (h : SumI I x s) (a : Ix → R) : ∃ s', SumI I (fun i => a i • x i) s' := by
  classical
  obtain ⟨N, hN, hs, hx, hS⟩ := h
  choose S hS using hS
  have h0 : ∀ n i, i ∉ S n → x i ∈ I ^ n • N := fun n i hi => by
    have := sub_mem (hS n (S n) le_rfl) (hS n (insert i (S n)) (Finset.subset_insert _ _))
    rwa [Finset.sum_insert hi, sub_sub_sub_cancel_left, add_sub_cancel_right] at this
  have h1 : ∀ n (T T' : Finset Ix), S n ⊆ T → T ⊆ T' → ∑ i ∈ T', a i • x i - ∑ i ∈ T, a i • x i ∈ I ^ n • N :=
    fun n T T' h h' => by
      rw [← Finset.sum_sdiff h', add_sub_cancel_right]
      exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
        (h0 n i fun hi' => (Finset.mem_sdiff.1 hi).2 (h hi'))
  haveI : Module.Finite R N := Module.Finite.iff_fg.2 hN
  have hP := T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module I N
  let T : ℕ → Finset Ix := fun n => (Finset.range (n + 1)).biUnion S
  have hT : ∀ n, S n ⊆ T n := fun n => Finset.subset_biUnion_of_mem S (Finset.self_mem_range_succ n)
  have hT' : ∀ m n, m ≤ n → T m ⊆ T n := fun m n h =>
    Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono (by omega))
  let f : ℕ → N := fun n => ⟨∑ i ∈ T n, a i • x i, Submodule.sum_mem _ fun i _ => N.smul_mem _ (hx i)⟩
  obtain ⟨l, hl⟩ := hP.prec' f (fun {m n} h => by
    rw [SModEq.sub_mem, Submodule.mem_smul_top_iff, ← neg_mem_iff]
    simpa [f] using h1 m _ _ (hT m) (hT' m n h))
  refine ⟨l, N, hN, l.2, fun i => N.smul_mem _ (hx i), fun n => ⟨T n, fun T' h => ?_⟩⟩
  have e := hl n
  rw [SModEq.sub_mem, Submodule.mem_smul_top_iff] at e
  have := add_mem (h1 n _ _ (hT n) h) e
  rw [← neg_mem_iff]
  convert this using 1
  simp [f]

theorem exists_sumF_twist {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hI : AdmBase R I) {Ix : Type}
    {x : Ix → FractionRing R} {s : FractionRing R} (h : SumF I (FractionRing R) x s) {n : ℕ} (hn : 1 ≤ n)
    (a : Ix → FractionRing R) (ha : ∀ i, a i ^ n = 1) : ∃ s', SumF I (FractionRing R) (fun i => a i * x i) s' := by
  obtain ⟨-, -, hc, hI⟩ := hI
  have : ∀ i, ∃ b : R, algebraMap R (FractionRing R) b = a i := fun i =>
    IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow hn (by rw [ha]; exact isIntegral_one))
  choose b hb using this
  letI : Module R (FractionRing R) := Module.compHom _ (algebraMap R (FractionRing R))
  obtain ⟨s', hs'⟩ := exists_sumI_smul h b
  refine ⟨s', ?_⟩
  simp only [← hb]
  exact hs'

end GlobalTheory.Poinc.Tors.AnyField
end
