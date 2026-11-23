import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestQuadraticFormEqPsiValuationMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecIsMulOfSval
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.Shift
open ReciprocityTheory.ChartRestriction.G.DVR IsLocalRing

theorem lin_iff {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {R : Type} [CommRing R] (p : Y ⟶ Sp R) {I : Type} [Fintype I] (a : I → R)
    (s : LB.Sec (LB.LinComb L φ ε)) (t : I → LB.Sec (LB.LinComb L φ ε)) :
    (∀ j, s.f j = ∑ i, constFn p _ (a i) * (t i).f j) ↔
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
        sval s r z J = ∑ i, cst (r ≫ p) z (a i) * sval (t i) r z J := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι) (hm : r z ∈ LB.wchart L φ j),
      gs r z (LB.wchart L φ j) (∑ i, constFn p (LB.wchart L φ j) (a i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j)) =
        ∑ i, cst (r ≫ p) z (a i) * gs r z (LB.wchart L φ j) ((t i).f j) := fun Z r z j hm => by
    have e : ∀ (b : I → Γ(Y, LB.wchart L φ j)), gs r z _ (∑ i, b i) = ∑ i, gs r z _ (b i) := fun b => by
      simp only [gs_eq r z _ hm, map_sum]
    rw [e]
    exact Finset.sum_congr rfl fun i _ => (gs_mul r z _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_constFn p _ r z hm _) rfl)
  constructor
  · intro h Z r z J hJ
    exact (congrArg (gs r z _) (h _)).trans (key Z r z _ (hJ.mem φ r))
  · intro h j
    refine fn_ext fun y hy => ?_
    choose J hJ using fun ψ : Y ⟶ X => exists_chart hL (ψ y)
    have hJ' : Good L y J := hJ
    have m := hJ'.mem φ (𝟙 Y)
    refine (sec_trans s (𝟙 Y) y (j := j) hy m).trans (Eq.trans ?_ (key Y (𝟙 Y) y j hy).symm)
    refine (congrArg _ (h Y (𝟙 Y) y J hJ')).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sec_trans (t i) (𝟙 Y) y (j := j) hy m]
    exact mul_left_comm _ _ _

section
variable {V : Type} [CommRing V] [IsDomain V] (D : DegPre V)

abbrev tr (mu : D.X) : D.P.A.left ⟶ D.P.A.left := (𝟙 D.P.A * SectionScalarValuation.cQ D D.P.A mu).left

theorem tr_hom (mu : D.X) : tr D mu ≫ D.P.A.hom = D.P.A.hom := Over.w _

theorem tr_tr (mu nu : D.X) (h : mu + nu = 0) : tr D mu ≫ tr D nu = 𝟙 _ := by
  have c₃ : SectionScalarValuation.cQ D D.P.A 0 = 1 := by
    have := SectionScalarValuation.cQ_nsmul D D.P.A 0 0
    rwa [zero_nsmul, pow_zero] at this
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, SectionScalarValuation.comp_cQ, _root_.mul_assoc, ← SectionScalarValuation.cQ_add, h, c₃,
    _root_.mul_one, Over.id_left]

abbrev EB (k : ℕ) (α mu : D.X) : Type :=
  LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (α + k • mu)) (fun i => tr D mu ≫ D.famφB α i)) (DegPre.deltaε k))

def Rel {k : ℕ} {α mu : D.X} (e : EB D k α mu) (β : D.SecB k α) (gm : D.SecB k (α + k • mu)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
    sval gm r z J = sval β (r ≫ tr D mu) z J * (val e r z J).val

theorem exists_fwd {k : ℕ} {α mu : D.X} (e : EB D k α mu) (he : e.IsGen) (β : D.SecB k α) : ∃ gm, Rel D e β gm := by
  have hform : FormEq (Sum.elim (fun i => tr D mu ≫ D.famφB α i)
      (Sum.elim (D.famφB (α + k • mu)) (fun i => tr D mu ≫ D.famφB α i)))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) (D.famφB (α + k • mu)) (DegPre.famε k) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨gm, hgm⟩ := exists_sec D.P.isLB hform (pullMulSec β (tr D mu) e he)
  exact ⟨gm, fun Z r z J hJ => (hgm Z r z J hJ).trans (sval_pullMulSec _ _ _ he r z hJ)⟩

theorem exists_bwd {k : ℕ} {α mu : D.X} (e : EB D k α mu) (he : e.IsGen) (gm : D.SecB k (α + k • mu)) :
    ∃ β, Rel D e β gm := by
  have h1 : tr D (-mu) ≫ tr D mu = 𝟙 _ := tr_tr D _ _ (neg_add_cancel mu)
  have h2 : tr D mu ≫ tr D (-mu) = 𝟙 _ := tr_tr D _ _ (add_neg_cancel mu)
  have hform : FormEq (Sum.elim (fun i => tr D (-mu) ≫ D.famφB (α + k • mu) i)
      (fun i => tr D (-mu) ≫ Sum.elim (D.famφB (α + k • mu)) (fun i => tr D mu ≫ D.famφB α i) i))
      (Sum.elim (DegPre.famε k) (fun i => - DegPre.deltaε k i)) (D.famφB α) (DegPre.famε k) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib, inv_inv,
      ← Category.assoc, h1, Category.id_comp]
    rw [← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]
  obtain ⟨β, hβ⟩ := exists_sec D.P.isLB hform (pullMulSec gm (tr D (-mu))
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ e (tr D (-mu)))) (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ he _)))
  refine ⟨β, fun Z r z J hJ => ?_⟩
  rw [hβ Z _ z J hJ, sval_pullMulSec _ _ _ _ _ z hJ, val_inv, val_pull hJ, Category.assoc, h2, Category.comp_id,
    _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem isBasisB_move {k : ℕ} {α mu : D.X} (e : EB D k α mu) (he : e.IsGen) {I : Type} [Fintype I]
    (β : I → D.SecB k α) (hβ : IsBasisB D β) (gm : I → D.SecB k (α + k • mu)) (u : Vˣ)
    (h : ∀ i, ∃ g, Rel D e (β i) g ∧ ∀ j, (gm i).f j = constFn D.P.A.hom _ (u : V) * g.f j) : IsBasisB D gm := by
  intro s
  obtain ⟨s₀, hs⟩ := exists_bwd D e he s
  choose g hg hgm using h
  have h1 : tr D (-mu) ≫ tr D mu = 𝟙 _ := tr_tr D _ _ (neg_add_cancel mu)
  have hv : ∀ i (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      sval (gm i) r z J = cst (r ≫ D.P.A.hom) z (u : V) * (sval (β i) (r ≫ tr D mu) z J * (val e r z J).val) :=
    fun i Z r z J hJ => by
      rw [← hg i Z r z J hJ]
      exact (congrArg (gs r z _) (hgm i _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans
        (congrArg₂ (· * ·) (gs_constFn _ _ r z (hJ.mem _ r) _) rfl))
  have key : ∀ b : I → V, (∀ j, s.f j = ∑ i, constFn D.P.A.hom _ (b i) * (gm i).f j) ↔
      (∀ j, s₀.f j = ∑ i, constFn D.P.A.hom _ (b i * u) * (β i).f j) := fun b => by
    rw [lin_iff D.P.isLB D.P.A.hom b s gm, lin_iff D.P.isLB D.P.A.hom (fun i => b i * u) s₀ β]
    constructor
    · intro H Z r z J hJ
      have e1 := H Z (r ≫ tr D (-mu)) z J hJ
      rw [hs Z _ z J hJ] at e1
      simp only [hv _ Z _ z J hJ, Category.assoc, h1, Category.comp_id, tr_hom] at e1
      refine (val e (r ≫ tr D (-mu)) z J).isUnit.mul_right_cancel (e1.trans ?_)
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [H1.cst_mul]; ring
    · intro H Z r z J hJ
      rw [hs Z _ z J hJ, H Z _ z J hJ, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [hv _ Z _ z J hJ, H1.cst_mul, Category.assoc, tr_hom]; ring
  obtain ⟨a, ha, hu⟩ := hβ s₀
  refine ⟨fun i => a i * (u⁻¹ : Vˣ), (key _).2 (by simpa using ha), fun b hb => funext fun i => ?_⟩
  rw [← hu _ ((key b).1 hb)]
  simp
end

theorem shift (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    (k : ℕ) (α mu : D.toPre.X) (n : ℕ) (hn : k * Q mu + QForm.bOf D.toPre Q mu α = n) :
    ∃ (e : EB D.toPre k α mu) (u : Vˣ), e.IsGen ∧ ∀ (f : ∀ α, D.toPre.SecB k α) (s : Fam D.toPre (FractionRing V) k),
      FamOf D.toPre _ f s → ∃ g, Rel D.toPre e (f α) g ∧
        ∀ j, (f (α + k • mu)).f j = constFn D.toPre.P.A.hom _ (ϖ ^ n * u) * g.f j := by
  have hL := D.toPre.P.isLB
  obtain ⟨Ix, _, φV, εV, e', he', hC, c₀, ⟨u, hc₀⟩, hval⟩ := SectionScalarValuation.famMult_data D hϖ hQ k mu α
  obtain ⟨eB, heB, veB⟩ := SectionScalarValuation.exists_eB D.toPre k α mu e' he' hC
  refine ⟨eB, u, heB, fun f s hf => ?_⟩
  obtain ⟨g, hg⟩ := exists_fwd D.toPre eB heB (f α)
  refine ⟨g, hg, GlobalTheory.LevelOneIdeal.secIsMul_of_sval hL D.toPre.P.A.hom
    (IntegralExpansion.prB_app_injective D.toPre) fun y J hJ => ?_⟩
  obtain ⟨⟨w, hw, hc⟩, hv⟩ := gen_fe (D := D.toPre) (F := FractionRing V) hG k mu α
  have vu := hv w hw hc _ (𝟙 _) y J hJ
  have hrel := (secRel_iff hL _ _ _ _ _ _ _ _ _ w).1 (s.fe mu α w hw hc) _ (𝟙 _) y J hJ
  rw [← SectionScalarValuation.secScal_sval (hf _) _ y hJ, ← SectionScalarValuation.secScal_sval (hf _) _ y hJ, Category.id_comp, Category.id_comp,
    SectionScalarValuation.trF_prB] at hrel
  rw [hrel, hg _ _ y J hJ, mul_left_comm]
  congr 1
  have w₁ : (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ jFK (R := V) (FractionRing V) ≫ jK V =
      (DegPre.prB D.toPre (FractionRing V)).left ≫ D.toPre.P.A.hom :=
    (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).trans (Over.w (DegPre.prB D.toPre (FractionRing V))).symm
  have v₁ := veB _ (DegPre.prB D.toPre (FractionRing V)) y J hJ
  have v₂ := hval (FractionRing V) _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y J hJ
  have hc₁ : c₀ = algebraMap V (FractionRing V) (ϖ ^ n * u) := by
    rw [hc₀, hn, zpow_natCast, map_mul, map_pow]
  have v₃ : gs ((fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ jFK (R := V) (FractionRing V)) y ⊤ (scal (𝟙 _) c₀) =
      cst ((DegPre.prB D.toPre (FractionRing V)).left ≫ D.toPre.P.A.hom) y (ϖ ^ n * u) := by
    rw [← w₁, ← Category.assoc, hc₁]
    exact (cst_comp _ (algebraMap V (FractionRing V)) y _).symm
  have v₄ : (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left ≫ DegPre.jFR (R := V) (FractionRing V) =
      (DegPre.prB D.toPre (FractionRing V)).left ≫ D.toPre.P.A.hom := w₁
  rw [v₃, v₄] at v₂
  rw [Over.id_left, Category.id_comp, uVal, Category.id_comp, Category.id_comp, comp_cP] at vu
  rw [vu, v₁]
  simp only [Units.val_mul]
  rw [v₂]
  simp only [SectionScalarValuation.cQ, cP, th]
  ring

theorem main : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → ∀ (i₀ : J) (α : u.D.toPre.X), (∃ m, α = cls i₀ + k • m) → (Short l.q k α → IsBasisB u.D.toPre (fun i : {i // cls i = cls i₀} => f i α)) ∧ (¬ Short l.q k α → ∃ (a : u.V) (β : u.D.toPre.SecB k α), a ∈ IsLocalRing.maximalIdeal u.V ∧ ∀ j, (f i₀ α).f j = constFn u.D.toPre.P.A.hom _ a * β.f j) := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u l k hk J _ σ cls f ⟨hsh, _, _, _, hfam, _, hB⟩ i₀ α ⟨m, hm⟩
  subst hm
  obtain ⟨ϖ, Q, hϖ, hQ, hlt, hq⟩ := GlobalTheory.ZH.PsiForm.q_eq_val_mul o Ω S ρ p y₀ u l
  have hne : (u.j ϖ : PadicAlgCl p) ≠ 0 := by
    show algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ) ≠ 0
    rw [map_ne_zero, map_ne_zero_iff _ (IsFractionRing.injective u.V (FractionRing u.V))]
    exact hϖ.ne_zero
  have hc : 0 < -Real.log ‖(u.j ϖ : PadicAlgCl p)‖ := neg_pos.2 (Real.log_neg (norm_pos_iff.2 hne) hlt)
  have hle : ∀ a b, l.q a ≤ l.q b ↔ Q a ≤ Q b := fun a b => by
    rw [hq, hq, mul_le_mul_iff_left₀ hc, Int.cast_le]
  have hs := q_shift hϖ hQ (cls i₀) m k
  have h0 := (hle _ _).1 (hsh i₀ m)
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have hnn : 0 ≤ k * Q m + QForm.bOf u.D.toPre Q m (cls i₀) :=
    nonneg_of_mul_nonneg_right (a := (k : ℤ)) (by linarith) hk'
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
  obtain ⟨e, w, he, H⟩ := shift hLL.1.globalFns hϖ u.D hQ k (cls i₀) m n hn
  rw [hn] at hs
  constructor
  · intro hS
    have h1 := (hle _ _).1 (hS (-m))
    rw [smul_neg, add_neg_cancel_right, hs] at h1
    have hn0 : n = 0 := by
      have : (n : ℤ) ≤ 0 := by nlinarith
      omega
    subst hn0
    refine isBasisB_move u.D.toPre e he _ (hB i₀) _ w fun i => ?_
    obtain ⟨s, hs'⟩ := hfam i.1
    obtain ⟨g, hg, hg'⟩ := H (f i.1) s hs'
    rw [pow_zero, _root_.one_mul] at hg'
    exact ⟨g, hg, hg'⟩
  · intro hS
    obtain ⟨s, hs'⟩ := hfam i₀
    obtain ⟨g, -, hg'⟩ := H (f i₀) s hs'
    refine ⟨_, g, ?_, hg'⟩
    have hn0 : n ≠ 0 := by
      rintro rfl
      refine hS fun m' => ?_
      rw [add_assoc, ← smul_add]
      refine le_trans ((hle _ _).2 ?_) (hsh i₀ (m + m'))
      rw [hs]; simp
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 hϖ.not_isUnit) n
      (Nat.pos_of_ne_zero hn0))

end GlobalTheory.ZH.Shift
end
