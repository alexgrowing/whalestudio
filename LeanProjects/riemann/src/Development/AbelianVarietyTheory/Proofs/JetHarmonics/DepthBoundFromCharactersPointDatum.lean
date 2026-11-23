import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RosIdSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermExistsUniqueLinear
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValueAtZeroLinearCombinationIntegralSections
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenOfTop
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SurjectiveAppTop
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivativeCongruenceGermIntegralTranslateStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumProdConstMul

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory GlobalTheory.FamGerm GlobalTheory.DepthBound
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DepthFromChars

theorem depth_bound_of_chars : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → (∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)) → ∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ (a : 𝓞 E) (k : ℕ), a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → Nat.Coprime p k → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → ∀ (isV : T → Prop) [DecidablePred isV], (∀ t, isV t → τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ¬ isV t → IsUnit (τ t a)) → (∃ lam : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ (n : ℕ) (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ), (∀ t, Function.Injective (col t)) → (∀ t i, col t i ∈ S ↔ isV t) → ∀ D : ℕ, D = ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) → D < p - 1 → 4 * D + 4 ≤ k → (D : ℝ) * M₀ < k → ∀ h : PS F 2 y.d, y.B.IsCanonGauge F h → ∀ ep : ℚ, y.v (p : F) = (ep : ℚ) → ∃ (s : Fin n → Fam y.P.D.toPre F k) (s' t : Fin n → Fam y.P.D.toPre F (k * p)) (f : Fin n → PS F 1 y.d) (gm : ℚ), (∀ b, NuGe y.P.D y.Q F y.v (k) (s b) 0 ∧ PullAl y.P.D F y.P.oD a k p (s b) (s' b) ∧ y.Transl (k * p) (star a) (s' b) (t b) ∧ y.Germ (k * p) (t b) (f b)) ∧ y.v (y.colVal h (k * p) (fun l i => (e l i : F)) (FamGerm.minorsP F col m) f) = (gm : ℚ) ∧ (gm : ℝ) ≤ (D : ℝ) * ep / (p - 1) + S.card * r * Cc / (4 * k) + (D : ℝ) ^ 2 * Cc / k := by
  intro hL _ hL4 hTB hC p hp E _ _ _ H V _ _ _ F _ _ _ _ _ _ y hcomp hpu Dw I r bs Cc M₀ hred a k
    haa hcop hpk T _ _ rk τ e he isV _ hV hU ⟨lam, hlam⟩ ⟨ε, hε⟩ n S col m hcol hS D hD hDp hk hM h hh ep hep
  have hTW : TwistBCSpanStatement := twistBCSpan_of hTB
  have hVR : TWM.VRatioGtStatement := GlobalTheory.RatioVal.main
  have hUU : UUStatement := GlobalTheory.UnitBallFree.main hL.globalFns hTB
  obtain ⟨jA, jR, -, -, -, -, -, jS, jX, -, -, -, -, jB⟩ := GlobalTheory.JetRoad.jetRoad
  have hG : FamGerm.GermExSt := GlobalTheory.FamGermExist.germ_exists_unique_linear hL hL4 hTW jA jR jS jX
  have hGV : GermValSt := GlobalTheory.GermValuation.main hL hL4 hTW jA jR jS jX hG
  have hJ : JetsSt := GlobalTheory.GermJets.jets hL hL4 hTW jA jR jS jX hG
  have hP : PullGermSt := GlobalTheory.PullGerm.germ_pullback hL hL4 hTW jA jR jS jX GlobalTheory.JetRoad.rosIdSt hG
  have hE : EigGermSt := GlobalTheory.T.derivative_congruence_germ_integral_translate hL hL4 hTW jA jR jS jX GlobalTheory.JetRoad.rosIdSt jB hG
  classical
  let _ := H.starRing
  have hp' : p.Prime := hp.out
  have hp2 : 2 ≤ p := hp'.two_le
  have hpF : ((p : TWO.Ov y.v) : F) = p := map_natCast (TWO.Ov y.v).subtype p
  have hep0 : 0 < ep := by
    by_contra hle
    refine hpu (Ideal.span_singleton_eq_top.1 ((Ideal.eq_top_iff_one _).2 (mem_span_of_val_le y.v _ 1 ?_ ?_)))
    · rw [hpF]; exact_mod_cast hp'.ne_zero
    · rw [hpF, hep, OneMemClass.coe_one, y.v.map_one]
      exact_mod_cast not_lt.1 hle
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hp2
    linarith
  set θ : ℚ := ep / ((p : ℚ) - 1) with hθ
  have hθ0 : 0 < θ := div_pos hep0 hp1
  obtain ⟨c, hc⟩ := ExactTerm.exists_val_eq_of_nonneg y.hv hθ0.le
  obtain ⟨ω, hω1, hω⟩ := FramePull.exists_integral_frame_pullback V y.d (𝓞 E) F y.B h hh H.w0 a p haa

  let m₁ : ∀ t, Fin (rk t) → ℕ := fun t s => if isV t then m t s else 0
  let m₂ : ∀ t, Fin (rk t) → ℕ := fun t s => if isV t then 0 else m t s
  have hm : m = fun t s => m₁ t s + m₂ t s := by
    funext t s
    by_cases ht : isV t <;> simp [m₁, m₂, ht]
  have hm₁ : ∀ t, ¬ isV t → ∀ s, m₁ t s = 0 := fun t ht s => if_neg ht
  have hm₂ : ∀ t, ¬ ¬ isV t → ∀ s, m₂ t s = 0 := fun t ht s => if_pos (not_not.1 ht)
  have hDD : ∑ t, ∑ s : Fin (rk t), m₁ t s * (s.val + 1) + ∑ t, ∑ s : Fin (rk t), m₂ t s * (s.val + 1) = D := by
    rw [hD, hm]
    simp only [add_mul, Finset.sum_add_distrib]

  obtain ⟨y₁, hy₁, hy₂⟩ := hC p E H V F y hcomp hpu a haa hcop {t // isV t} (fun t => rk t.1) (fun t => τ t.1)
    (fun l => e ⟨l.1.1, l.2⟩) (fun c l => he c ⟨l.1.1, l.2⟩) (fun t => hV t.1 t.2)
    (fun t => ⟨fun i => lam ⟨t.1, i⟩, fun i i' => by simpa using hlam ⟨t.1, i⟩ ⟨t.1, i'⟩⟩)
    ⟨fun t => ε t.1, fun t t' => by simpa only [Subtype.ext_iff] using hε t.1 t'.1⟩
    ⟨c, by rw [TWO.mem_Ov, hc]; exact_mod_cast hθ0.le⟩
    (by
      change (p - 1) • y.v c = _
      rw [hc, hep, ← WithTop.coe_nsmul, nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_one, hθ,
        mul_div_cancel₀ _ hp1.ne'])
    n (fun t => col t.1) (fun t => hcol t.1)
  let yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v := fun x =>
    if hx : isV x.1.1 then y₁ (⟨⟨x.1.1, hx⟩, x.1.2⟩, x.2) else 0
  choose s₁ s₁' t₁ c₁ f₁ r₁ h₁ hc₁ hr₁ hf₁ hf₁' using fun b => exists_eigen_column y hL hTW hVR hUU hG hGV hE Dw I r bs
    Cc M₀ hred a p k hp' (by omega) haa hcop hpk (Σ t : {t // isV t}, Fin (rk t.1)) (fun l => e ⟨l.1.1, l.2⟩)
    (fun l => y₁ (l, b)) (fun l => τ l.1.1 a) (fun l => hV _ l.1.2) (fun l => he a ⟨l.1.1, l.2⟩) (hy₁ b) h hh ω hω1 hω
  have hD₁ : ((∑ t, ∑ s : Fin (rk t), m₁ t s * (s.val + 1) : ℕ) : ℚ) * θ ≤ D * θ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega)) hθ0.le
  have hF₁ := val_eigen_columns y.v _ (fO_comp_eq y) y.B h hh H.w0 a p k hp'.ne_zero hpu hcop ω hω1 hω τ e he isV hV
    S col m₁ (fun t i ht => (hS t i).2 ht) hm₁ yy f₁ (fun b _ => hf₁ b)
    (fun b _ l hl mo => by
      simp only [yy, dif_pos hl]
      exact hf₁' b ⟨⟨l.1, hl⟩, l.2⟩ mo)
    θ ep hep
    (fun t ht s => by
      simp only [yy, dif_pos ht]
      refine (hy₂ ⟨t, ht⟩ s).trans (le_of_eq ?_)
      change (s.val + 1) • y.v c = _
      rw [hc, ← WithTop.coe_nsmul, nsmul_eq_mul, Nat.cast_succ])
    (hD₁.trans_lt (by
      have : (D : ℚ) < (p : ℚ) - 1 := by
        have h1 : D + 1 < p := by omega
        have h2 : (D : ℚ) + 1 < p := by exact_mod_cast h1
        linarith
      calc (D : ℚ) * θ < ((p : ℚ) - 1) * θ := mul_lt_mul_of_pos_right this hθ0
        _ = ep := by rw [hθ, mul_div_cancel₀ _ hp1.ne']))

  obtain ⟨g, nb, hg, hnb, hF₂⟩ := val_unit_columns y.v y.B h hh H.w0 a p k hp' hpu ω hω τ e (he a) (fun t => ¬ isV t)
    hU lam hlam Sᶜ col m₂ hcol (fun t i ht => Finset.mem_compl.2 fun h' => ht ((hS t i).1 h')) hm₂ (by omega)
  have hnbD : ∑ b, nb b ≤ D := by omega
  have hnbD' : ∀ b, nb b ≤ D := fun b =>
    (Finset.single_le_sum (f := nb) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)).trans hnbD
  choose s₂ s₂' t₂ c₂ f₂ r₂ h₂ hc₂ hr₂ hf₂ using fun b => exists_jet_column y hL hG hJ hP r bs Cc M₀ hred a p k (nb b)
    (by omega) haa (by have := hnbD' b; omega)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hnbD' b) hred.2.1) hM) h hh ω hω (g b) (hg b)
  have hF₂' := hF₂ f₂ fun b _ => hf₂ b
  let f : Fin n → PS F 1 y.d := fun b =>
    if b ∈ S then MvPowerSeries.C (c₁ b) * (FB.toK F (f₁ b) * FB.toK F ω ^ k)
    else MvPowerSeries.C (c₂ b) * (ev (n := 1) ![y.B.actK F a] (f₂ b) * FB.toK F ω ^ k)
  have hval : y.v (y.colVal h (k * p) (fun l i => (e l i : F)) (minorsP F col m) f) ≤
      ((∑ b ∈ S, r₁ b + D * θ + ∑ b ∈ Sᶜ, r₂ b : ℚ) : WithTop ℚ) := by
    have e₁ := colValue_mul_of_disjoint_columns F _ n (fun b mo => y.B.nabVal F h H.w0 (k * p) (f b)
      (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) S (minorsP F col m₁) (minorsP F col m₂)
      (fun mo hmo l b hb => by
        obtain ⟨hz, i, rfl⟩ := minorMonomial_support col m₁ isV hm₁ hmo l b hb
        exact (hS _ i).2 hz)
      (fun mo hmo l b hb => by
        obtain ⟨hz, i, rfl⟩ := minorMonomial_support col m₂ (fun t => ¬ isV t) hm₂ hmo l b hb
        exact fun h' => hz ((hS _ i).1 h'))
    rw [← minorMonomial_add, ← hm, sum_prod_const_mul S _ (fun b mo => y.B.nabVal F h H.w0 (k * p) (f b)
        (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) (fun b mo => y.B.nabVal F h H.w0 (k * p)
        (FB.toK F (f₁ b) * FB.toK F ω ^ k) (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) c₁
        (fun b hb mo => by simp only [f, if_pos hb]; exact nabVal_C_mul _ _ _ _ _ _ _ _),
      sum_prod_const_mul Sᶜ _ (fun b mo => y.B.nabVal F h H.w0 (k * p) (f b)
        (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) (fun b mo => y.B.nabVal F h H.w0 (k * p)
        (ev (n := 1) ![y.B.actK F a] (f₂ b) * FB.toK F ω ^ k) (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) c₂
        (fun b hb mo => by simp only [f, if_neg (Finset.mem_compl.1 hb)]; exact nabVal_C_mul _ _ _ _ _ _ _ _)] at e₁
    refine (congrArg y.v e₁).trans_le ?_
    rw [y.v.map_mul, y.v.map_mul, y.v.map_mul, hF₂', add_zero, WithTop.coe_add, WithTop.coe_add]
    exact add_le_add (add_le_add (val_prod_le y.v _ _ _ fun b _ => (hc₁ b).le)
      (hF₁.trans (WithTop.coe_le_coe.2 hD₁))) (val_prod_le y.v _ _ _ fun b _ => (hc₂ b).le)
  obtain ⟨gm, hgm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hval)
  refine ⟨fun b => if b ∈ S then s₁ b else s₂ b, fun b => if b ∈ S then s₁' b else s₂' b,
    fun b => if b ∈ S then t₁ b else t₂ b, f, gm, fun b => ?_, hgm.symm, ?_⟩
  · by_cases hb : b ∈ S
    · simp only [f, if_pos hb]; exact h₁ b
    · simp only [f, if_neg hb]; exact h₂ b
  · rw [← hgm, WithTop.coe_le_coe] at hval
    have h1 : (gm : ℝ) ≤ ∑ b ∈ S, (r₁ b : ℝ) + D * (ep / (p - 1)) + ∑ b ∈ Sᶜ, (r₂ b : ℝ) := by
      rw [hθ] at hval
      exact_mod_cast hval
    have h2 : ∑ b ∈ S, (r₁ b : ℝ) ≤ S.card * r * Cc / (4 * k) := by
      refine (Finset.sum_le_card_nsmul _ _ _ fun b _ => hr₁ b).trans (le_of_eq ?_)
      rw [nsmul_eq_mul]; ring
    have hCk : 0 ≤ Cc / k := div_nonneg hred.1 (Nat.cast_nonneg _)
    have h3 : ∑ b ∈ Sᶜ, (r₂ b : ℝ) ≤ (D : ℝ) ^ 2 * Cc / k := by
      have h4 : ∑ b ∈ Sᶜ, nb b ^ 2 ≤ D ^ 2 :=
        calc ∑ b ∈ Sᶜ, nb b ^ 2 ≤ ∑ b, nb b ^ 2 := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          _ ≤ ∑ b, nb b * D := Finset.sum_le_sum fun b _ => by
            rw [sq]; exact Nat.mul_le_mul_left _ (hnbD' b)
          _ ≤ D ^ 2 := by rw [← Finset.sum_mul, sq]; exact Nat.mul_le_mul_right _ hnbD
      refine (Finset.sum_le_sum fun b _ => hr₂ b).trans ?_
      simp only [mul_div_assoc]
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h4) hCk
    rw [mul_div_assoc (D : ℝ) (ep : ℝ)]
    linarith

end GlobalTheory.DepthFromChars
