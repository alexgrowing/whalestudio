import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameRatioAdj

section
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh GlobalTheory.FrameBiextId

variable {V : Type} [CommRing V] {d n : ℕ}

theorem jEq_of_psJet {σ : Type} [Fintype σ] [DecidableEq σ] {m : ℕ} {f g : MvPowerSeries σ V}
    (h : psJet m f = psJet m g) : JEq m f g := by
  intro e he
  rw [psJet, psJet, FBIdJet.psTrunc_eq, FBIdJet.psTrunc_eq] at h
  have h' := Ideal.Quotient.eq.1 h
  have h'' := (MvPolynomial.mem_pow_idealOfVars_iff' _ _).1 h' e (Nat.lt_succ_of_le he)
  rwa [MvPolynomial.coeff_sub, MvPowerSeries.coeff_truncTotal _ (Nat.lt_succ_of_le he),
    MvPowerSeries.coeff_truncTotal _ (Nat.lt_succ_of_le he), sub_eq_zero] at h''

theorem ac_ac (A B : Q V d 1) (u : Q V d n) : ac (ac A B) u = ac A (ac B u) := sq_ac _ _ _

theorem formalSeriesValueAtTwoPoints_zero_zero (f : PS V 2 d) (h : ev (n := 1) ![0, pt V d 0] f = 1) : E2 f (0 : Q V d n) 0 = 1 := by
  have := congrArg (sb (![0] : Fin 1 → Q V d n)) ((formalSeriesValueAtTwoPoints_eq_ev f 0 (gen 0)).trans h)
  rwa [formalPointSubstitutionSeries_valueAtTwoPoints, map_zero, sq_gen, map_one] at this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {t : SAB H (Sp V)}
  {x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G}

theorem PP_coord (Φ : Q V d 1) (h : CoordRel x x' Φ.1) (m : ℕ) (u : Q V d n) : PP m x' u = PP m x (ac Φ u) := by
  have e := h m
  rw [subst_eq m _ ![Φ] (fun s => by obtain ⟨j, s⟩ := s; fin_cases j; rfl)
    (fun s => (cc_psTrunc m _).trans (Φ.2 _))] at e
  rw [PP, e]
  exact PP_sq m x _ _

theorem ee_rel (Φ : Q V d 1) {e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m} {e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m} {m : ℕ}
    {ε : PS V 2 d} (h : FrRel t x x' e e' Φ.1 m ε) {y : (jOG (𝟙 (Sp V)) d m n).left} {J} (hJ : Good t.PP.L y J)
    (u v : Q V d n) : VV m y (E2 ε u v) = (ee x' e' y J u v * (ee x e y J (ac Φ u) (ac Φ v))⁻¹).val := by
  obtain ⟨U, hU, h⟩ := h
  have hΦ : ∀ (i : Fin 2) (j : Fin d), (Ideal.Quotient.mk _ (psIn d m ![i] (Φ.1 j)) : Jet V (Fin 2 × Fin d) m) =
      psJet m ((ac Φ (gen i) : Q V d 2).1 j) := fun i j =>
    (mk_psIn m _ _).trans (congrArg (fun b => psJet m (sb b (Φ.1 j))) (funext fun l => by fin_cases l; rfl))
  have e₀ := val_peG x hJ e ![u, v] ![fun j => psIn d m ![0] (Φ.1 j), fun j => psIn d m ![1] (Φ.1 j)]
    (ac Φ (gen 0)) (ac Φ (gen 1)) (by rintro ⟨l, j⟩; fin_cases l; exacts [hΦ 0 j, hΦ 1 j])
    (by rintro ⟨l, j⟩; fin_cases l <;> exact (cc_psIn d m _ _).trans (Φ.2 j))
  rw [sq_ac, sq_ac, sq_gen, sq_gen] at e₀
  have k := (val_corr hJ h (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jQ m ![u, v])).left).trans
    ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·) rfl e₀))
  exact (gm_unit (y := y) U ![u, v] _ hU).symm.trans (congrArg Units.val (eq_mul_inv_of_mul_eq k.symm))

end

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FrameBiextId in

theorem ratio_adj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → (∀ a : 𝓞 E, star a = H.bar a) → Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → FamAd t (𝟙 (Sp V)) d x B.A.act B.ad e → FamAd t (𝟙 (Sp V)) d x' B'.A.act B'.ad e' → ∀ a, JEq m (B'.ad a * ev (n := 2) ![pt V (n := 2) d 0, comp1 (B'.A.act (star a)) (pt V (n := 2) d 1)] ε) (ev (n := 2) ![comp1 φ (pt V (n := 2) d 0), comp1 φ (pt V (n := 2) d 1)] (B.ad a) * ev (n := 2) ![comp1 (B'.A.act a) (pt V (n := 2) d 0), pt V (n := 2) d 1] ε) := by
  intro E _ _ _ H _ V _ _ t d B B' κ κ' _ _ tg tg' uv uv' x x' e e' φ φi m ε hc hc' hinv hx _ hact _ _ hrel hstar hs
    hf hf' a
  let Φ : Q V d 1 := ⟨φ, hinv.1⟩
  let Ψ : Q V d 1 := ⟨φi, hinv.2.1⟩
  have hΦΨ : ac Φ Ψ = gen 0 := Subtype.ext ((ac_val Φ Ψ).trans hinv.2.2.1)
  have hA : ∀ (b : 𝓞 E) (u : Q V d 2), ac Φ (ac (AQ B'.A b) u) = ac (AQ B.A b) (ac Φ u) := fun b u => by
    have : AQ B'.A b = ac Ψ (ac (AQ B.A b) Φ) := Subtype.ext (by rw [ac_val, ac_val]; exact hact b)
    rw [this, ac_ac, ac_ac, ← ac_ac Φ Ψ, hΦΨ]
    exact sq_gen _ _
  obtain ⟨w, hw, hU⟩ := hf a
  obtain ⟨w', hw', hU'⟩ := hf' a
  obtain ⟨U, h₁, h₂⟩ := hU m
  obtain ⟨U', h₁', h₂'⟩ := hU' m
  obtain ⟨c₀, hc₀⟩ := exists_const t.PP.L t.PP.isLB (t.G ⊗ t.G).hom hs
    (LB.mulGen t.PP.L _ _ _ _ w' (LB.invGen t.PP.L _ _ w))
    (mulGen_isGen _ _ _ _ _ _ _ hw' (invGen_isGen _ _ _ _ hw)) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
  have g2 : ∀ f : PS V 2 d, ev (n := 2) ![pt V d 0, pt V d 1] f = f := fun f =>
    (formalSeriesValueAtTwoPoints_eq_ev f (gen 0) (gen 1)).symm.trans (formalSeriesValueAtTwoPoints_genericPoints f)
  have key : psJet m (E2 (B'.ad a) (gen 0 : Q V d 2) (gen 1) * E2 ε (gen 0) (ac (AQ B'.A (H.bar a)) (gen 1))) =
      psJet m (E2 (B.ad a) (ac Φ (gen 0)) (ac Φ (gen 1)) * E2 ε (ac (AQ B'.A a) (gen 0)) (gen 1)) := by
    refine cst_ext fun y => ?_
    choose J hJ using fun ψ : (jOG (𝟙 (Sp V)) d m 2).left ⟶ t.G.left => exists_chart t.PP.isLB (ψ y)
    replace hJ : Good t.PP.L (Z := (jOG (𝟙 (Sp V)) d m 2).left) y J := hJ
    change VV (x0 := 𝟙 (Sp V)) m y _ = VV (x0 := 𝟙 (Sp V)) m y _
    have dA := dict_ad (A := B.A) (ad := B.ad) hJ a w U h₁ h₂
    have dB := dict_ad (A := B'.A) (ad := B'.ad) hJ a w' U' h₁' h₂'
    have hE := ee_rel Φ hrel hJ
    have k : ∀ p q : jOG (𝟙 (Sp V)) d m 2 ⟶ t.G, (val₂ w' y J p q * (val₂ w y J p q)⁻¹).val =
        gs (jOG (𝟙 (Sp V)) d m 2).hom y ⊤ c₀ := fun p q => by
      have := hc₀ _ (lift p q).left y J hJ
      rw [val_mul hJ, val_inv, Over.w] at this
      exact this
    have a₀ := dA 0 0
    have b₀ := dB 0 0
    rw [formalSeriesValueAtTwoPoints_zero_zero _ (B.adjoint_zero_fst a), VV_one, ac0, ac0, mul_inv_cancel_right, PP_zero hc] at a₀
    rw [formalSeriesValueAtTwoPoints_zero_zero _ (B'.adjoint_zero_fst a), VV_one, ac0, ac0, mul_inv_cancel_right, PP_zero hc'] at b₀
    have k₁ := Units.ext ((k (PP m x (ac Φ (gen 0))) (PP m x (ac Φ (gen 1)))).trans (k 1 1).symm)
    rw [Units.ext a₀.symm (v := 1), Units.ext b₀.symm (v := 1), mul_inv_cancel, mul_inv_eq_one] at k₁
    simp only [VV_mul, dA, dB, hE, hA, PP_coord Φ hx, k₁, ← Units.val_mul]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [hstar a]
  simpa only [formalSeriesValueAtTwoPoints_eq_ev, ac_val, gen_val, g2] using jEq_of_psJet key

end GlobalTheory.FrameRatioAdj
