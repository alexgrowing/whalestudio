import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesJetEqCalculus
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChartCmp.RatioSecondLaw
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
open Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh GlobalTheory.FrameBiextId

section Dict
variable {S : Type} [CommRing S] {d n k m : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0} {x0 : Sp S ⟶ X0}
  {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {y : (jOG x0 d m n).left} {J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι}

theorem frame_value_second_partial_law (hJ : Good t.PP.L y J) (G : FGLaw S d) {e : ∀ m, FrTyG t x0 d x m} {ph2 : PS S 3 d}
    (hf : FamPh2 t x0 d x G.F ph2 e) (u v w : Q S d n) :
    VV m y (E3 ph2 u v w) = (cubV t.cub y J (PP m x v) (PP m x w) (PP m x u) *
    (ee x e y J u (op (FQ G) v w))⁻¹ * ee x e y J u v * ee x e y J u w).val := by
  obtain ⟨U, hU, h⟩ := hf m
  have hc := gm_unit (y := y) U ![u, v, w]
  have e₀ := val_peG x hJ e ![u, v, w] ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (G.F j)] (gen 0) (op (FQ G) (gen 1) (gen 2))
    (by rintro ⟨l, j⟩; fin_cases l; exacts [hX 0 j, hF 1 2 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [MvPolynomial.constantCoeff_X _ _, (cc_psIn d m _ _).trans (G.const j)])
  rw [sq_op, sq_gen, sq_gen, sq_gen] at e₀
  have k := (val_th hJ ![u, v, w] 1 2 0).symm.trans ((val_corr hJ h _).trans ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·) rfl
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e₀ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_inv _ _).trans (congrArg (·⁻¹) (peXX hJ _ 0 1))) ((val_inv _ _).trans (congrArg (·⁻¹) (peXX hJ _ 0 2))))))))))
  refine (hc _ hU).symm.trans (congrArg Units.val (Additive.ofMul.injective ?_))
  have k' := congrArg Additive.ofMul k
  simp only [ofMul_mul, ofMul_inv, Matrix.cons_val] at k' ⊢
  linear_combination (norm := abel) -k'

theorem mk_psIn_one (Φ : Q S d 1) (i : Fin k) (j : Fin d) :
    (Ideal.Quotient.mk _ (psIn d m ![i] (Φ.1 j)) : Jet S (Fin k × Fin d) m) = psJet m ((ac Φ (gen i) : Q S d k).1 j) :=
  (mk_psIn m _ _).trans (congrArg (fun b => psJet m (sb b (Φ.1 j))) (funext fun l => by fin_cases l; rfl))

end Dict

section Rel
variable {V : Type} [CommRing V] {d n m : ℕ}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {t : SAB H (Sp V)}
  {x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {y : (jOG (𝟙 (Sp V)) d m n).left}
  {J : ((jOG (𝟙 (Sp V)) d m n).left ⟶ t.G.left) → t.PP.L.ι}

theorem PP_rel (Φ : Q V d 1) (h : CoordRel x x' Φ.1) (u : Q V d n) : PP m x' u = PP m x (ac Φ u) := by
  have e := h m
  rw [subst_eq m _ ![Φ] (fun s => by obtain ⟨j, s⟩ := s; fin_cases j; rfl)
    (fun s => (cc_psTrunc m _).trans (Φ.2 _))] at e
  exact (congrArg (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jQ m ![u]) ≫ ·) e).trans (PP_sq m x _ _)

theorem val_eps (hJ : Good t.PP.L y J) (Φ : Q V d 1) {e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m}
    {e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m} {ε : PS V 2 d} (h : FrRel t x x' e e' Φ.1 m ε) (u v : Q V d n) :
    VV m y (E2 ε u v) = (ee x' e' y J u v * (ee x e y J (ac Φ u) (ac Φ v))⁻¹).val := by
  obtain ⟨U, hU, h⟩ := h
  have hc := gm_unit (y := y) U ![u, v]
  have e₀ := val_peG x hJ e ![u, v] ![fun j => psIn d m ![0] (Φ.1 j), fun j => psIn d m ![1] (Φ.1 j)]
    (ac Φ (gen 0)) (ac Φ (gen 1))
    (by rintro ⟨l, j⟩; fin_cases l; exacts [mk_psIn_one Φ 0 j, mk_psIn_one Φ 1 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [(cc_psIn d m _ _).trans (Φ.2 j), (cc_psIn d m _ _).trans (Φ.2 j)])
  rw [sq_ac, sq_ac, sq_gen, sq_gen] at e₀
  have k : ee x' e' y J u v = _ := (val_corr hJ h _).trans ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·) rfl e₀))
  exact (hc _ hU).symm.trans (congrArg Units.val (eq_mul_inv_of_mul_eq k.symm))

theorem ac_op_trans (G G' : FGLaw V d) (Φ Ψ : Q V d 1) (hi : comp1 Φ.1 Ψ.1 = pt V (n := 1) d 0)
    (h : ∀ i, G'.F i = transF G.F Φ.1 Ψ.1 i) (u v : Q V d n) :
    ac Φ (op (FQ G') u v) = op (FQ G) (ac Φ u) (ac Φ v) := by
  have h1 : (FQ G' : Q V d 2) = ac Ψ (op (FQ G) (ac Φ (gen 0)) (ac Φ (gen 1))) := by
    apply Subtype.ext
    simp only [ac_val, op_val]
    exact funext h
  have h2 : ac Φ Ψ = gen 0 := Subtype.ext ((ac_val _ _).trans hi)
  have h3 : ∀ w : Q V d n, ac Φ (ac Ψ w) = w := fun w => by
    have := congrArg (sq ![w]) h2
    rw [sq_ac, sq_gen] at this
    exact this
  rw [op, h1, sq_ac, h3, sq_op, sq_ac, sq_ac, sq_gen, sq_gen]
  rfl

end Rel

theorem ratio_second_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → FamPh2 t (𝟙 (Sp V)) d x B.G.F B.ph2 e → FamPh2 t (𝟙 (Sp V)) d x' B'.G.F B'.ph2 e' → JEq m (B'.ph2 * ev (n := 3) ![pt V (n := 3) d 0, addOf B'.G.F (pt V (n := 3) d 1) (pt V (n := 3) d 2)] ε) (ev (n := 3) ![comp1 φ (pt V (n := 3) d 0), comp1 φ (pt V (n := 3) d 1), comp1 φ (pt V (n := 3) d 2)] B.ph2 * (ev (n := 3) ![pt V (n := 3) d 0, pt V (n := 3) d 1] ε * ev (n := 3) ![pt V (n := 3) d 0, pt V (n := 3) d 2] ε)) := by
  intro E _ _ _ H _ V _ _ t d B B' κ κ' _ _ tg tg' uv uv' x x' e e' φ φi m ε _ _ hi hco hl _ _ _ hr hf hf'
  let Φ : Q V d 1 := ⟨φ, hi.1⟩
  let Ψ : Q V d 1 := ⟨φi, hi.2.1⟩
  have key : psJet m (E3 B'.ph2 (gen 0 : Q V d 3) (gen 1) (gen 2) * E2 ε (gen 0) (op (FQ B'.G) (gen 1) (gen 2))) =
      psJet m (E3 B.ph2 (ac Φ (gen 0)) (ac Φ (gen 1)) (ac Φ (gen 2)) * (E2 ε (gen 0) (gen 1) * E2 ε (gen 0) (gen 2))) := by
    refine cst_ext fun y => ?_
    choose J hJ using fun ψ : (jOG (𝟙 (Sp V)) d m 3).left ⟶ t.G.left => exists_chart t.PP.isLB (ψ y)
    have hJ : Good t.PP.L (Z := (jOG (𝟙 (Sp V)) d m 3).left) y J := hJ
    show VV (x0 := 𝟙 (Sp V)) m y _ = VV (x0 := 𝟙 (Sp V)) m y _
    simp only [VV_mul, frame_value_second_partial_law hJ _ hf, frame_value_second_partial_law hJ _ hf', val_eps hJ Φ hr, PP_rel Φ hco,
      ac_op_trans B.G B'.G Φ Ψ hi.2.2.1 hl, ← Units.val_mul]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [formalSeriesValueAtThreePoints_genericPoints, formalSeriesValueAtThreePoints_eq_ev, formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtTwoPoints_eq_ev, op_val, ac_val, ac_val, ac_val] at key
  exact ((JCalc.jeq_calculus V m).2.2.2.2.1 _ _ _).2 key

end GlobalTheory.ChartCmp.RatioSecondLaw
