import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RatioPh1
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
open GlobalTheory.FrameBiextId

theorem jeq_of_psJet {R σ : Type} [CommRing R] [Fintype σ] [DecidableEq σ] {m : ℕ} {f g : MvPowerSeries σ R}
    (h : psJet m f = psJet m g) : JEq m f g := by
  intro e he
  rw [psJet, psJet, FBIdJet.psTrunc_eq, FBIdJet.psTrunc_eq] at h
  have h' : Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ (m + 1)) (MvPowerSeries.truncTotal (m + 1) f) =
      Ideal.Quotient.mk _ (MvPowerSeries.truncTotal (m + 1) g) := h
  rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff'] at h'
  have := h' e (Nat.lt_succ_of_le he)
  rwa [MvPolynomial.coeff_sub, MvPowerSeries.coeff_truncTotal _ (Nat.lt_succ_of_le he),
    MvPowerSeries.coeff_truncTotal _ (Nat.lt_succ_of_le he), sub_eq_zero] at this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] {t : SAB H (Sp V)}
  {d n m : ℕ} {x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G}
  {y : (jOG (𝟙 (Sp V)) d m n).left} {J : ((jOG (𝟙 (Sp V)) d m n).left ⟶ t.G.left) → t.PP.L.ι}

theorem frame_value_first_partial_law (hJ : Good t.PP.L y J) {G : FGLaw V d} {ph1 : PS V 3 d} {e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m}
    (hf : FamPh1 t (𝟙 (Sp V)) d x G.F ph1 e) (u v w : Q V d n) :
    VV m y (E3 ph1 u v w) = (cubV t.cub y J (PP m x u) (PP m x v) (PP m x w) *
      (ee x e y J (op (FQ G) u v) w)⁻¹ * ee x e y J u w * ee x e y J v w).val := by
  obtain ⟨U, hU, h⟩ := hf m
  have hc := gm_unit (y := y) U ![u, v, w]
  have e₀ := val_peG x hJ e ![u, v, w] ![fun j => psIn d m ![0, 1] (G.F j), fun j => MvPolynomial.X ((2 : Fin 3), j)]
    (op (FQ G) (gen 0) (gen 1)) (gen 2)
    (by rintro ⟨l, j⟩; fin_cases l; exacts [hF 0 1 j, hX 2 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [(cc_psIn d m _ _).trans (G.const j), MvPolynomial.constantCoeff_X _ _])
  rw [sq_op, sq_gen, sq_gen, sq_gen] at e₀
  have k := (val_th hJ ![u, v, w] 0 1 2).symm.trans ((val_corr hJ h _).trans ((val_scale hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) e₀ ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) (peXX hJ _ 0 2)))
        ((val_inv _ _).trans (congrArg (·⁻¹) (peXX hJ _ 1 2))))))))))
  refine (hc _ hU).symm.trans (congrArg Units.val (Additive.ofMul.injective ?_))
  have k' := congrArg Additive.ofMul k
  simp only [ofMul_mul, ofMul_inv, Matrix.cons_val] at k' ⊢
  linear_combination (norm := abel) -k'

theorem PP_coord (φ : Q V d 1) (h : CoordRel x x' φ.1) (u : Q V d n) : PP m x' u = PP m x (ac φ u) := by
  have e := h m
  rw [subst_eq m _ ![φ] (fun s => by obtain ⟨j, s⟩ := s; fin_cases j; rfl)
    (fun s => (cc_psTrunc m _).trans (φ.2 _))] at e
  exact (congrArg (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jQ m ![u]) ≫ ·) e).trans (PP_sq m x _ _)

theorem ee_rel (hJ : Good t.PP.L y J) {e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m} {e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m}
    (φ : Q V d 1) {ε : PS V 2 d} (h : FrRel t x x' e e' φ.1 m ε) (u v : Q V d n) :
    VV m y (E2 ε u v) = (ee x' e' y J u v * (ee x e y J (ac φ u) (ac φ v))⁻¹).val := by
  obtain ⟨U, hU, h⟩ := h
  have hc := gm_unit (y := y) U ![u, v]
  have hA : ∀ (i : Fin 2) j, (Ideal.Quotient.mk _ (psIn d m ![i] (φ.1 j)) : Jet V (Fin 2 × Fin d) m) =
      psJet m ((ac φ (gen i) : Q V d 2).1 j) := fun i j =>
    (mk_psIn m _ _).trans (congrArg (fun b => psJet m (sb b (φ.1 j))) (funext fun l => by fin_cases l; rfl))
  have e₀ := val_peG x hJ e ![u, v] ![fun j => psIn d m ![0] (φ.1 j), fun j => psIn d m ![1] (φ.1 j)]
    (ac φ (gen 0)) (ac φ (gen 1))
    (by rintro ⟨l, j⟩; fin_cases l; exacts [hA 0 j, hA 1 j])
    (by rintro ⟨l, j⟩; fin_cases l; exacts [(cc_psIn d m _ _).trans (φ.2 j), (cc_psIn d m _ _).trans (φ.2 j)])
  rw [sq_ac, sq_ac, sq_gen, sq_gen] at e₀
  have k : ee x' e' y J u v = _ := (val_corr hJ h _).trans ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·) rfl e₀))
  exact (hc _ hU).symm.trans (congrArg Units.val (eq_mul_inv_of_mul_eq k.symm))

theorem ac_op_trans {G G' : FGLaw V d} (φ φi : Q V d 1) (hi : comp1 φ.1 φi.1 = pt V (n := 1) d 0)
    (hl : ∀ i, G'.F i = transF G.F φ.1 φi.1 i) (u v : Q V d n) :
    ac φ (op (FQ G') u v) = op (FQ G) (ac φ u) (ac φ v) := by
  have h1 : FQ G' = ac φi (op (FQ G) (ac φ (gen 0)) (ac φ (gen 1))) := Subtype.ext (by
    simp only [ac_val, op_val, gen_val]; exact funext hl)
  have h2 : ac φ φi = gen 0 := Subtype.ext ((ac_val _ _).trans hi)
  have h3 : ∀ w : Q V d n, ac φ (ac φi w) = w := fun w => by
    have := congrArg (sq ![w]) h2
    rwa [sq_ac, sq_gen] at this
  have h4 : op (FQ G') u v = ac φi (op (FQ G) (ac φ u) (ac φ v)) := by
    have := congrArg (sq ![u, v]) h1
    rw [sq_ac, sq_op, sq_ac, sq_ac, sq_gen, sq_gen] at this
    exact this
  rw [h4, h3]

theorem frame_ratio_first_partial_law_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)) (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t (𝟙 (Sp V)) d x' m) (φ φi : Pt V 1 d) (m : ℕ) (ε : PS V 2 d), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → IsInvPair φ φi → CoordRel x x' φ → (∀ i, B'.G.F i = transF B.G.F φ φi i) → (∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)) → (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → FrRel t x x' e e' φ m ε → FamPh1 t (𝟙 (Sp V)) d x B.G.F B.ph1 e → FamPh1 t (𝟙 (Sp V)) d x' B'.G.F B'.ph1 e' → JEq m (B'.ph1 * ev (n := 3) ![addOf B'.G.F (pt V (n := 3) d 0) (pt V (n := 3) d 1), pt V (n := 3) d 2] ε) (ev (n := 3) ![comp1 φ (pt V (n := 3) d 0), comp1 φ (pt V (n := 3) d 1), comp1 φ (pt V (n := 3) d 2)] B.ph1 * (ev (n := 3) ![pt V (n := 3) d 0, pt V (n := 3) d 2] ε * ev (n := 3) ![pt V (n := 3) d 1, pt V (n := 3) d 2] ε)) := by
  intro E _ _ _ H _ V _ _ t d B B' κ κ' _ _ tg tg' uv uv' x x' e e' φ φi m ε _ _ hi hco hl _ _ _ hr h1 h1'
  let φ' : Q V d 1 := ⟨φ, hi.1⟩
  let φi' : Q V d 1 := ⟨φi, hi.2.1⟩
  have key : psJet m (E3 B'.ph1 (gen 0 : Q V d 3) (gen 1) (gen 2) * E2 ε (op (FQ B'.G) (gen 0) (gen 1)) (gen 2)) =
      psJet m (E3 B.ph1 (ac φ' (gen 0 : Q V d 3)) (ac φ' (gen 1)) (ac φ' (gen 2)) *
        (E2 ε (gen 0) (gen 2) * E2 ε (gen 1) (gen 2))) := cst_ext fun y => by
    choose J hJ using fun ψ : (jOG (𝟙 (Sp V)) d m 3).left ⟶ t.G.left => exists_chart t.PP.isLB (ψ y)
    replace hJ : Good t.PP.L (Z := (jOG (𝟙 (Sp V)) d m 3).left) y J := hJ
    show VV (x0 := 𝟙 (Sp V)) m y _ = VV (x0 := 𝟙 (Sp V)) m y _
    simp only [VV_mul, frame_value_first_partial_law hJ h1, frame_value_first_partial_law hJ h1', ee_rel hJ φ' hr, ← Units.val_mul, PP_coord φ' hco,
      ac_op_trans φ' φi' hi.2.2.1 hl]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [ofMul_mul, ofMul_inv]
    abel
  have := jeq_of_psJet key
  rw [formalSeriesValueAtThreePoints_genericPoints] at this
  simpa only [formalSeriesValueAtTwoPoints_eq_ev, formalSeriesValueAtThreePoints_eq_ev, op_val, ac_val, gen_val] using this

end GlobalTheory.RatioPh1
