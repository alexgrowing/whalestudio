import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ExistsChartComplexPoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SectionsEquivAnArcTheta
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

noncomputable section

namespace GlobalTheory.AnPairing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open FrameValue TwistedTheta

section Frames

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (hL : L.IsLB)

def frAt (z : Fin g → ℂ) : ℂ := u.fr (chartAt hL (u.ex z).left) z

theorem frAt_ne_zero (z : Fin g → ℂ) : frAt u hL z ≠ 0 := u.fr_ne _ _ (le_chartAt hL _)

variable {u} {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ}

theorem sval_eq (s : LB.Sec (LB.LinComb L φ ε)) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} (hz : IsLift u φ y z) :
    sval s y pt (chartAt hL) = toStalk (FrameValue.secVal u hL s y z * ∏ k, frAt u hL (z k) ^ ε k) := by
  have h := le_wchart_chartAt hL φ y
  refine (gs_eq_toStalk _ _ h _).trans (congrArg toStalk ((valAt'_sec hL s hz h).trans ?_))
  simp only [FrameValue.frameProd, frAt, hz _]

theorem val_eq {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ}
    (hz : IsLift u φ y z) :
    (val t y pt (chartAt hL)).val = toStalk (genVal u hL t y z * ∏ k, frAt u hL (z k) ^ ε k) :=
  (sval_genSec t ht y pt (good_chartAt hL)).symm.trans (sval_eq hL (genSec t ht) hz)

end Frames

variable {O : Type} [CommRing O] [StarRing O] [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {D : DegPre ℂ} [Module O D.X] {oa : D.OAct O} (d : GtDict D oa)

abbrev fr (z : Fin d.A.gB → ℂ) : ℂ := frAt d.u D.P.isLB z

theorem fr_period (l : d.A.abelian₂) (z : Fin d.A.gB → ℂ) : fr d z = d.A.ah l z * fr d (z + l) := by
  rw [fr, fr, frAt, frAt, d.ex_add_lam]
  exact d.fr_eq_ah_mul l _ z (le_chartAt _ _)

theorem th_ex (a b c : Fin d.A.gB → ℂ) :
    (th D (T := 𝟙_ (Over (Sp ℂ))) pt (chartAt D.P.isLB) (d.u.ex a) (d.u.ex b) (d.u.ex c)).val =
      toStalk (fr d (a + b + c) * (fr d (a + b))⁻¹ * (fr d (a + c))⁻¹ * (fr d (b + c))⁻¹ * fr d a * fr d b * fr d c *
        (fr d 0)⁻¹) := by
  refine (val_eq D.P.isLB D.cub.isGen (isLift_cube d.u ![a, b, c])).trans (congrArg toStalk ?_)
  refine (congrArg₂ (· * ·) (genVal_cube_of_face D.P.isLB d.isAH D.cub.t D.cub.isGen (D.cub.face 0) ![a, b, c])
    (prod_thK fun I => fr d (∑ i ∈ I, ![a, b, c] i))).trans ((_root_.one_mul _).trans ?_)
  simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val]

theorem cubN_ex (k : ℕ) (a b c : Fin d.A.gB → ℂ) :
    (cubN (th D (T := 𝟙_ (Over (Sp ℂ))) pt (chartAt D.P.isLB)) k (d.u.ex a) (d.u.ex b) (d.u.ex c)).val =
      toStalk (fr d (a + k • b + c) * (fr d (a + k • b))⁻¹ * (fr d (a + c))⁻¹ * fr d a *
        ((fr d (b + c))⁻¹ * fr d b * fr d c * (fr d 0)⁻¹) ^ k) := by
  have n := frAt_ne_zero d.u D.P.isLB
  induction k with
  | zero =>
    have := n (a + c)
    have := n a
    refine (map_one toStalk).symm.trans (congrArg toStalk ?_)
    simp only [zero_smul, add_zero]
    field_simp
  | succ k ih =>
    rw [cubN, Finset.prod_range_succ, Units.val_mul, ← ex_nsmul, ← d.u.ex_add]
    refine (congrArg₂ (· * ·) ih (th_ex d _ _ _)).trans ((map_mul toStalk _ _).symm.trans (congrArg toStalk ?_))
    have := n (a + k • b + c)
    have := n (a + k • b)
    rw [succ_nsmul, ← add_assoc a, pow_succ]
    field_simp

def base : 𝟙_ (Over (Sp ℂ)) ⟶ TF (R := ℂ) ℂ := Over.homMk (𝟙 (Sp ℂ)) ((Category.id_comp _).trans jFK_comp_jK_complex)

def ptB (z : Fin d.A.gB → ℂ) : 𝟙_ (Over (Sp ℂ)) ⟶ DegPre.BF D ℂ := lift base (d.u.ex z)

theorem ptB_fst (z : Fin d.A.gB → ℂ) : ptB d z ≫ fst _ _ = base := lift_fst _ _

theorem ptB_prB (z : Fin d.A.gB → ℂ) : ptB d z ≫ DegPre.prB D ℂ = d.u.ex z := lift_snd _ _

omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem comp_toUnit_comp {T B : Over (Sp ℂ)} (x : 𝟙_ (Over (Sp ℂ)) ⟶ T) (y : 𝟙_ (Over (Sp ℂ)) ⟶ B) :
    x ≫ toUnit T ≫ y = y := by
  rw [← Category.assoc, Subsingleton.elim (x ≫ toUnit T) (𝟙 _), Category.id_comp]

theorem cPoint_eX (α : d.A.X) : cP D (𝟙_ (Over (Sp ℂ))) (d.eX α) = d.u.ex (d.A.ct α) := by
  rw [cP, d.ex_ct, toUnit_unit, Category.id_comp]

theorem base_b (v : d.A.V) : base ≫ (d.ex₀ v).b = d.u.ex v.2 := by
  rw [d.ex₀_b, comp_toUnit_comp]

theorem ptB_trPt (z : Fin d.A.gB → ℂ) (v : d.A.V) : ptB d z ≫ DegPre.trPt D ℂ (d.ex₀ v).b = ptB d (z + v.2) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, tr_fst, ptB_fst, ptB_fst]
  · refine ((Category.assoc _ _ _).trans (congrArg (ptB d z ≫ ·) (tr_pr D ℂ _))).trans (Eq.trans ?_ (ptB_prB d _).symm)
    rw [MonObj.comp_mul, ptB_prB, ← Category.assoc, ptB_fst, base_b, d.u.ex_add]

theorem isLift_famφ (α : d.A.X) (z : Fin d.A.gB → ℂ) :
    IsLift d.u (DegPre.famφ D ℂ (d.eX α)) (ptB d z).left ![z, z + d.A.ct α, d.A.ct α, 0] := fun k => by
  have e : ∀ (q : DegPre.BF D ℂ ⟶ D.P.A) w, ptB d z ≫ q = d.u.ex w → (ptB d z).left ≫ q.left = (d.u.ex w).left :=
    fun q w hq => congrArg (fun m => m.left) hq
  fin_cases k
  · exact e _ z (ptB_prB d z)
  · exact e _ (z + d.A.ct α) ((MonObj.comp_mul _ _ _).trans (by rw [ptB_prB, comp_toUnit_comp, d.u.ex_add, d.ex_ct]))
  · exact e _ (d.A.ct α) (by rw [comp_toUnit_comp, d.ex_ct])
  · exact e _ 0 (by rw [comp_toUnit_comp, d.ex_zero])

def famFn {k : ℕ} (s : Fam D ℂ k) (α : d.A.X) (z : Fin d.A.gB → ℂ) : ℂ :=
  FrameValue.secVal d.u D.P.isLB (s.s (d.eX α)) (ptB d z).left ![z, z + d.A.ct α, d.A.ct α, 0]

theorem sval_fam {k : ℕ} (s : Fam D ℂ k) (α : d.A.X) (z : Fin d.A.gB → ℂ) :
    sval (s.s (d.eX α)) (ptB d z).left pt (chartAt D.P.isLB) = toStalk (famFn d s α z *
      (fr d z ^ k * (fr d z)⁻¹ * fr d (z + d.A.ct α) * (fr d (d.A.ct α))⁻¹ * fr d 0)) := by
  refine (sval_eq D.P.isLB _ (isLift_famφ d α z)).trans (congrArg toStalk (congrArg₂ (· * ·) rfl ?_))
  simp [Fin.prod_univ_four, DegPre.famε, zpow_sub₀ (frAt_ne_zero d.u D.P.isLB z), div_eq_mul_inv]

theorem val_coord (v : d.A.V) (α : d.A.X) :
    (val ((d.ex₀ v).s (d.eX α)) (base.left) pt (chartAt D.P.isLB)).val = toStalk (eTwoPi (v.1 α) *
      ((fr d (d.A.ct α + v.2))⁻¹ * fr d (d.A.ct α) * fr d v.2 * (fr d 0)⁻¹)) := by
  have hz : IsLift d.u (DegPre.gtφ D ℂ (d.ex₀ v).b (d.eX α)) (𝟙 (Sp ℂ)) ![d.A.ct α + v.2, d.A.ct α, v.2, 0] :=
    fun k => (Category.id_comp _).trans (d.gtφ_eq v α k)
  have h := le_wchart_chartAt D.P.isLB (DegPre.gtφ D ℂ (d.ex₀ v).b (d.eX α)) (𝟙 (Sp ℂ))
  refine (val_eq D.P.isLB ((d.ex₀ v).isGen _) hz).trans (congrArg toStalk (congrArg₂ (· * ·) ?_ ?_))
  · exact (div_eq_iff (FrameValue.frameProd_ne_zero hz _ h)).2 (d.chi_val v α _ h)
  · simp [Fin.prod_univ_four, DegPre.gtε]

theorem exists_val_line {k : ℕ} (v : d.A.V)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D ℂ (d.ex₀ v).b) (DegPre.lineε k))) (hw : w.IsGen) :
    ∃ c : ℂ, c ≠ 0 ∧ (val w (base.left) pt (chartAt D.P.isLB)).val = toStalk (c * (fr d 0 ^ k * (fr d v.2 ^ k)⁻¹)) := by
  have hz : IsLift d.u (DegPre.lineφ D ℂ (d.ex₀ v).b) (𝟙 (Sp ℂ)) ![0, v.2] := fun i => by
    refine (Category.id_comp _).trans ?_
    fin_cases i
    · exact (toUnit_TF_comp_left _).trans (congrArg (·.left) d.ex_zero.symm)
    · exact d.ex₀_b_left v
  refine ⟨_, genVal_ne_zero D.P.isLB w hz,
    (val_eq D.P.isLB hw hz).trans (congrArg toStalk (congrArg₂ (· * ·) rfl ?_))⟩
  simp [Fin.prod_univ_two, DegPre.lineε]

theorem exists_phi_eq_shift (k : ℕ) [NeZero k] (la : d.A.La)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D ℂ (d.qk k la).g.b) (DegPre.lineε k))) (hw : w.IsGen) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ s t : Fam D ℂ k, PhiRel D ℂ k (d.qk k la) w s t →
      ∀ α, famFn d t (α + la.y) = c • d.A.shift k la α (famFn d s α) := by
  obtain ⟨c, hc, hv⟩ := exists_val_line d ((k : ℂ)⁻¹ • d.A.P0 la) w hw
  refine ⟨c, hc, fun s t h α => funext fun z => ?_⟩
  have hJ := good_chartAt D.P.isLB
  have e := (phiRel_iff globalFns_holds _ w hw s t).1 h (d.eX α) (d.eX (α + la.y)) (map_add d.eX _ _).symm
    _ (ptB d z) pt _ hJ
  set v := (k : ℂ)⁻¹ • d.A.P0 la with hvdef
  replace hv : _ = toStalk (c * (fr d 0 ^ k * (fr d v.2 ^ k)⁻¹)) := hv
  have e₁ : ptB d z ≫ DegPre.trPt D ℂ (d.qk k la).g.b = ptB d (z + v.2) := ptB_trPt d z v
  have e₂ : ptB d z ≫ fst _ _ ≫ (d.qk k la).g.b = d.u.ex v.2 := by
    rw [← Category.assoc, ptB_fst]; exact base_b d v
  rw [e₁, uVal, e₂, ptB_fst, ptB_prB, cPoint_eX, sval_fam, sval_fam] at e
  have e₃ := e.trans (congrArg₂ (· * ·) rfl (congrArg Units.val (congrArg₂ (· * ·) rfl (val_mul hJ _ _ _))))
  have e₄ : ((th D (T := 𝟙_ (Over (Sp ℂ))) pt (chartAt D.P.isLB) (d.u.ex (d.A.ct α)) (d.u.ex z) (d.u.ex v.2))⁻¹).val =
      toStalk (_)⁻¹ := Units.inv_eq_of_mul_eq_one_right (by
    rw [th_ex, ← map_mul, mul_inv_cancel₀, map_one]
    simp [frAt_ne_zero])
  rw [Units.val_mul, Units.val_mul, Units.val_mul, cubN_ex, e₄] at e₃
  have e₅ := toStalk.injective (e₃.trans (((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (map_mul _ _ _) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (val_coord d v α).symm hv.symm))))))).symm)
  have hb : k • v.2 = d.A.ct la.y + la.l := by
    rw [hvdef, Prod.smul_snd, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 (NeZero.ne k))]; rfl
  have f₁ := fr_period d la.l (z + d.A.ct (α + la.y))
  have f₂ := fr_period d la.l (d.A.ct (α + la.y))
  rw [add_comm z, d.A.ah_add, add_comm _ z] at f₁
  have a₁ : d.A.ct α + (d.A.ct la.y + la.l) + z = z + d.A.ct (α + la.y) + la.l := by rw [map_add]; abel
  have a₂ : d.A.ct α + (d.A.ct la.y + la.l) = d.A.ct (α + la.y) + la.l := by rw [map_add]; abel
  have a₃ : z + v.2 + d.A.ct α = d.A.ct α + z + v.2 := by abel
  rw [hb, a₁, a₂, a₃, f₁, f₂, add_comm v.2 z] at e₅
  have a₄ : v.1 α = (d.A.P0 la).1 α / k := by rw [hvdef, div_eq_inv_mul]; rfl
  rw [Pi.smul_apply, smul_eq_mul, AnArc.shift_apply', ← a₄, Complex.exp_neg]
  change _ = c * (_ * famFn d s α (z + v.2))
  have n := frAt_ne_zero d.u D.P.isLB
  have n₀ := n 0
  have n₁ := n z
  have n₂ := n v.2
  have n₃ := n (z + v.2)
  have n₄ := n (d.A.ct α)
  have n₅ := n (d.A.ct α + z)
  have n₆ := n (d.A.ct α + v.2)
  have n₇ := n (d.A.ct α + z + v.2)
  have n₈ := n (d.A.ct (α + la.y) + la.l)
  have n₉ := n (z + d.A.ct (α + la.y) + la.l)
  have m₁ := d.A.ah_ne_zero la.l (d.A.ct (α + la.y))
  have m₂ := Complex.exp_ne_zero (Real.pi * d.A.H z la.l)
  simp only [mul_pow, inv_pow] at e₅
  field_simp at e₅ ⊢
  linear_combination e₅

theorem eq_of_famFn_eq {k : ℕ} {s t : Fam D ℂ k} {α : d.A.X} (h : famFn d s α = famFn d t α) (i : Fin 4 → D.P.L.ι) :
    (s.s (d.eX α)).f i = (t.s (d.eX α)).f i := by
  have hT : (TF (R := ℂ) ℂ).hom = 𝟙 (Sp ℂ) := jFK_comp_jK_complex
  have hp : (DegPre.BF D ℂ).hom = pullback.fst (TF (R := ℂ) ℂ).hom D.P.A.hom :=
    (congrArg (pullback.fst (TF (R := ℂ) ℂ).hom D.P.A.hom ≫ ·) hT).trans (Category.comp_id _)
  have := D.P.isAb.smooth
  have : Smooth (DegPre.BF D ℂ).hom := by rw [hp]; infer_instance
  have := isReduced_of_smooth_complex _ (DegPre.BF D ℂ).hom inferInstance
  refine ComplexPoints.eq_of_valAt'_eq (DegPre.BF D ℂ).hom _ _ _ fun x hx hi => ?_
  let x' : 𝟙_ (Over (Sp ℂ)) ⟶ DegPre.BF D ℂ := Over.homMk x hx
  obtain ⟨z, hz⟩ := d.u.ex_onto (x' ≫ DegPre.prB D ℂ)
  have e : ptB d z = x' := by
    apply CartesianMonoidalCategory.hom_ext
    · refine (ptB_fst d z).trans (Over.OverMorphism.ext ?_)
      exact (Over.w (x' ≫ fst _ _)).symm.trans ((congrArg ((x' ≫ fst _ _).left ≫ ·) hT).trans (Category.comp_id _))
    · exact (ptB_prB d z).trans hz
  obtain rfl : (ptB d z).left = x := congrArg (·.left) e
  exact (valAt'_sec D.P.isLB _ (isLift_famφ d α z) hi).trans ((congrArg (· * _) (congrFun h z)).trans
    (valAt'_sec D.P.isLB _ (isLift_famφ d α z) hi).symm)

theorem fam_ext_fn {k : ℕ} {s t : Fam D ℂ k} (h : ∀ α, famFn d s α = famFn d t α) : s = t :=
  fam_ext fun β i => by
    obtain ⟨α, rfl⟩ := d.eX.surjective β
    exact eq_of_famFn_eq d (h α) i

theorem famFn_smul {k : ℕ} (ζ : ℂ) (s : Fam D ℂ k) (α : d.A.X) : famFn d (ζ • s) α = ζ • famFn d s α := by
  funext z
  have e := sval_smul ζ s (d.eX α) (ptB d z).left pt (good_chartAt D.P.isLB)
  have e₁ : (ptB d z).left ≫ (fst (TF (R := ℂ) ℂ) D.P.A).left = 𝟙 (Sp ℂ) := congrArg (·.left) (ptB_fst d z)
  have e₂ : gs (𝟙 (Sp ℂ)) pt ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom ζ) = toStalk ζ :=
    gs_eq (𝟙 (Sp ℂ)) pt ⊤ trivial _
  rw [sval_fam, sval_fam, e₁] at e
  have e₃ := toStalk.injective (e.trans ((congrArg (· * _) e₂).trans (map_mul _ _ _).symm))
  rw [← _root_.mul_assoc ζ] at e₃
  exact mul_right_cancel₀ (by simp [frAt_ne_zero]) e₃

include d in

theorem tauBimult : D.TauBimult := by
  intro a a' b
  obtain ⟨b, rfl⟩ := d.eX.surjective b
  have hb : Function.Bijective (algebraMap (FractionRing ℂ) ℂ) := ⟨RingHom.injective _, fun x =>
    ⟨algebraMap ℂ _ x, (IsScalarTower.algebraMap_apply ℂ (FractionRing ℂ) ℂ x).symm⟩⟩
  have : IsIso (CommRingCat.ofHom (algebraMap (FractionRing ℂ) ℂ)) :=
    (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  have : IsIso (jFK (R := ℂ) ℂ) := inferInstanceAs (IsIso (Spec.map _))
  let σ : TK ℂ ⟶ TF (R := ℂ) ℂ := Over.homMk (inv (jFK (R := ℂ) ℂ)) (IsIso.inv_hom_id_assoc _ _)
  have hσ : σ.left ≫ jFK (R := ℂ) ℂ = 𝟙 _ := IsIso.inv_hom_id _
  have hι := d.iota (AnArc.La.mk b 0 0)
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  have hv : ∀ χ, val ((d.ex₀ (d.A.P0 (AnArc.La.mk b 0 0))).s χ) σ.left y J = val (D.tau χ (d.eX b)) (𝟙 _) y J :=
    fun χ => (val_corr hJ (hι.2 χ) σ.left).trans ((val_pull hJ _ _ _).trans ((tau_symm σ hJ _ _).trans (by rw [hσ]; rfl)))
  have e := gt_mul σ hJ (d.ex₀ (d.A.P0 (AnArc.La.mk b 0 0))) a a'
  have e₁ : σ ≫ (d.ex₀ (d.A.P0 (AnArc.La.mk b 0 0))).b = cP D _ (d.eX b) := by
    rw [hι.1]; exact comp_cP D σ _
  rw [hv, hv, hv, e₁] at e
  refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl ?_) (e.trans (val_mul hJ _ _ _).symm))
  refine (val_cub D.cub (𝟙 (TK ℂ)) hJ (cP D _ a) (cP D _ a') (cP D _ (d.eX b))).trans ?_
  rw [Category.id_comp, Category.id_comp, Category.id_comp]

theorem famFn_comm (k : ℕ) [NeZero k] (la la' : d.A.La)
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D ℂ (d.qk k la).g.b) (DegPre.lineε k))}
    {w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D ℂ (d.qk k la').g.b) (DegPre.lineε k))} (hw : w.IsGen) (hw' : w'.IsGen)
    {s s₁ s₂ s₃ s₄ : Fam D ℂ k} (h₁ : PhiRel D ℂ k (d.qk k la') w' s s₁) (h₂ : PhiRel D ℂ k (d.qk k la) w s₁ s₂)
    (h₃ : PhiRel D ℂ k (d.qk k la) w s s₃) (h₄ : PhiRel D ℂ k (d.qk k la') w' s₃ s₄) :
    s₂ = eTwoPi (-(d.A.EF la la' / k)) • s₄ := by
  obtain ⟨c, -, hc⟩ := exists_phi_eq_shift d k la w hw
  obtain ⟨c', -, hc'⟩ := exists_phi_eq_shift d k la' w' hw'
  refine fam_ext_fn d fun β => ?_
  obtain ⟨α, rfl⟩ : ∃ α, β = α + la'.y + la.y := ⟨β - la.y - la'.y, by abel⟩
  rw [famFn_smul, hc _ _ h₂, hc' _ _ h₁, add_right_comm, hc' _ _ h₄, hc _ _ h₃, map_smul, map_smul, AnArc.shift_comm]
  simp only [smul_smul]
  congr 1
  ring

end GlobalTheory.AnPairing

namespace GlobalTheory.GtDict

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR AnPairing

variable {O : Type} [CommRing O] [StarRing O] [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {D₀ : DegPre ℂ} [Module O D₀.X] {oa : D₀.OAct O} (d : GtDict D₀ oa)

theorem weilQkIs_qk (k : ℕ) [NeZero k] (la la' : d.A.La) :
    WeilQkIs D₀ ℂ k (d.qk k la) (d.qk k la')
      (Complex.exp (-(2 * Real.pi * Complex.I) * (d.A.EF la la' : ℂ) / k)) := by
  intro w w' hw hw' s s₁ s₂ s₃ s₄ h₁ h₂ h₃ h₄
  rw [isSmul_iff, famFn_comm d k la la' hw hw' h₁ h₂ h₃ h₄, eTwoPi]
  congr 2
  ring

end GlobalTheory.GtDict
