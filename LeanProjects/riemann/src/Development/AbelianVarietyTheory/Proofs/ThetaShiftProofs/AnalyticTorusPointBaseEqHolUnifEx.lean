import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.NonemptyGtAnOfToric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SectionsEquivAnArcTheta
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPhiEqShift
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRingHomLift
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtensionComplexPointsEqCharacters

noncomputable section

namespace GlobalTheory.ArcOfModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open FrameValue ToricDict
open scoped CategoryTheory.Obj

theorem genVal_mul_of {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g} {hL : L.IsLB}
    {Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ A.left)} {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} {z' : K' → Fin g → ℂ} {p q : ℂ} (h : genVal u hL t y z = p)
    (h' : genVal u hL t' y z' = q) : genVal u hL (LB.mulGen L φ ε φ' ε' t t') y (Sum.elim z z') = p * q :=
  (genVal_mul hL t t' y _).trans (congrArg₂ (· * ·) h h')

theorem genVal_inv_of {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g} {hL : L.IsLB}
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {y : Sp ℂ ⟶ Y} {z : K → Fin g → ℂ} {p : ℂ} (h : genVal u hL t y z = p) :
    genVal u hL (LB.invGen L φ ε t) y z = p⁻¹ :=
  (genVal_inv hL t y _).trans (congrArg (·⁻¹) h)

theorem genVal_pull_of {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g} {hL : L.IsLB}
    {Y Y' : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {f : Y' ⟶ Y} {y : Sp ℂ ⟶ Y'} {y' : Sp ℂ ⟶ Y} (e : y ≫ f = y') {z : K → Fin g → ℂ} {p : ℂ}
    (h : genVal u hL t y' z = p) : genVal u hL (LB.pullGen L φ ε t f) y z = p :=
  (genVal_pull hL t f y z).trans (e ▸ h)

theorem ex_zero {B : Over (Sp ℂ)} [GrpObj B] {L : LB B.left} {g : ℕ} (u : HolUnif B L g) : u.ex 0 = η[B] := by
  rw [(u.ker 0).2 (zero_mem _), Hom.one_def, toUnit_unit, Category.id_comp]

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

section Points

variable {O : Type} [CommRing O] [StarRing O] {A : AnArc O} {D : Out.DegPre ℂ} [Module O D.X] {ε : A.X ≃ₗ[O] D.X}
  {u : HolUnif D.P.A D.P.L A.gB} (lam : u.Λ = A.abelian₂) (ah : u.IsAH A.Hm fun l => A.chi ⟨l, lam.le l.2⟩)
  (rig : u.IsRig D.rig) (hct : ∀ x, u.ex (A.ct x) = D.c (ε x))
  (hψ : ∀ x, genVal u D.P.isLB (D.psi (ε x)) (Out.jFK (R := ℂ) ℂ) (fun _ => A.ct x) = A.psi x)
  {ex0 : A.V → Out.GtPtF D ℂ} (hxb : ∀ v, (show Sp ℂ ⟶ _ from (ex0 v).b.left) = (u.ex v.2).left)
  (hxs : ∀ v x, genVal u D.P.isLB ((ex0 v).s (ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
    ![A.ct x + v.2, A.ct x, v.2, 0] = eTwoPi (v.1 x))

include hxb in

theorem analyticTorusPoint_base_eq_holUnif_ex (v : A.V) : (ex0 v).b = toUnit _ ≫ u.ex v.2 := by
  exact Over.OverMorphism.ext ((hxb v).trans (toUnit_TF_comp_left _).symm)

include hct hxb in

theorem is_lift_exponential_zero (v : A.V) (x : A.X) :
    IsLift u (Out.DegPre.gtφ D ℂ (ex0 v).b (ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
      ![A.ct x + v.2, A.ct x, v.2, 0] := fun k => by
  refine (Category.id_comp _).trans ?_
  fin_cases k
  · refine Eq.trans ?_ (toUnit_TF_comp_left _)
    change (toUnit _ ≫ D.c (ε x) * (ex0 v).b).left = (toUnit _ ≫ u.ex (A.ct x + v.2)).left
    rw [analyticTorusPoint_base_eq_holUnif_ex hxb, u.ex_add, MonObj.comp_mul, hct]
  · exact (toUnit_TF_comp_left _).trans (congrArg (·.left) (hct x).symm)
  · exact hxb v
  · exact (toUnit_TF_comp_left _).trans (congrArg (·.left) (ex_zero u).symm)

include lam ah hct hxb hxs in

theorem genVal_shift (v : A.V) (z : Fin A.gB → ℂ) (m : A.abelian₂) (hv : v.2 = z + m) (x : A.X) :
    IsLift u (Out.DegPre.gtφ D ℂ (ex0 v).b (ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
      ![A.ct x + z, A.ct x, z, 0] ∧
    genVal u D.P.isLB ((ex0 v).s (ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![A.ct x + z, A.ct x, z, 0] =
      eTwoPi (v.1 x + A.H (A.ct x) m / (2 * Complex.I)) := by
  let m' : u.Λ := ⟨m, lam.ge m.2⟩
  have e₂ : ![A.ct x + v.2, A.ct x, v.2, 0] = fun k => ![A.ct x + z, A.ct x, z, 0] k +
      ((![m', 0, m', 0] : Fin 4 → u.Λ) k : Fin A.gB → ℂ) := by
    funext k
    fin_cases k <;> simp [m', hv, add_assoc]
  have hz : IsLift u (Out.DegPre.gtφ D ℂ (ex0 v).b (ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
      ![A.ct x + z, A.ct x, z, 0] := fun k => by
    refine (is_lift_exponential_zero hct hxb v x k).trans ?_
    rw [e₂]
    beta_reduce
    rw [u.ex_add, (u.ker _).2 (Subtype.prop _), _root_.mul_one]
  refine ⟨hz, ?_⟩
  have h := hxs v x
  rw [e₂] at h
  have h' := (genVal_add_period D.P.isLB ah _ hz _).symm.trans h
  simp only [Fin.prod_univ_four, Out.DegPre.gtε, Matrix.cons_val, ahFactor_zero D.P.isLB ah] at h'
  change A.ah m (A.ct x + z) ^ (-1 : ℤ) * _ * A.ah m z ^ (1 : ℤ) * _ * _ = _ at h'
  have n := A.ah_ne_zero m z
  have e₃ : eTwoPi (A.H (A.ct x) m / (2 * Complex.I)) = Complex.exp (Real.pi * A.H (A.ct x) m) := by
    have := AnArc.e_neg_div (-A.H (A.ct x) m)
    simpa [neg_div] using this
  rw [add_comm (A.ct x) z, AnArc.ah_add] at h'
  rw [AnArc.e_add, e₃, ← h', add_comm (A.ct x) z]
  simp
  field_simp
  rfl

include lam ah hct hxb hxs in

theorem isZero_iff (v : A.V) : (ex0 v).IsZero ↔ ∃ la : A.La, la.y = 0 ∧ v = A.P0 la := by
  constructor
  · rintro ⟨hb, hs⟩
    have h0 : u.ex v.2 = 1 := Over.OverMorphism.ext ((hxb v).symm.trans ((congrArg (·.left) hb).trans
      ((toUnit_TF_comp_left _).trans (by rw [Hom.one_def, toUnit_unit, Category.id_comp]))))
    let m : A.abelian₂ := ⟨v.2, lam.le ((u.ker _).1 h0)⟩
    let w : A.V := v - A.P0 (AnArc.La.mk 0 0 m)
    obtain ⟨n, hn⟩ := (expChar_eq_one_iff w.1).1 (MonoidHom.ext fun x => Units.ext (by
      obtain ⟨hz, h⟩ := genVal_shift lam ah hct hxb hxs v 0 m (zero_add _).symm x.toAdd
      have := genVal_corr D.P.isLB (hs _) hz (z' := PEmpty.elim) (fun k => k.elim)
        (fun f => by simp [Fin.prod_univ_four, Out.DegPre.gtε])
      have e := h.symm.trans (this.trans (genVal_one (u := u) _ _ _))
      change eTwoPi (w.1 x.toAdd) = 1
      simpa [w] using e))
    refine ⟨AnArc.La.mk 0 n m, rfl, Prod.ext (AddMonoidHom.ext fun x => ?_) (by simp [m])⟩
    have := hn x
    simp [w] at this
    simp [← this]
  · rintro ⟨la, hy, rfl⟩
    have hv : (A.P0 la).2 = 0 + la.l := by simp [hy]
    refine ⟨by rw [analyticTorusPoint_base_eq_holUnif_ex hxb, hv, zero_add, (u.ker _).2 (lam.ge la.l.2), Hom.one_def, toUnit_unit, Category.id_comp], fun x => ?_⟩
    obtain ⟨x, rfl⟩ := ε.surjective x
    obtain ⟨hz, h⟩ := genVal_shift lam ah hct hxb hxs _ 0 la.l hv x
    refine TorusExtChar.corr_of_genVal (u := u) D.P.isLB ((ex0 _).isGen _) (fun i j => ?_) hz
      (z' := PEmpty.elim) (fun k => k.elim) (fun f => ?_) ?_
    · exact (map_one _).trans ((_root_.mul_one _).symm.trans (congrArg₂ (· * ·) rfl (map_one _).symm))
    · simp [Fin.prod_univ_four, Out.DegPre.gtε]
    · exact h.trans (Eq.trans (by simp [hy]) (genVal_one (u := u) _ _ _).symm)

include lam ah rig hct hψ hxb hxs in

theorem isIota (la : A.La) : Out.GtPtF.IsIota (ε la.y) (ex0 (A.P0 la)) := by
  refine ⟨by rw [analyticTorusPoint_base_eq_holUnif_ex hxb, AnArc.degeneratingTori_basePeriodMap_snd, u.ex_add, (u.ker _).2 (lam.ge la.l.2), _root_.mul_one, hct], fun x => ?_⟩
  obtain ⟨x, rfl⟩ := ε.surjective x
  obtain ⟨hz, h⟩ := genVal_shift lam ah hct hxb hxs _ _ la.l (A.degeneratingTori_basePeriodMap_snd la) x
  have hc : ∀ y : A.X, 𝟙 (Sp ℂ) ≫ Out.jFK (R := ℂ) ℂ ≫ D.xK (ε y) = (u.ex (A.ct y)).left := fun y => by
    rw [Category.id_comp, hct]
    change Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ ≫ _ = _
    rw [← Category.assoc, jFK_comp_jK_complex, Category.id_comp]
  refine TorusExtChar.corr_of_genVal (u := u) D.P.isLB ((ex0 _).isGen _) ?_ hz
    (z' := Sum.elim (Sum.elim (Sum.elim (fun _ => A.ct (la.y + x)) (fun _ => A.ct la.y)) (fun _ => A.ct x))
      (fun _ => 0)) ?_ (fun f => ?_) ?_
  · exact DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (DVR.invGen_isGen _ _ _ _ (D.psi_gen _)))
      (DVR.invGen_isGen _ _ _ _ (D.psi_gen _)))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.rig_gen _))) _
  · rintro (((k | k) | k) | k)
    · exact (by rw [map_add]; rfl : _ = 𝟙 (Sp ℂ) ≫ Out.jFK (R := ℂ) ℂ ≫ D.xK (ε (la.y + x))).trans (hc _)
    · exact hc _
    · exact hc _
    · change 𝟙 (Sp ℂ) ≫ Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ ≫ eSec D.P.A = (u.ex 0).left
      rw [Category.id_comp, ← Category.assoc, jFK_comp_jK_complex, Category.id_comp, ex_zero u]
      rfl
  · simp [Fin.prod_univ_four, Out.DegPre.gtε, Fintype.prod_sum_type, add_comm]
    ac_rfl
  · have h1 := hψ (la.y + x)
    rw [map_add ε] at h1
    have hr := genVal_pull_of (f := (toUnit (Out.TK ℂ)).left) (y := Out.jFK (R := ℂ) ℂ) jFK_comp_jK_complex
      (genVal_rig D.P.isLB rig)
    have h2 := genVal_pull_of (Category.id_comp (Out.jFK (R := ℂ) ℂ)) (genVal_mul_of (genVal_mul_of
      (genVal_mul_of h1 (genVal_inv_of (hψ la.y))) (genVal_inv_of (hψ x))) (genVal_inv_of hr))
    refine h.trans (Eq.trans ?_ h2.symm)
    have n1 := (A.psi la.y).ne_zero
    have n2 := (A.psi x).ne_zero
    simp [A.psi_add, AnArc.e_add]

    field_simp

include ah hct hxb hxs in

theorem isAdd (v v' : A.V) : (ex0 v).IsAdd (ex0 v') (ex0 (v + v')) := by
  refine ⟨by rw [analyticTorusPoint_base_eq_holUnif_ex hxb, analyticTorusPoint_base_eq_holUnif_ex hxb, analyticTorusPoint_base_eq_holUnif_ex hxb, Prod.snd_add, u.ex_add, MonObj.comp_mul]; rfl, fun x => ?_⟩
  obtain ⟨x, rfl⟩ := ε.surjective x
  have hp : 𝟙 (Sp ℂ) ≫ (lift (Out.DegPre.cF D ℂ (ε x)) (lift (ex0 v).b (ex0 v').b)).left =
      (CubeValues.pt3 u ![A.ct x, v.2, v'.2]).left := by
    rw [Category.id_comp, analyticTorusPoint_base_eq_holUnif_ex hxb, analyticTorusPoint_base_eq_holUnif_ex hxb, Out.DegPre.cF, ← hct, ← comp_lift, ← comp_lift]
    exact toUnit_TF_comp_left _
  refine TorusExtChar.corr_of_genVal (u := u) D.P.isLB
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ((ex0 _).isGen _) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ((ex0 _).isGen _) ((ex0 _).isGen _))
    (z := Sum.elim ![A.ct x + (v + v').2, A.ct x, (v + v').2, 0] (cubeLift ![A.ct x, v.2, v'.2]))
    (z' := Sum.elim ![A.ct x + v.2, A.ct x, v.2, 0] ![A.ct x + v'.2, A.ct x, v'.2, 0]) ?_ ?_ (fun f => ?_) ?_
  · rintro (k | k)
    · exact is_lift_exponential_zero hct hxb _ x k
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hp).trans (isLift_cube u _ k))
  · rintro (k | k)
    · exact is_lift_exponential_zero hct hxb _ x k
    · exact is_lift_exponential_zero hct hxb _ x k
  · erw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    erw [show ∏ I : thK, f (cubeLift ![A.ct x, v.2, v'.2] I) ^ thε I = _ from
      prod_thK fun I => f (∑ a ∈ I, ![A.ct x, v.2, v'.2] a)]
    simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val, Fin.prod_univ_four,
      Out.DegPre.gtε, zpow_neg, zpow_one, Prod.snd_add, add_assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have h1 := genVal_mul_of (hxs (v + v') x) (genVal_pull_of hp
      (genVal_cube_of_face D.P.isLB ah _ D.cub.isGen (D.cub.face 0) _))
    have h2 := genVal_mul_of (hxs v x) (hxs v' x)
    refine h1.trans (Eq.trans ?_ h2.symm)
    simp [AnArc.e_add]

include ah hct hxb hxs in

theorem analyticTorusPoint_surjective : Function.Surjective ex0 := by
  intro g
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk (show Sp ℂ ⟶ _ from g.b.left) ((Over.w g.b).trans jFK_comp_jK_complex))
  have hb : ∀ w : A.X →+ ℂ, (ex0 (w, z)).b = g.b := fun w =>
    Over.OverMorphism.ext ((hxb _).trans (congrArg (·.left) hz))
  have hl : ∀ x, IsLift u (Out.DegPre.gtφ D ℂ g.b (ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
      ![A.ct x + z, A.ct x, z, 0] := fun x => hb 0 ▸ is_lift_exponential_zero hct hxb (0, z) x
  let t : Multiplicative A.X →* ℂˣ := MonoidHom.mk'
    (fun x => Units.mk0 _ (genVal_ne_zero D.P.isLB (g.s (ε x.toAdd)) (hl x.toAdd))) fun x' y' => Units.ext (by
      let x := x'.toAdd
      let y := y'.toAdd
      have hp : 𝟙 (Sp ℂ) ≫ (lift (Out.DegPre.cF D ℂ (ε x)) (lift (Out.DegPre.cF D ℂ (ε y)) g.b)).left =
          (CubeValues.pt3 u ![A.ct x, A.ct y, z]).left := by
        rw [Category.id_comp, ← hb 0, analyticTorusPoint_base_eq_holUnif_ex hxb, Out.DegPre.cF, Out.DegPre.cF, ← hct, ← hct, ← comp_lift, ← comp_lift]
        exact toUnit_TF_comp_left _
      have hm := g.mult (ε x) (ε y)
      rw [← map_add ε] at hm
      have h0 := genVal_corr (u := u) D.P.isLB hm (y := 𝟙 (Sp ℂ))
        (z := Sum.elim ![A.ct (x + y) + z, A.ct (x + y), z, 0] (cubeLift ![A.ct x, A.ct y, z]))
        (z' := Sum.elim ![A.ct x + z, A.ct x, z, 0] ![A.ct y + z, A.ct y, z, 0])
        (by
          rintro (k | k)
          · exact hl _ k
          · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hp).trans (isLift_cube u _ k)))
        (by
          rintro (k | k)
          · exact hl _ k
          · exact hl _ k)
        (fun f => by
          erw [Fintype.prod_sum_type, Fintype.prod_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr]
          erw [show ∏ I : thK, f (cubeLift ![A.ct x, A.ct y, z] I) ^ thε I = _ from
            prod_thK fun I => f (∑ a ∈ I, ![A.ct x, A.ct y, z] a)]
          simp only [sum_three, Finset.sum_singleton, Finset.sum_empty, Matrix.cons_val, Fin.prod_univ_four,
            Out.DegPre.gtε, zpow_neg, zpow_one, map_add]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel)
      have h1 := genVal_mul_of (rfl : genVal u D.P.isLB (g.s (ε (x + y))) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
        ![A.ct (x + y) + z, A.ct (x + y), z, 0] = _) (genVal_pull_of hp
        (genVal_cube_of_face D.P.isLB ah _ D.cub.isGen (D.cub.face 0) _))
      have h2 := genVal_mul_of (rfl : genVal u D.P.isLB (g.s (ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
        ![A.ct x + z, A.ct x, z, 0] = _) (rfl : genVal u D.P.isLB (g.s (ε y))
        (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![A.ct y + z, A.ct y, z, 0] = _)
      exact (_root_.mul_one _).symm.trans (h1.symm.trans (h0.trans h2)))
  obtain ⟨w, hw⟩ := expChar_surjective t
  refine ⟨(w, z), TorusExt.gt_ext (hb w) fun x => ?_⟩
  obtain ⟨x, rfl⟩ := ε.surjective x
  exact TorusExtChar.corr_of_genVal (u := u) D.P.isLB ((ex0 _).isGen _) (g.isGen _) (is_lift_exponential_zero hct hxb (w, z) x) (hl x)
    (fun _ => rfl) ((hxs _ x).trans (congrArg Units.val (DFunLike.congr_fun hw (Multiplicative.ofAdd x))))

include ah hct hxb hxs in

theorem gtAct {oa : D.OAct O} (hact : ∀ (a : O) z, u.ex (A.F a z) = u.ex z ≫ oa.onB.act a) (r : O) (v : A.V) :
    GtAct oa r (ex0 v) (ex0 (A.actV r v)) := by
  refine ⟨by rw [analyticTorusPoint_base_eq_holUnif_ex hxb, analyticTorusPoint_base_eq_holUnif_ex hxb, AnArc.actV_snd, hact, Category.assoc], fun w hw h₀ x => ?_⟩
  obtain ⟨x, rfl⟩ := ε.surjective x
  have hp : 𝟙 (Sp ℂ) ≫ (lift (Out.DegPre.cF D ℂ (ε x)) (ex0 v).b).left =
      (lift (u.ex (A.ct x)) (u.ex v.2)).left := by
    rw [Category.id_comp, analyticTorusPoint_base_eq_holUnif_ex hxb, Out.DegPre.cF, ← hct, ← comp_lift]
    exact toUnit_TF_comp_left _
  rw [← map_smul ε]
  refine TorusExtChar.corr_of_genVal (u := u) D.P.isLB
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ((ex0 _).isGen _) (DVR.pullGen_isGen _ _ _ _ hw _)) ((ex0 _).isGen _)
    (z := Sum.elim ![A.ct (star r • x) + v.2, A.ct (star r • x), v.2, 0]
      (rosatiLift (A.F (star r)) (A.F r) (A.ct x) v.2)) ?_ (is_lift_exponential_zero hct hxb _ x) (fun f => ?_) ?_
  · rintro (k | k)
    · exact is_lift_exponential_zero hct hxb _ _ k
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hp).trans
        (isLift_rosati (hact (star r)) (hact r) _ _ k))
  · erw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, Fin.prod_univ_six, rosatiLift, Out.rosatiε,
      Out.DegPre.gtε, Matrix.cons_val, zpow_neg, zpow_one, A.ct_smul, AnArc.actV_snd]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have h1 := genVal_mul_of (hxs v (star r • x)) (genVal_pull_of hp
      ((genVal_rosati D.P.isLB ah (hact (star r)) (hact r) w hw h₀).2 _ _))
    exact h1.trans ((_root_.mul_one _).trans (hxs (A.actV r v) x).symm)

end Points

theorem corr_of_genVal_frac {B : Over (Sp ℂ)} [GrpObj B] {L : LB B.left} {g : ℕ} {u : HolUnif B L g} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → ((Out.TK ℂ).left ⟶ B.left)} {ε : K → ℤ}
    {φ' : K' → ((Out.TK ℂ).left ⟶ B.left)} {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen) {z : K → Fin g → ℂ} {z' : K' → Fin g → ℂ}
    (hz : IsLift u φ (Out.jFK (R := ℂ) ℂ) z) (hz' : IsLift u φ' (Out.jFK (R := ℂ) ℂ) z')
    (hs : ∀ f : (Fin g → ℂ) → ℂˣ, ∏ k, f (z k) ^ ε k = ∏ k, f (z' k) ^ ε' k)
    (h : genVal u hL t (Out.jFK (R := ℂ) ℂ) z = genVal u hL t' (Out.jFK (R := ℂ) ℂ) z') :
    LB.Gen.Corr L φ ε φ' ε' t t' := by
  have hb : Function.Bijective (algebraMap (FractionRing ℂ) ℂ) := ⟨RingHom.injective _, fun x =>
    ⟨algebraMap ℂ _ x, (IsScalarTower.algebraMap_apply ℂ (FractionRing ℂ) ℂ x).symm⟩⟩
  have : IsIso (CommRingCat.ofHom (algebraMap (FractionRing ℂ) ℂ)) :=
    (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
  have : IsIso (Out.jFK (R := ℂ) ℂ) := inferInstanceAs (IsIso (Spec.map _))
  have c := TorusExtChar.corr_of_genVal (u := u) hL (DVR.pullGen_isGen _ _ _ _ ht (Out.jFK (R := ℂ) ℂ))
    (DVR.pullGen_isGen _ _ _ _ ht' (Out.jFK (R := ℂ) ℂ)) (z := z) (z' := z')
    (fun k => (Category.id_comp _).trans (hz k)) (fun k => (Category.id_comp _).trans (hz' k)) hs
    ((genVal_pull_of (Category.id_comp _) h).trans (genVal_pull_of (Category.id_comp _) rfl).symm)
  refine corr_of_val hL fun y J hJ => ?_
  have e := val_corr hJ c (inv (Out.jFK (R := ℂ) ℂ))
  rw [val_pull hJ, val_pull hJ, IsIso.inv_hom_id] at e
  exact e

section Values

variable {O : Type} [CommRing O] [StarRing O] {A : AnArc O} {D : Out.DegPre ℂ} [Module O D.X] {ε : A.X ≃ₗ[O] D.X}
  {u : HolUnif D.P.A D.P.L A.gB} (lam : u.Λ = A.abelian₂) (ah : u.IsAH A.Hm fun l => A.chi ⟨l, lam.le l.2⟩)
  (rig : u.IsRig D.rig) (hct : ∀ x, u.ex (A.ct x) = D.c (ε x))
  (hψ : ∀ x, genVal u D.P.isLB (D.psi (ε x)) (Out.jFK (R := ℂ) ℂ) (fun _ => A.ct x) = A.psi x)

include hct in

theorem jFK_xK (x : A.X) : Out.jFK (R := ℂ) ℂ ≫ D.xK (ε x) = (u.ex (A.ct x)).left := by
  rw [hct]; exact ArcModel.jFK_comp_point _

theorem jFK_eSec : Out.jFK (R := ℂ) ℂ ≫ (toUnit (Out.TK ℂ)).left ≫ eSec D.P.A = (u.ex 0).left := by
  rw [← Category.assoc, ArcModel.jFK_comp_toUnit, ex_zero, Category.id_comp]
  rfl

variable (A) in

def tauLift (x y : A.X) : ((PUnit ⊕ PUnit) ⊕ PUnit) ⊕ PUnit → Fin A.gB → ℂ :=
  Sum.elim (Sum.elim (Sum.elim (fun _ => A.ct (x + y)) (fun _ => A.ct x)) (fun _ => A.ct y)) (fun _ => 0)

include hct in

theorem isLift_tau (x y : A.X) :
    IsLift u (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => D.xK (ε x + ε y)) (fun _ : PUnit => D.xK (ε x)))
      (fun _ : PUnit => D.xK (ε y))) (fun _ : PUnit => (toUnit (Out.TK ℂ)).left ≫ eSec D.P.A))
      (Out.jFK (R := ℂ) ℂ) (tauLift A x y) := by
  rintro (((_ | _) | _) | _)
  · exact (by rw [map_add]; rfl : _ = Out.jFK (R := ℂ) ℂ ≫ D.xK (ε (x + y))).trans (jFK_xK hct _)
  · exact jFK_xK hct _
  · exact jFK_xK hct _
  · exact jFK_eSec

omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem tau_isGen (D : Out.DegPre ℂ) (a b : D.X) : (D.tau a b).IsGen :=
  DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (DVR.invGen_isGen _ _ _ _ (D.psi_gen _)))
    (DVR.invGen_isGen _ _ _ _ (D.psi_gen _))) (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ D.rig_gen _))

include rig in

theorem genVal_rigK : genVal u D.P.isLB D.rigK (Out.jFK (R := ℂ) ℂ) (fun _ => 0) = 1 :=
  genVal_pull_of (f := (toUnit (Out.TK ℂ)).left) (y := Out.jFK (R := ℂ) ℂ) jFK_comp_jK_complex
    (genVal_rig D.P.isLB rig)

include rig hψ in

theorem genVal_tau (x y : A.X) :
    genVal u D.P.isLB (D.tau (ε x) (ε y)) (Out.jFK (R := ℂ) ℂ) (tauLift A x y) = eTwoPi (A.T x y) := by
  have h1 := hψ (x + y)
  rw [map_add ε] at h1
  refine (genVal_mul_of (genVal_mul_of (genVal_mul_of h1 (genVal_inv_of (hψ x))) (genVal_inv_of (hψ y)))
    (genVal_inv_of (genVal_rigK rig))).trans ?_
  have n1 := (A.psi x).ne_zero
  have n2 := (A.psi y).ne_zero
  rw [A.psi_add]
  field_simp

include lam ah hct hψ in

theorem psiEven : D.PsiEven := by
  intro x
  obtain ⟨x, rfl⟩ := ε.surjective x
  rw [← map_neg ε]
  refine corr_of_genVal_frac (u := u) D.P.isLB
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (DVR.pullGen_isGen _ _ _ _ D.sym_gen _)) (D.psi_gen _)
    (z := Sum.elim (fun _ => A.ct (-x)) ![-A.ct x, A.ct x]) (z' := fun _ => A.ct x) ?_ (fun _ => jFK_xK hct x)
    (fun f => by simp [Fintype.prod_sum_type]) ?_
  · rintro (_ | k)
    · exact jFK_xK hct _
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (jFK_xK hct x)).trans (isLift_sym u _ k))
  · refine (genVal_mul_of (hψ (-x)) (genVal_pull_of (jFK_xK hct x)
      ((genVal_sym D.P.isLB ah D.sym D.sym_gen D.sym_rig).1 _))).trans (Eq.trans ?_ (hψ x).symm)
    rw [A.psi_neg, _root_.mul_one]

include lam ah rig hct hψ in

theorem tauBal (a : O) {f f' : D.P.A ⟶ D.P.A} (hf : ∀ z, u.ex (A.F a z) = u.ex z ≫ f)
    (hf' : ∀ z, u.ex (A.F (star a) z) = u.ex z ≫ f') : D.TauBal f f' (fun y => a • y) (fun y => star a • y) := by
  intro r hr h₀ x y
  obtain ⟨x, rfl⟩ := ε.surjective x
  obtain ⟨y, rfl⟩ := ε.surjective y
  have hp : Out.jFK (R := ℂ) ℂ ≫ D.pt2 (ε x) (ε y) = (lift (u.ex (A.ct x)) (u.ex (A.ct y))).left := by
    rw [← ArcModel.jFK_comp_point]
    simp only [comp_lift, Out.DegPre.pt2, ← hct]
  beta_reduce
  rw [← map_smul ε, ← map_smul ε]
  refine corr_of_genVal_frac (u := u) D.P.isLB
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (tau_isGen D _ _) (DVR.pullGen_isGen _ _ _ _ hr _)) (tau_isGen D _ _)
    (z := Sum.elim (tauLift A (a • x) y) (rosatiLift (A.F a) (A.F (star a)) (A.ct x) (A.ct y)))
    (z' := tauLift A x (star a • y)) ?_ (isLift_tau hct _ _) (fun f => ?_) ?_
  · rintro (k | k)
    · exact isLift_tau hct _ _ k
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hp).trans (isLift_rosati hf hf' _ _ k))
  · simp [Fintype.prod_sum_type, tauLift, rosatiLift, Out.rosatiε, Fin.prod_univ_six, A.ct_smul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · refine (genVal_mul_of (genVal_tau rig hψ _ _) (genVal_pull_of hp
      ((genVal_rosati D.P.isLB ah hf hf' r hr h₀).2 _ _))).trans (Eq.trans ?_ (genVal_tau rig hψ _ _).symm)
    rw [A.T_adj, _root_.mul_one]

include hct hψ in

theorem psiUnitOn (y : D.X) : PsiUnitOn D y Set.univ := by
  obtain ⟨x, rfl⟩ := ε.surjective y
  obtain ⟨t, ht, hv⟩ := TorusExtChar.exists_genVal (u := u) D.P.isLB (φ := fun _ : PUnit => (D.c (ε x)).left)
    (fun _ => -1) (z := fun _ => A.ct x) (fun _ => (Category.id_comp _).trans (by rw [hct])) (A.psi x).ne_zero
  exact (ArcPull.psiUnitOn_univ_iff D _).2 ⟨t, ht, corr_of_genVal_frac (u := u) D.P.isLB
    (DVR.pullGen_isGen _ _ _ _ ht _) (D.psi_gen _) (z := fun _ => A.ct x) (z' := fun _ => A.ct x)
    (fun _ => jFK_xK hct x) (fun _ => jFK_xK hct x) (fun _ => rfl)
    ((genVal_pull_of jFK_comp_jK_complex hv).trans (hψ x).symm)⟩

end Values

section Primitive

variable {O : Type} [CommRing O] [StarRing O] {A : AnArc O} {B : Over (Sp ℂ)} [GrpObj B] {L : LB B.left}
  {u : HolUnif B L A.gB} (hL : L.IsLB) (lam : u.Λ = A.abelian₂) (ah : u.IsAH A.Hm fun l => A.chi ⟨l, lam.le l.2⟩)
  {w : O} {f : B ⟶ B} (hf : ∀ z, u.ex (A.F w z) = u.ex z ≫ f)

omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

include hf in

theorem isLift_prim (z : Fin A.gB → ℂ) :
    IsLift u (K := Fin 4) ![(padd B (𝟙 _) f).left, 𝟙 B.left, f.left, (toUnit B ≫ η[B]).left] (u.ex z).left
      ![z + A.F w z, z, A.F w z, 0] := fun k => by
  fin_cases k
  · change (u.ex z ≫ (𝟙 B * f)).left = (u.ex (z + A.F w z)).left
    rw [MonObj.comp_mul, Category.comp_id, u.ex_add, hf]
  · exact Category.comp_id _
  · exact congrArg (·.left) (hf z).symm
  · change (u.ex z ≫ toUnit _ ≫ η[B]).left = (u.ex 0).left
    rw [AnPairing.comp_toUnit_comp, ex_zero]

include ah hf in

theorem genVal_prim (hw : w + star w = 1)
    (t : LB.Gen (LB.LinComb L (K := Fin 4) ![(padd B (𝟙 _) f).left, 𝟙 B.left, f.left, (toUnit B ≫ η[B]).left]
      ![1, -2, -1, 2])) (ht : t.IsGen) (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t (eSec B)) (LB.oneGen L))
    (z : Fin A.gB → ℂ) : genVal u hL t (u.ex z).left ![z + A.F w z, z, A.F w z, 0] = 1 := by
  have dF : Differentiable ℂ (A.F w) := (LinearMap.toContinuousLinearMap (A.F w)).differentiable
  have hd : Differentiable ℂ fun z => genVal u hL t (u.ex z).left ![z + A.F w z, z, A.F w z, 0] := by
    have := differentiable_genVal hL ht (𝟙 _) (q := id) differentiable_id (z := fun z => ![z + A.F w z, z, A.F w z, 0])
      (fun k => by fin_cases k <;> simp <;> fun_prop) (fun z => by rw [id, Category.comp_id]; exact isLift_prim hf z)
    simpa only [id, Category.comp_id] using this
  have key : ∀ z m, A.H (A.F w z) m = A.H z m - A.H z (A.F w m) := fun z m => by
    rw [A.H_F, eq_sub_iff_add_eq, ← A.H_add_right, ← LinearMap.add_apply, ← map_add, add_comm, hw, map_one]
    rfl
  have hc := const_of_norm_periodic u hd (fun l z => by
    let m : A.abelian₂ := ⟨l, lam.le l.2⟩
    let l' : u.Λ := ⟨A.F w l, lam.ge (A.F_mem w _ m.2)⟩
    have e₂ : ![z + l + A.F w (z + l), z + l, A.F w (z + l), 0] = fun k => ![z + A.F w z, z, A.F w z, 0] k +
        ((![l + l', l, l', 0] : Fin 4 → u.Λ) k : Fin A.gB → ℂ) := by
      funext k
      fin_cases k <;> simp [l']
      abel
    beta_reduce
    rw [show u.ex (z + l) = u.ex z by rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one], e₂,
      genVal_add_period hL ah t (isLift_prim hf z), norm_mul]
    refine (congrArg (· * _) ?_).trans (_root_.one_mul _)
    simp only [Fin.prod_univ_four, Matrix.cons_val, ahFactor_zero hL ah, one_zpow, _root_.mul_one]
    simp only [ahFactor, ← A.H_def, norm_mul, norm_zpow, A.chi_norm, _root_.one_mul]
    rw [← norm_zpow, ← norm_zpow, ← norm_zpow, ← norm_mul, ← norm_mul, ← Complex.exp_int_mul, ← Complex.exp_int_mul,
      ← Complex.exp_int_mul, ← Complex.exp_add, ← Complex.exp_add]
    refine (congrArg (fun x => ‖Complex.exp x‖) (a₂ := 0) ?_).trans (by simp)
    have k₁ := key z l
    have k₂ := key l l
    simp only [l', Submodule.coe_add, A.H_add_left, A.H_add_right]
    push_cast
    linear_combination (Real.pi : ℂ) * k₁ + (Real.pi / 2 : ℂ) * k₂)
  refine (hc z 0).trans ?_
  have e : (u.ex 0).left = 𝟙 (Sp ℂ) ≫ eSec B := by rw [ex_zero, Category.id_comp]; rfl
  have hz := isLift_prim hf 0
  rw [e] at hz ⊢
  rw [← genVal_pull, ← genVal_one (u := u) hL (𝟙 (Sp ℂ)) PEmpty.elim]
  refine genVal_corr hL h₀ (fun k => (Category.assoc _ _ _).symm.trans (hz k)) (fun k => k.elim) fun g => ?_
  simp [Fin.prod_univ_four, zpow_neg]

end Primitive

section Dict

variable {O : Type} [CommRing O] [StarRing O] {A : AnArc O} {D : Out.DegPre ℂ} [Module O D.X] {ε : A.X ≃ₗ[O] D.X}
  {u : HolUnif D.P.A D.P.L A.gB} (lam : u.Λ = A.abelian₂) (ah : u.IsAH A.Hm fun l => A.chi ⟨l, lam.le l.2⟩)
  (rig : u.IsRig D.rig) (hct : ∀ x, u.ex (A.ct x) = D.c (ε x))
  (hψ : ∀ x, genVal u D.P.isLB (D.psi (ε x)) (Out.jFK (R := ℂ) ℂ) (fun _ => A.ct x) = A.psi x)

include ah rig hct hψ in

theorem psi_weight_zero_linear_combination (oa : D.OAct O) {w : O} (hw : w + star w = 1) (hf : ∀ z, u.ex (A.F w z) = u.ex z ≫ oa.onB.act w)
    (hT : ∀ x, (A.psi x : ℂ) = eTwoPi (A.T x (w • x)))
    (t : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(padd D.P.A (𝟙 _) (oa.onB.act w)).left, 𝟙 D.P.A.left,
      (oa.onB.act w).left, (toUnit D.P.A ≫ η[D.P.A]).left] ![1, -2, -1, 2])) (ht : t.IsGen)
    (h₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (eSec D.P.A)) (LB.oneGen D.P.L)) : TraceFormTwistIso D oa w := by
  refine ⟨t, ht, h₀, fun x => ?_⟩
  obtain ⟨x, rfl⟩ := ε.surjective x
  rw [← map_smul ε]
  refine corr_of_genVal_frac (u := u) D.P.isLB
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (tau_isGen D _ _) (DVR.pullGen_isGen _ _ _ _ ht _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _) (DVR.pullGen_isGen _ _ _ _ D.rig_gen _))
    (z := Sum.elim (tauLift A x (w • x)) ![A.ct x + A.F w (A.ct x), A.ct x, A.F w (A.ct x), 0])
    (z' := Sum.elim (fun _ => A.ct x) fun _ => 0) ?_ ?_ (fun f => ?_) ?_
  · rintro (k | k)
    · exact isLift_tau hct _ _ k
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (jFK_xK hct x)).trans (isLift_prim hf _ k))
  · rintro (k | k)
    · exact jFK_xK hct x
    · exact jFK_eSec
  · simp [Fintype.prod_sum_type, tauLift, Fin.prod_univ_four, A.ct_smul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    abel
  · refine (genVal_mul_of (genVal_tau rig hψ _ _) (genVal_pull_of (jFK_xK hct x)
      (genVal_prim D.P.isLB lam ah hf hw t ht h₀ _))).trans
      (Eq.trans ?_ (genVal_mul_of (hψ x) (genVal_rigK rig)).symm)
    rw [hT]

include ah rig hct in

theorem exists_torus_extension_point (v : A.V) : ∃ p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex v.2).left ∧
    ∀ x, genVal u D.P.isLB (p.s (ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![A.ct x + v.2, A.ct x, v.2, 0] =
      eTwoPi (v.1 x) := by
  obtain ⟨p, hp, hv⟩ := ((TorusExtChar.points_eq_characters D _ u _ _ (A.ct.comp ε.symm.toAddEquiv.toAddMonoidHom) ah
    rig (fun x => by simpa using hct (ε.symm x)) v.2).1 (v.1.comp ε.symm.toAddEquiv.toAddMonoidHom)).exists
  exact ⟨p, hp, fun x => by simpa using hv (ε x)⟩

def dictOf (oa : D.OAct O) (hact : ∀ (a : O) z, u.ex (A.F a z) = u.ex z ≫ oa.onB.act a) : GtDict D oa where
  A := A
  eX := ε
  u := u
  lam_eq := lam
  isAH := ah
  isRig := rig
  ex_act := hact
  ex_ct := hct
  psi_val x j hj := by
    have hz : IsLift u (fun _ : PUnit => D.xK (ε x)) (Out.jFK (R := ℂ) ℂ) fun _ => A.ct x := fun _ => jFK_xK hct x
    refine (valAt'_gen D.P.isLB (D.psi_gen _) hz ((hz.le_iff j).2 fun _ => hj)).trans ?_
    rw [hψ, FrameValue.frameProd, Fintype.prod_unique, zpow_neg, zpow_one]
  ex₀ v := (exists_torus_extension_point lam ah rig hct v).choose
  ex₀_b := analyticTorusPoint_base_eq_holUnif_ex fun v => (exists_torus_extension_point lam ah rig hct v).choose_spec.1
  chi_val v x j hj :=
    (valAt'_gen D.P.isLB (Out.GtPtF.isGen _ _) (is_lift_exponential_zero hct (fun v => (exists_torus_extension_point lam ah rig hct v).choose_spec.1) v x)
      hj).trans (congrArg (· * _) ((exists_torus_extension_point lam ah rig hct v).choose_spec.2 x))
  add := isAdd lam ah hct (fun v => (exists_torus_extension_point lam ah rig hct v).choose_spec.1)
    fun v => (exists_torus_extension_point lam ah rig hct v).choose_spec.2
  onto := analyticTorusPoint_surjective lam ah hct (fun v => (exists_torus_extension_point lam ah rig hct v).choose_spec.1)
    fun v => (exists_torus_extension_point lam ah rig hct v).choose_spec.2
  lin := gtAct lam ah hct (fun v => (exists_torus_extension_point lam ah rig hct v).choose_spec.1)
    (fun v => (exists_torus_extension_point lam ah rig hct v).choose_spec.2) hact
  ker := isZero_iff lam ah hct (fun v => (exists_torus_extension_point lam ah rig hct v).choose_spec.1)
    fun v => (exists_torus_extension_point lam ah rig hct v).choose_spec.2
  iota := isIota lam ah rig hct hψ (fun v => (exists_torus_extension_point lam ah rig hct v).choose_spec.1)
    fun v => (exists_torus_extension_point lam ah rig hct v).choose_spec.2

end Dict

theorem nonempty_secFn {O : Type} [CommRing O] [StarRing O] {D : Out.DegPre ℂ} [Module O D.X] {oa : D.OAct O}
    (d : GtDict D oa) (hθ : ∀ j : ℕ, 1 ≤ j → ∀ θ,
      d.u.IsThetaFn d.A.Hm (fun l => d.A.chi ⟨l, d.lam_eq.le l.2⟩) j θ → ∃ s, d.u.IsFnPow j s θ) :
    Nonempty d.SecFn := by
  choose e _ he using fun (j : ℕ) (hj : NeZero j) (α : d.A.X) =>
    TwistedTheta.sections_equiv_anArc_theta d.A D d.u _ d.lam_eq
      (fun l l' h => congrArg d.A.chi (Subtype.ext h)) d.isAH j (Nat.one_le_iff_ne_zero.2 hj.ne)
      (hθ j (Nat.one_le_iff_ne_zero.2 hj.ne)) (d.eX α) α (d.ex_ct α)
  refine ⟨⟨fun j hj α => (e j hj α).toEquiv, fun j hj α s z i hi => (he j hj α s z i hi).trans (congrArg₂ (· * ·) rfl ?_)⟩⟩
  simp [GlobalTheory.frameProd, Fin.prod_univ_four, Out.DegPre.famε]

section Data

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (P : Out.PolAV (Sp ℂ))
  (rig : LB.Gen (P.L.pull (eSec P.A))) (rig_gen : rig.IsGen) (cub : CubicalStr P.A ⟨P.L, rig, P.isLB, rig_gen⟩)
  (sym : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(ι[P.A]).left, 𝟙 P.A.left] ![1, -1])) (sym_gen : sym.IsGen)
  (sym_rig : LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ sym (eSec P.A)) (LB.oneGen P.L))
  (u : HolUnif P.A P.L A.gB)

omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem exists_psiGen (y : A.X) :
    ∃ t : LB.Gen (LB.LinComb P.L (K := PUnit) (Y := Sp ℂ) (fun _ => (u.ex (A.ct y)).left) fun _ => -1),
      t.IsGen ∧ genVal u P.isLB t (𝟙 _) (fun _ => A.ct y) = A.psi y :=
  TorusExtChar.exists_genVal P.isLB _ (fun _ => Category.id_comp _) (A.psi y).ne_zero

def degPre : Out.DegPre ℂ where
  P := P
  rig := rig
  rig_gen := rig_gen
  cub := cub
  sym := sym
  sym_gen := sym_gen
  sym_rig := sym_rig
  X := A.X
  c y := u.ex (A.ct y)
  c_add a b := by rw [map_add, u.ex_add]; rfl
  psi y := LB.pullGen P.L _ _ (exists_psiGen A P u y).choose (Out.jK ℂ)
  psi_gen y := DVR.pullGen_isGen _ _ _ _ (exists_psiGen A P u y).choose_spec.1 _

instance : Module O (degPre A P rig rig_gen cub sym sym_gen sym_rig u).X := A.mod

theorem degPre_psi (y : A.X) : genVal u P.isLB ((degPre A P rig rig_gen cub sym sym_gen sym_rig u).psi y)
    (Out.jFK (R := ℂ) ℂ) (fun _ => A.ct y) = A.psi y :=
  genVal_pull_of jFK_comp_jK_complex (exists_psiGen A P u y).choose_spec.2

variable (lam : u.Λ = A.abelian₂) (ah : u.IsAH A.Hm fun l => A.chi ⟨l, lam.le l.2⟩) (hrig : u.IsRig rig) (oa : P.OAct O)
  (hact : ∀ (a : O) z, u.ex (A.F a z) = u.ex z ≫ oa.act a)

def oAct : (degPre A P rig rig_gen cub sym sym_gen sym_rig u).OAct O where
  onB := oa
  c_lin a y := (congrArg u.ex (A.ct_smul a y)).trans (hact a _)
  tau_bal a := tauBal (D := degPre A P rig rig_gen cub sym sym_gen sym_rig u) (ε := LinearEquiv.refl O A.X) lam ah hrig
    (fun _ => rfl) (degPre_psi A P rig rig_gen cub sym sym_gen sym_rig u) a (hact a) (hact (star a))

def dict : GtDict (degPre A P rig rig_gen cub sym sym_gen sym_rig u)
    (oAct A P rig rig_gen cub sym sym_gen sym_rig u lam ah hrig oa hact) :=
  dictOf (D := degPre A P rig rig_gen cub sym sym_gen sym_rig u) (ε := LinearEquiv.refl O A.X) lam ah hrig
    (fun _ => rfl) (degPre_psi A P rig rig_gen cub sym sym_gen sym_rig u) _ hact

end Data

end GlobalTheory.ArcOfModel
