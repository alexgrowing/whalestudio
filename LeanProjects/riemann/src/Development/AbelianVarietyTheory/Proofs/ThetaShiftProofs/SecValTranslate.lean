import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SectionsEquivAnArcTheta

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.TranslateShift

open CubeValues SymmetricSemicharacter EigenNorm FrameValue TwistedTheta ConstFam Out DVR

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]

theorem tf_hom : (TF (R := ℂ) ℂ).hom = 𝟙 (Sp ℂ) := by
  have e : toF (R := ℂ) ℂ = RingHom.id ℂ :=
    RingHom.ext fun x => (IsScalarTower.algebraMap_apply ℂ (FractionRing ℂ) ℂ x).symm
  rw [TF_hom, e]
  exact Spec.map_id _

def basePt : 𝟙_ (Over (Sp ℂ)) ⟶ TF (R := ℂ) ℂ := Over.homMk (𝟙 (Sp ℂ)) ((Category.id_comp _).trans tf_hom)

variable (D : DegPre ℂ)

def sect : D.P.A ⟶ DegPre.BF D ℂ := lift (toUnit _ ≫ basePt) (𝟙 _)

variable {D} {g : ℕ} {u : HolUnif D.P.A D.P.L g}

theorem pt_pr (x : 𝟙_ (Over (Sp ℂ)) ⟶ D.P.A) : (x.left ≫ (sect D).left) ≫ (DegPre.prB D ℂ).left = x.left := by
  rw [← Over.comp_left, ← Over.comp_left, Category.assoc, sect, lift_snd, Category.comp_id]

theorem pt_tr {b : TF (R := ℂ) ℂ ⟶ D.P.A} {bt : Fin g → ℂ} (hb : (show Sp ℂ ⟶ _ from b.left) = (u.ex bt).left)
    (z : Fin g → ℂ) : (((u.ex z).left ≫ (sect D).left) ≫ (DegPre.trPt D ℂ b).left) ≫ (DegPre.prB D ℂ).left =
      (u.ex (z + bt)).left := by
  have e : basePt ≫ b = u.ex bt := Over.OverMorphism.ext ((Category.id_comp _).trans hb)
  rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, Category.assoc, tr_pr, MonObj.comp_mul, u.ex_add,
    Category.assoc, Category.assoc, sect, lift_snd, lift_fst_assoc, Category.comp_id, Category.assoc, comp_const, e]

theorem pt_zero : (u.ex 0).left ≫ (sect D).left = (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ≫ (DegPre.zF D ℂ).left := by
  have : u.ex 0 ≫ sect D = basePt ≫ DegPre.zF D ℂ := by
    rw [sect, DegPre.zF, comp_lift, comp_lift, ← Category.assoc, Subsingleton.elim (_ ≫ toUnit _) (𝟙 _),
      Category.id_comp, Category.comp_id, Category.comp_id, ex_zero]
    exact congrArg _ (MonObj.comp_one _).symm
  exact congrArg (fun m => m.left) this

theorem isLift_famF {Z : Sp ℂ ⟶ (DegPre.BF D ℂ).left} {α : D.X} {c z : Fin g → ℂ} (hc : u.ex c = D.c α)
    (hZ : Z ≫ (DegPre.prB D ℂ).left = (u.ex z).left) : IsLift u (DegPre.famφ D ℂ α) Z ![z, z + c, c, 0] := fun i => by
  rw [GC.famφ_eq, ← Category.assoc, hZ]
  exact isLift_fam hc z i

def phiLift (c c' bt z : Fin g → ℂ) : Fin 4 ⊕ Fin 4 → Fin g → ℂ :=
  Sum.elim ![z, z + c', c', 0] ![z + bt, z + bt + c, c, 0]

theorem isLift_phi {b : TF (R := ℂ) ℂ ⟶ D.P.A} {bt : Fin g → ℂ} (hb : (show Sp ℂ ⟶ _ from b.left) = (u.ex bt).left)
    {α y : D.X} {c c' : Fin g → ℂ} (hc : u.ex c = D.c α) (hc' : u.ex c' = D.c (α + y)) (z : Fin g → ℂ) :
    IsLift u (DegPre.phiφ D ℂ y α b) ((u.ex z).left ≫ (sect D).left) (phiLift c c' bt z) := by
  rintro (i | i)
  · exact isLift_famF hc' (pt_pr _) i
  · exact (Category.assoc _ _ _).symm.trans (isLift_famF hc (pt_tr hb z) i)

variable {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem genVal_phi (h : u.IsAH Hm χ) {b : TF (R := ℂ) ℂ ⟶ D.P.A} {bt : Fin g → ℂ}
    (hb : (show Sp ℂ ⟶ _ from b.left) = (u.ex bt).left)
    {α y : D.X} {c c' : Fin g → ℂ} (hc : u.ex c = D.c α) (hc' : u.ex c' = D.c (α + y)) {k : ℕ} {l : Fin g → ℂ}
    (hl : k • bt + c = c' + l) (w : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D ℂ y α b) (DegPre.deltaε k)))
    (hw : w.IsGen) (z : Fin g → ℂ) :
    genVal u D.P.isLB w ((u.ex z).left ≫ (sect D).left) (phiLift c c' bt z) =
      Complex.exp (-(Real.pi * hermForm Hm z l)) *
        genVal u D.P.isLB w ((u.ex 0).left ≫ (sect D).left) (phiLift c c' bt 0) := by
  obtain ⟨U, hU⟩ : ∃ U : (Fin g → ℂ) → ℂ,
    ∀ z, U z = genVal u D.P.isLB w ((u.ex z).left ≫ (sect D).left) (phiLift c c' bt z) := ⟨_, fun _ => rfl⟩
  have hd : Differentiable ℂ U := by
    have := differentiable_genVal D.P.isLB hw (sect D).left (q := id) differentiable_id
      (z := fun z => phiLift c c' bt z)
      (by rintro (i | i) <;> fin_cases i <;> simp [phiLift] <;> fun_prop) (fun z => isLift_phi hb hc hc' z)
    simpa only [id, ← hU] using this
  have hper : ∀ (m : u.Λ) z, U (z + m) = Complex.exp (-(Real.pi * hermForm Hm l m)) * U z := fun m z => by
    have e : phiLift c c' bt (z + m) = fun i => phiLift c c' bt z i +
        ((Sum.elim ![m, m, 0, 0] ![m, m, 0, 0] : Fin 4 ⊕ Fin 4 → u.Λ) i : Fin g → ℂ) := by
      funext i
      rcases i with i | i <;> fin_cases i <;> simp [phiLift] <;> abel
    rw [hU, hU, ex_add_period u z m m.2, e, genVal_add_period D.P.isLB h w (isLift_phi hb hc hc' z)]
    congr 1
    have n := ahFactor_ne_zero h m z
    have n' := Complex.exp_ne_zero (Real.pi * hermForm Hm bt m)
    have e' := congrArg (fun x => Complex.exp (Real.pi * hermForm Hm x m)) hl
    simp only [hermForm_add_left, mul_add, Complex.exp_add, exp_nsmul] at e'
    simp only [Fintype.prod_sum_type, Fin.prod_univ_four, DegPre.deltaε, DegPre.famε, phiLift, Sum.elim_inl,
      Sum.elim_inr, Matrix.cons_val, ahFactor_zero D.P.isLB h, ahFactor_translate, zpow_neg, mul_zpow,
      zpow_one, one_zpow, _root_.mul_one, zpow_sub₀ n, zpow_sub₀ n', zpow_natCast, Complex.exp_neg]
    field_simp
    linear_combination -e'
  have dH : Differentiable ℂ fun z => hermForm Hm z l := by
    simp only [hermForm, dotProduct]
    fun_prop
  have hc := const_of_norm_periodic u (F := fun z => U z * Complex.exp (Real.pi * hermForm Hm z l))
    (hd.mul (dH.const_mul _).cexp) (fun m z => by
      simp only [hper, hermForm_add_left, norm_mul, Complex.norm_exp]
      rw [mul_comm (Real.exp _), _root_.mul_assoc, ← Real.exp_add, hermForm_conj Hm h.1 l m]
      congr 2
      simp
      ring) z 0
  simp only [hermForm_zero_left, mul_zero, Complex.exp_zero, _root_.mul_one] at hc
  rw [← hU, ← hU, ← hc, Complex.exp_neg]
  field_simp

theorem genVal_phi_zero {p : GtPtF D ℂ} {bt : Fin g → ℂ}
    (hb : (show Sp ℂ ⟶ _ from p.b.left) = (u.ex bt).left)
    {α y : D.X} {c c' : Fin g → ℂ} (hc : u.ex c = D.c α) (hc' : u.ex c' = D.c (α + y)) {k : ℕ}
    {v : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D ℂ p.b) (DegPre.lineε k))}
    {w : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D ℂ y α p.b) (DegPre.deltaε k))}
    (hw : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ w (DegPre.zF D ℂ).left)
      (LB.mulGen D.P.L _ _ _ _ (p.s α) v)) :
    genVal u D.P.isLB w ((u.ex 0).left ≫ (sect D).left) (phiLift c c' bt 0) =
      genVal u D.P.isLB (p.s α) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + bt, c, bt, 0] *
        genVal u D.P.isLB v (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![0, bt] := by
  have hz := isLift_phi hb hc hc' 0
  rw [pt_zero] at hz ⊢
  rw [← genVal_pull]
  have e : basePt ≫ p.b = u.ex bt := Over.OverMorphism.ext ((Category.id_comp _).trans hb)
  have a : ∀ (q : TF (R := ℂ) ℂ ⟶ D.P.A) x, basePt ≫ q = u.ex x →
      (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ≫ q.left = (u.ex x).left := fun q x hq => congrArg (fun m => m.left) hq
  have e₁ : basePt ≫ DegPre.cF D ℂ α = u.ex c := by
    rw [← Category.assoc, Subsingleton.elim (basePt ≫ toUnit _) (𝟙 _), Category.id_comp, hc]
  have e₀ : basePt ≫ DegPre.zeroF D ℂ = u.ex 0 := (MonObj.comp_one _).trans (ex_zero u).symm
  refine (genVal_corr D.P.isLB hw (z' := Sum.elim ![c + bt, c, bt, 0] ![0, bt])
    (fun i => (Category.assoc _ _ _).symm.trans (hz i)) ?_ fun f => ?_).trans (genVal_mul _ _ _ _ _)
  · rintro (i | i) <;> fin_cases i
    · exact a _ (c + bt) ((MonObj.comp_mul _ _ _).trans (by rw [e, e₁, u.ex_add]))
    · exact a _ _ e₁
    · exact a _ _ e
    · exact a _ _ e₀
    · exact a _ _ e₀
    · exact a _ _ e
  · simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_two, DegPre.deltaε, DegPre.famε, phiLift,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val, DegPre.gtε, DegPre.lineε, zero_add, add_comm bt c]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    module

omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem secVal_congr {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {u : HolUnif A L g} (hL : L.IsLB)
    {Y Y' : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ A.left)} {φ' : K → (Y' ⟶ A.left)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb L φ ε)} {s' : LB.Sec (LB.LinComb L φ' ε)} {y : Sp ℂ ⟶ Y} {y' : Sp ℂ ⟶ Y'}
    (h : sval s y pt (chartAt hL) = sval s' y' pt (chartAt hL)) {z : K → Fin g → ℂ}
    (hz : IsLift u φ y z) (hz' : IsLift u φ' y' z) :
    FrameValue.secVal u hL s y z = FrameValue.secVal u hL s' y' z := by
  refine congrArg₂ (· / ·) (toStalk.injective ?_) ?_
  · exact (gs_eq_toStalk _ _ (le_wchart_chartAt hL φ y) _).symm.trans
      (h.trans (gs_eq_toStalk _ _ (le_wchart_chartAt hL φ' y') _))
  · simp only [hz _, hz' _]

theorem secVal_translate (hG : GlobalFnsSt) (h : u.IsAH Hm χ) {k : ℕ} {q : QkPt D ℂ k} {bt : Fin g → ℂ}
    (hb : (show Sp ℂ ⟶ _ from q.g.b.left) = (u.ex bt).left)
    {v : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D ℂ q.g.b) (DegPre.lineε k))} (hv : v.IsGen)
    {α α' : D.X} (hα : α + q.y = α') {c c' : Fin g → ℂ} (hc : u.ex c = D.c α) (hc' : u.ex c' = D.c α') {l : Fin g → ℂ}
    (hl : k • bt + c = c' + l) {s : D.SecB k α} {t : D.SecB k (α + q.y)} {t' : D.SecB k α'}
    (hst : ThetaTranslate.IsPhiTranslate D ℂ k q v α s t) (ht : HEq t t') (z : Fin g → ℂ) :
    secVal u D.P.isLB t' (u.ex z).left ![z, z + c', c', 0] =
      secVal u D.P.isLB s (u.ex (z + bt)).left ![z + bt, z + bt + c, c, 0] *
        (Complex.exp (-(Real.pi * hermForm Hm z l)) *
          (genVal u D.P.isLB (q.g.s α) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + bt, c, bt, 0] *
            genVal u D.P.isLB v (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![0, bt])) := by
  subst hα
  obtain rfl := eq_of_heq ht
  obtain ⟨⟨w, hw, hw₀⟩, -⟩ := gen_phi hG q v hv α
  rw [← genVal_phi_zero hb hc hc' hw₀, ← genVal_phi h hb hc hc' hl w hw]
  have hJ := good_chartAt (L := D.P.L) D.P.isLB
  have e := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ w).1 (hst w hw hw₀) _ ((u.ex z).left ≫ (sect D).left) pt _ hJ
  rw [sval_resF D ℂ s _ hJ, pt_tr hb] at e
  have e₁ := secVal_eq_mul D.P.isLB e (isLift_famF hc' (pt_pr _)) (isLift_fam hc (z + bt)) (isLift_phi hb hc hc' z)
    fun f => by
      refine Eq.symm ((congrArg (_ * ·) (Fintype.prod_sum_type _)).trans ?_)
      simp only [DegPre.deltaε, phiLift, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      exact (mul_left_comm _ _ _).trans (by rw [mul_inv_cancel, _root_.mul_one])
  refine Eq.trans ?_ e₁
  refine secVal_congr D.P.isLB ?_ (isLift_fam hc' z) (isLift_famF hc' (pt_pr _))
  rw [sval_resF D ℂ t _ hJ, pt_pr]

omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem fn_translate : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (Λ : GtAn a) (k : ℕ) [NeZero k] (la : Λ.A.La) (q : Out.QkPt a.D₀ ℂ k) (v : LB.Gen (LB.LinComb a.D₀.P.L (Out.DegPre.lineφ a.D₀ ℂ q.g.b) (Out.DegPre.lineε k))), q.y = Λ.ε la.y → q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 la) → v.IsGen → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (α : Λ.A.X) (s : a.D₀.SecB k (Λ.ε α)) (t : a.D₀.SecB k (Λ.ε α + q.y)) (t' : a.D₀.SecB k (Λ.ε (α + la.y))), ThetaTranslate.IsPhiTranslate a.D₀ ℂ k q v (Λ.ε α) s t → HEq t t' → Λ.fn k (α + la.y) t' = κ • Λ.A.shift k la α (Λ.fn k α s) := by
  intro hL _ E _ _ _ H _ D l c O _ β _ _ b a Λ k _ la q v hy hg hv
  have hk : (k : ℂ) ≠ 0 := NeZero.ne _
  have hb : (show Sp ℂ ⟶ _ from q.g.b.left) = (Λ.u.ex ((k : ℂ)⁻¹ • (Λ.A.P0 la).2)).left := by
    rw [hg]; exact Λ.ex0_b _
  have hs : ∀ α, genVal Λ.u a.D₀.P.isLB (q.g.s (Λ.ε α)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
      ![Λ.A.ct α + (k : ℂ)⁻¹ • (Λ.A.P0 la).2, Λ.A.ct α, (k : ℂ)⁻¹ • (Λ.A.P0 la).2, 0] =
      eTwoPi ((Λ.A.P0 la).1 α / k) := fun α => by
    rw [hg]
    refine (Λ.arcDict_expZero_section _ α).trans (congrArg _ ?_)
    rw [div_eq_inv_mul]
    rfl
  refine ⟨genVal Λ.u a.D₀.P.isLB v (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![0, (k : ℂ)⁻¹ • (Λ.A.P0 la).2],
    genVal_ne_zero _ _ fun i => ?_, fun α s t t' hst ht => funext fun z => ?_⟩
  · fin_cases i
    · exact congrArg (fun m => m.left)
        ((MonObj.comp_one _).trans (ex_zero Λ.u).symm : basePt ≫ DegPre.zeroF a.D₀ ℂ = Λ.u.ex 0)
    · exact (Category.id_comp _).trans hb
  · refine (secVal_translate hL.globalFns Λ.ah hb hv (by rw [map_add, hy]) (Λ.ct α) (Λ.ct (α + la.y))
      (l := la.l) ?_ hst ht z).trans ?_
    · rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk, AnArc.degeneratingTori_basePeriodMap_snd, map_add]
      abel
    · rw [hs, Pi.smul_apply, smul_eq_mul, AnArc.shift_apply', GtAn.fn, AnArc.H_def]
      ring

end GlobalTheory.TranslateShift
