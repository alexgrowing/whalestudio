import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamCoefVal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistBaseChangeOfFinrankSectionsOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestQuadraticFormEqPsiValuationMul
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationsTorusExtensionPoints

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.TermSize

theorem exists_rat_log {p : ℕ} [hp : Fact p.Prime] {x : PadicAlgCl p} (hx : x ≠ 0) :
    ∃ q : ℚ, Real.log ‖x‖ = q * Real.log p := by
  have e := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow ℚ_[p] (PadicAlgCl p) x
  rw [PadicAlgCl.spectralNorm_eq] at e
  have h0 : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral x) hx
  refine ⟨-((minpoly ℚ_[p] x).coeff 0).valuation / (minpoly ℚ_[p] x).natDegree, ?_⟩
  rw [e, Real.log_rpow (norm_pos_iff.2 h0), Padic.norm_eq_zpow_neg_valuation h0, Real.log_zpow]
  push_cast
  ring

theorem exists_addValuation {p : ℕ} [hp : Fact p.Prime] {π : PadicAlgCl p} (h0 : π ≠ 0) (h1 : ‖π‖ < 1) :
    ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), ∀ (x : PadicAlgCl p) (q : ℚ),
      ((q : WithTop ℚ) ≤ v x ↔ ‖x‖ ≤ Real.exp (-(q * -Real.log ‖π‖))) ∧
      (v x ≤ (q : WithTop ℚ) ↔ Real.exp (-(q * -Real.log ‖π‖)) ≤ ‖x‖) := by
  have hc : 0 < -Real.log ‖π‖ := neg_pos.2 (Real.log_neg (norm_pos_iff.2 h0) h1)
  have ex : ∀ x : PadicAlgCl p, ∃ q : ℚ, x ≠ 0 → ‖x‖ = Real.exp (-(q * -Real.log ‖π‖)) := fun x => by
    by_cases hx : x = 0
    · exact ⟨0, fun h => absurd hx h⟩
    obtain ⟨a, ha⟩ := exists_rat_log hx
    obtain ⟨b, hb⟩ := exists_rat_log h0
    have hb0 : (b : ℝ) ≠ 0 := fun h => by rw [hb, h] at hc; simp at hc
    refine ⟨a / b, fun _ => ?_⟩
    rw [← Real.exp_log (norm_pos_iff.2 hx), ha, hb]
    congr 1
    push_cast
    field_simp
  generalize -Real.log ‖π‖ = c at hc ex
  classical
  choose r hr using ex
  have mono : ∀ a b : ℚ, Real.exp (-(a * c)) ≤ Real.exp (-(b * c)) ↔ b ≤ a := fun a b => by
    rw [Real.exp_le_exp, neg_le_neg_iff, mul_le_mul_iff_left₀ hc, Rat.cast_le]
  let f : PadicAlgCl p → WithTop ℚ := fun x => if x = 0 then ⊤ else r x
  have f0 : f 0 = ⊤ := if_pos rfl
  have fn : ∀ x, x ≠ 0 → f x = r x := fun x hx => if_neg hx
  have key : ∀ x (q : ℚ), ((q : WithTop ℚ) ≤ f x ↔ ‖x‖ ≤ Real.exp (-(q * c))) ∧
      (f x ≤ (q : WithTop ℚ) ↔ Real.exp (-(q * c)) ≤ ‖x‖) := fun x q => by
    by_cases hx : x = 0
    · subst hx
      rw [f0, norm_zero]
      exact ⟨iff_of_true le_top (Real.exp_pos _).le, iff_of_false (by simp) (not_le.2 (Real.exp_pos _))⟩
    · rw [fn x hx, hr x hx, mono, mono, WithTop.coe_le_coe, WithTop.coe_le_coe]
      exact ⟨Iff.rfl, Iff.rfl⟩
  have keq : ∀ x (q : ℚ), ‖x‖ = Real.exp (-(q * c)) → f x = q := fun x q h =>
    le_antisymm ((key x q).2.2 h.ge) ((key x q).1.2 h.le)
  refine ⟨AddValuation.of f f0 (keq 1 0 (by simp)) (fun x y => ?_) (fun x y => ?_), key⟩
  · by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    rw [fn x hx, fn y hy, ← WithTop.coe_min, (key _ _).1]
    refine (IsUltrametricDist.norm_add_le_max x y).trans (max_le ?_ ?_)
    · rw [hr x hx, mono]; exact min_le_left _ _
    · rw [hr y hy, mono]; exact min_le_right _ _
  · by_cases hx : x = 0
    · simp [hx, f0]
    by_cases hy : y = 0
    · simp [hy, f0]
    rw [fn x hx, fn y hy, ← WithTop.coe_add]
    refine keq _ _ ?_
    rw [norm_mul, hr x hx, hr y hy, ← Real.exp_add]
    congr 1
    push_cast
    ring

section
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefBasic IsLocalRing

theorem gs_sum' {Y Z : Scheme.{0}} (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) {I : Type} (A : Finset I)
    (a : I → Γ(Y, U)) : gs f z U (∑ i ∈ A, a i) = ∑ i ∈ A, gs f z U (a i) := by
  simp only [gs_eq f z U h, map_sum]

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem coef_zero_of_sval {g : GtPtF D F} {w : Frm D F k g.b} {s : Fam D F k} {α : D.X}
    (h : ∀ z J, Good D.P.L z J → sval (s.s α) (lift (𝟙 (TF (R := R) F)) g.b).left z J = 0) : coef s g w α = 0 :=
  coef_eq fun z J hJ => by rw [h z J hJ, cst_eq, map_zero, zero_mul, zero_mul, zero_mul]

theorem coef_zero_of_famOf {g : GtPtF D F} {w : Frm D F k g.b} {s : Fam D F k} {f : ∀ α, D.SecB k α}
    (hs : FamOf D F f s) {α : D.X} (h : ∀ j, (f α).f j = 0) : coef s g w α = 0 :=
  coef_zero_of_sval fun z J hJ => by
    rw [← SectionScalarValuation.secScal_sval (hs α) _ z hJ]
    exact UUA.sval_zero_of h _ z J (hJ.mem _ _)

theorem coef_sum {g : GtPtF D F} {w : Frm D F k g.b} (hw : w.IsGen) {I : Type} (A : Finset I) (b : I → F)
    (s : I → Fam D F k) (α : D.X) : coef (∑ i ∈ A, b i • s i) g w α = ∑ i ∈ A, b i * coef (s i) g w α := by
  induction A using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact coef_zero_of_sval fun z J hJ => UUA.sval_zero_of (fun _ => rfl) _ z J (hJ.mem _ _)
  | insert i A hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ((coef_basic R D F k g).2.2 w hw).2.1, ih]

theorem sval_sum {I : Type} (A : Finset I) (b : I → F) (s : I → Fam D F k) (α : D.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J} (hJ : Good D.P.L z J) :
    sval ((∑ i ∈ A, b i • s i).s α) r z J = ∑ i ∈ A, gs r z ⊤ (gF D F (b i)) * sval ((s i).s α) r z J := by
  have hm := hJ.mem (DegPre.famφ D F α) r
  induction A using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact UUA.sval_zero_of (fun _ => rfl) _ z J (hJ.mem _ _)
  | insert i A hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    exact (gs_add _ z _ hm _ _).trans (congrArg₂ (· + ·) ((gs_mul _ z _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_res _ z le_top hm _) rfl)) rfl)

end

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v) {k : ℕ}

theorem vge_of_secScal {α : D.toPre.X} {σ : D.toPre.SecB k α} {s}
    (h : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) s
      (D.toPre.famφB α) (DegPre.famε k) σ (DegPre.prB D.toPre F).left 1) : VGe D F v k α s 0 :=
  ⟨1, fun _ => 1, fun _ => σ, fun _ => s, fun _ => h, fun _ => by rw [AddValuation.map_one]; exact le_rfl, fun j => by
    rw [Fin.sum_univ_one, DVR.constBF_eq, map_one]
    simp [resTop]⟩

theorem cst_prB (y : (DegPre.BF D.toPre F).left) (a : V) :
    Geo.Tor.cst ((𝟙 _ ≫ (DegPre.prB D.toPre F).left) ≫ D.toPre.P.A.hom) y a =
      gs (𝟙 _) y ⊤ (gF D.toPre F (TWO.algVF a)) := by
  have e : (𝟙 _ ≫ (DegPre.prB D.toPre F).left) ≫ D.toPre.P.A.hom =
      (𝟙 _ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) ≫ Spec.map (CommRingCat.ofHom (TWO.algVF (F := F) (V := V))) := by
    rw [← TWM.TF_hom, Category.assoc, Category.assoc, Over.w, Over.w]
  have n := congrArg (fun φ => φ.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (TWO.algVF (F := F) (V := V))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  rw [e]
  refine (gs_pull _ _ y ⊤ trivial _).symm.trans (Eq.trans ?_ (gs_pull (𝟙 _) (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ trivial _).symm)
  exact congrArg (gs _ y ⊤) n.symm

include hϖ hv in

theorem exists_comb {α : D.toPre.X} {I : Type} [Fintype I] {β : I → D.toPre.SecB k α} (hβ : IsBasisB D.toPre β)
    (s : I → Fam D.toPre F k)
    (hs : ∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) ((s i).s α)
      (D.toPre.famφB α) (DegPre.famε k) (β i) (DegPre.prB D.toPre F).left 1)
    {t} {r : ℚ} (ht : VGe D F v k α t r) :
    ∃ b : I → F, (∀ i, (r : WithTop ℚ) ≤ v (b i)) ∧ t = (∑ i, b i • s i).s α := by
  obtain ⟨n, a, σ, σF, hσ, ha, hsum⟩ := ht
  choose c hc _ using fun m => hβ (σ m)
  refine ⟨fun i => ∑ m, a m * TWO.algVF (c m i), fun i => AddValuation.map_le_sum v fun m _ => ?_,
    SecOps.sec_ext fun j => sec_ext_val D.toPre.P.isLB (fun y J hJ => ?_) j⟩
  · rw [AddValuation.map_mul]
    exact (ha m).trans (le_add_of_nonneg_right (TWO.v_of_V v hϖ hv _).1)
  · have hm := hJ.mem (D.toPre.famφB α) (𝟙 _ ≫ (DegPre.prB D.toPre F).left)
    have e : ∀ m, sval (σF m) (𝟙 _) y J =
        ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (TWO.algVF (c m i))) * sval ((s i).s α) (𝟙 _) y J := fun m => by
      rw [← SectionScalarValuation.secScal_sval (hσ m) _ y hJ]
      refine (congrArg (gs _ y _) (hc m _)).trans ?_
      refine (gs_sum' _ y _ hm _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
      rw [← SectionScalarValuation.secScal_sval (hs i) _ y hJ, ← cst_prB]
      exact (gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_constFn _ _ _ y hm _) rfl)
    rw [sval_sum _ _ _ _ _ _ hJ, SectionScalarValuation.sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) _ y hJ]
    simp only [e, Finset.mul_sum, gs_eq (𝟙 (DegPre.BF D.toPre F).left) y ⊤ trivial, map_sum, map_mul, Finset.sum_mul,
      _root_.mul_assoc]
    exact Finset.sum_comm

variable {Q : D.toPre.X → ℤ} {g : GtPtF D.toPre F} {w : Frm D.toPre F k g.b} {l : D.toPre.X → ℚ} {ω : ℚ}

theorem le_v_term (hQ : QForm.IsQ D.toPre ϖ Q) (hk : 1 ≤ k) (hw : w.IsGen) (hl : GtV hϖ hv g l)
    (hω : GenV hϖ hv w ω) {s : Fam D.toPre F k} {α₀ : D.toPre.X} (hs : VGe D F v k α₀ (s.s α₀) 0) (m : D.toPre.X) :
    ((((Q (α₀ + k • m) : ℚ) - Q α₀) / k + l (α₀ + k • m) + ω : ℚ) : WithTop ℚ) ≤ v (coef s g w (α₀ + k • m)) := by
  have H := SectionScalarValuation.fe_move hϖ hQ hv k m α₀ s hs
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have e : 0 + ((k * Q m + QForm.bOf D.toPre Q m α₀ : ℤ) : ℚ) = ((Q (α₀ + k • m) : ℚ) - Q α₀) / k := by
    rw [q_shift hϖ hQ α₀ m k]; push_cast; field_simp; ring
  rw [e] at H
  exact CoefVal.le_v_coef hw H (hl _) hω

theorem exists_v_term_le (hLL : LL) [CharZero V] [IsAlgClosed F] (hc : IsAdicComplete (maximalIdeal V) V)
    (hQ : QForm.IsQ D.toPre ϖ Q) (hk : 4 ≤ k) (hw : w.IsGen) (hl : GtV hϖ hv g l) (hω : GenV hϖ hv w ω)
    {α₀ : D.toPre.X} {I : Type} [Fintype I] {β : I → D.toPre.SecB k α₀} (hβ : IsBasisB D.toPre β)
    (s : I → Fam D.toPre F k)
    (hs : ∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α₀) (DegPre.famε k) ((s i).s α₀)
      (D.toPre.famφB α₀) (DegPre.famε k) (β i) (DegPre.prB D.toPre F).left 1) (m : D.toPre.X) :
    ∃ i, v (coef (s i) g w (α₀ + k • m)) ≤
      ((((Q (α₀ + k • m) : ℚ) - Q α₀) / k + l (α₀ + k • m) + ω : ℚ) : WithTop ℚ) := by
  have hT : TwistBaseChangeStatement := GlobalTheory.twistBaseChange_of_finrank_sections_one fun K _ _ P =>
    (hLL.1.globalSectionsRank K P 1 le_rfl).trans (one_pow _)
  have hS := twistBCSpan_of hT
  obtain ⟨t, ht, -, e⟩ := CoefUnit.exists_fam_coef_val hLL hS GlobalTheory.RatioVal.main
    (TWM.tw_of hLL.1.globalFns hS GlobalTheory.RatioVal.main) (GlobalTheory.UnitBallFree.main hLL.1.globalFns hT) V hc ϖ hϖ D Q hQ F v hv k hk g w l ω hw hl hω
    (α₀ + k • m)
  obtain ⟨b, hb, hbt⟩ := exists_comb hϖ hv hβ s hs (ht α₀)
  have e₁ := GlobalTheory.FamFree.eq_of_eq_add_nsmul hLL.1.globalFns t (∑ i, b i • s i) ⟨m, rfl⟩ hbt
  have e₂ : coef t g w (α₀ + k • m) = coef (∑ i, b i • s i) g w (α₀ + k • m) := by
    unfold coef; rw [e₁]
  rw [e₂, coef_sum hw] at e
  by_contra h
  push Not at h
  refine lt_irrefl _ (lt_of_lt_of_eq (AddValuation.map_lt_sum v WithTop.coe_ne_top fun i _ => ?_) e)
  have e₃ : (Q (α₀ + k • m) : ℚ) / k + l (α₀ + k • m) + ω =
      (0 + (Q α₀ : ℚ) / k) + (((Q (α₀ + k • m) : ℚ) - Q α₀) / k + l (α₀ + k • m) + ω) := by ring
  rw [AddValuation.map_mul, e₃, WithTop.coe_add]
  exact (WithTop.add_lt_add_left WithTop.coe_ne_top (h i)).trans_le (add_le_add_left (hb i) _)

end

section
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefBasic IsLocalRing

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem norm_j_unit (a : u.Vˣ) : ‖(u.j a : PadicAlgCl p)‖ = 1 := by
  by_contra h
  exact (not_isUnit_OO_iff _).2 (lt_of_le_of_ne ((mem_OO_iff _).1 (u.j a).2) h) (a.isUnit.map u.j)

theorem v_valF {ϖ : u.V} (hϖ : Irreducible ϖ) {v : AddValuation (PadicAlgCl p) (WithTop ℚ)}
    (hv : ValOver ϖ (PadicAlgCl p) v) (hO : ∀ x, 0 ≤ v x ↔ ‖x‖ ≤ 1) {g : GtPtF u.D.toPre (PadicAlgCl p)}
    {χ : u.D.toPre.X} {r : ℚ} (h : GenV hϖ hv (g.s χ) r) {J} (hJ : u.IntGood J) (hG : ∀ z, Good u.D.toPre.P.L z J) :
    v (valF (𝟙 (Sp (PadicAlgCl p))) _
      ((g.s χ).s (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k))).val) = r := by
  obtain ⟨φ₀, h₀, t₀, ht₀, x, hx, e⟩ := h
  let e₁ : TWO.Ov v →+* OO p := (TWO.Ov v).subtype.codRestrict (OO p) fun x => (mem_OO_iff _).2 ((hO _).1 x.2)
  let e₂ : OO p →+* TWO.Ov v := (OO p).subtype.codRestrict (TWO.Ov v) fun x => (hO _).2 ((mem_OO_iff _).1 x.2)
  have c₁ : spMap e₂ ≫ spMap e₁ = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]; rfl
  have c₂ : gPt p ≫ spMap e₁ = (TWM.ιS hϖ hv).left := by
    rw [← Spec.map_comp]; rfl
  have c₃ : spMap e₁ ≫ (TWM.TO hϖ hv).hom = spMap u.j := (Spec.map_comp _ _).symm.trans rfl
  have c₄ : ∀ i, φ₀ i ≫ u.D.toPre.P.A.hom = (TWM.TO hϖ hv).hom := fun i =>
    CoefVal.ι_inj hϖ hv (X := Sp u.V) (by
      show _ ≫ _ ≫ _ = _ ≫ _
      rw [← Category.assoc, ← h₀ i, Over.w]
      fin_cases i <;> exact Over.w _)
  have le : (⊤ : (TWM.TO hϖ hv).left.Opens) ≤
      LB.wchart u.D.toPre.P.L φ₀ fun i => J ((TWM.ιS hϖ hv).left ≫ φ₀ i) := fun y _ => Set.mem_iInter.2 fun i => by
    have a := hJ (spMap e₁ ≫ φ₀ i) (by rw [Category.assoc, c₄, c₃]) (show spMap e₂ y ∈ ⊤ from trivial)
    rw [← Category.assoc, c₂] at a
    have b : (spMap e₁ ≫ φ₀ i) (spMap e₂ y) = φ₀ i y := by
      rw [← Scheme.Hom.comp_apply, ← Category.assoc, c₁, Category.id_comp]
    have a' : (spMap e₁ ≫ φ₀ i) (spMap e₂ y) ∈ u.D.toPre.P.L.U (J ((TWM.ιS hϖ hv).left ≫ φ₀ i)) := a
    rw [b] at a'
    exact a'
  obtain ⟨z⟩ := exists_pt (R := u.V) (F := PadicAlgCl p)
  let a : Γ(Spec (CommRingCat.of (TWO.Ov v)), ⊤)ˣ := res le (t₀.s fun i => J ((TWM.ιS hϖ hv).left ≫ φ₀ i))
  have ha : v (TWM.ιr (v := v) a.val) = 0 :=
    TWO.v_unit v (Units.map (Scheme.ΓSpecIso (CommRingCat.of (TWO.Ov v))).hom.hom.toMonoidHom a)
  have e' := e z J (hG z)
  have e₃ : (val t₀ (TWM.ιS hϖ hv).left z J).val = UT.cst (R := u.V) (PadicAlgCl p) z (TWM.ιr (v := v) a.val) := by
    rw [← CoefVal.gs_ι hϖ hv]
    exact ((gs_unit _ z ⊤ trivial a).trans (congrArg Units.val (gm_res _ z le trivial _))).symm
  rw [e₃, val_of (g.s χ) _ z J (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k))
    (fun k => by rw [Category.id_comp]), cst_eq, cst_eq, ← map_mul] at e'
  have e₄ := (toStk_valF (𝟙 (Sp (PadicAlgCl p))) _ z (Set.mem_iInter.2 fun k =>
    hG z (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k)) _).trans e'
  have e₅ := cstH_inj (R := u.V) z e₄
  refine (congrArg v e₅).trans ?_
  rw [AddValuation.map_mul, hx, ha, add_zero]

end

theorem term_sizes : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 4 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → ∀ s : J → Fam u.D.toPre (PadicAlgCl p) k, (∀ i, FamOf u.D.toPre _ (f i) (s i)) → ∀ (g : GtPtF u.D.toPre (PadicAlgCl p)) (ν : u.D.toPre.X → ℝ) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b), u.GtN g ν → w.IsGen → ∃ κ : ℝ, 0 < κ ∧ ∀ α, (∀ i, GlobalTheory.UT.coef (s i) g w α ≠ 0 → ∃ m, α = cls i + k • m) ∧ (∀ i, ‖GlobalTheory.UT.coef (s i) g w α‖ ≤ κ * Real.exp (-((l.q α - l.q (cls i)) / k + ν α))) ∧ ∃ i, ‖GlobalTheory.UT.coef (s i) g w α‖ = κ * Real.exp (-((l.q α - l.q (cls i)) / k + ν α)) := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u l k hk J _ σ cls f hB s hs g ν w hν hw
  obtain ⟨-, hcl, hall, -, -, hzero, hbas⟩ := hB
  obtain ⟨ϖ, Q, hϖ, hQ, h1, hq⟩ := GlobalTheory.ZH.PsiForm.q_eq_val_mul o Ω S ρ p y₀ u l
  obtain ⟨⟨I, hI, hG⟩, -⟩ := GlobalTheory.ZH.TorusVal.main hLL o Ω S ρ p y₀ u l
  have hinj : Function.Injective (DVR.TWO.algVF (F := PadicAlgCl p) (V := u.V)) :=
    (algebraMap (FractionRing u.V) (PadicAlgCl p)).injective.comp (IsFractionRing.injective u.V _)
  have : CharZero u.V := (RingHom.charZero_iff hinj).2 inferInstance
  have h0 : (u.j ϖ : PadicAlgCl p) ≠ 0 := fun h => hϖ.ne_zero (hinj (h.trans (map_zero _).symm))
  obtain ⟨v, key⟩ := exists_addValuation h0 h1
  have keq : ∀ x (q : ℚ), v x = q ↔ ‖x‖ = Real.exp (-(q * -Real.log ‖(u.j ϖ : PadicAlgCl p)‖)) := fun x q => by
    rw [le_antisymm_iff, le_antisymm_iff, (key x q).1, (key x q).2, and_comm]
  have hv : DVR.ValOver ϖ (PadicAlgCl p) v := by
    rintro c n ⟨a, rfl⟩
    rw [keq, map_mul, map_zpow₀, norm_mul, norm_zpow]
    show ‖(u.j ϖ : PadicAlgCl p)‖ ^ n * ‖(u.j a : PadicAlgCl p)‖ = _
    rw [norm_j_unit, _root_.mul_one, mul_neg, neg_neg, Rat.cast_intCast, ← Real.log_zpow,
      Real.exp_log (zpow_pos (norm_pos_iff.2 h0) n)]
  have hO : ∀ x, 0 ≤ v x ↔ ‖x‖ ≤ 1 := fun x => by simpa using (key x 0).1
  obtain ⟨lv, hl, -⟩ := UT.CoefVal.exists_gtV (hϖ := hϖ) (hv := hv) g
  obtain ⟨ω, hω⟩ := UT.CoefVal.exists_genV_frm (hϖ := hϖ) (hv := hv) hw
  have hνl : ∀ χ, ν χ = lv χ * -Real.log ‖(u.j ϖ : PadicAlgCl p)‖ := fun χ =>
    neg_injective (Real.exp_injective ((hν I hI χ).symm.trans ((keq _ _).1 (v_valF u hϖ hv hO (hl χ) hI hG))))
  have hexp : ∀ α β : u.D.toPre.X,
      Real.exp (-(((((Q α : ℚ) - Q β) / k + lv α + ω : ℚ) : ℝ) * -Real.log ‖(u.j ϖ : PadicAlgCl p)‖)) =
      Real.exp (-(ω * -Real.log ‖(u.j ϖ : PadicAlgCl p)‖)) * Real.exp (-((l.q α - l.q β) / k + ν α)) := fun α β => by
    rw [← Real.exp_add, hq, hq, hνl]
    congr 1
    push_cast
    ring
  have hsupp : ∀ α i, GlobalTheory.UT.coef (s i) g w α ≠ 0 → ∃ m, α = cls i + k • m := fun α i h => by
    by_contra hn
    exact h (coef_zero_of_famOf (hs i) (hzero i α fun m e => hn ⟨m, e⟩))
  have hle : ∀ α i, ‖GlobalTheory.UT.coef (s i) g w α‖ ≤ Real.exp (-(ω * -Real.log ‖(u.j ϖ : PadicAlgCl p)‖)) *
      Real.exp (-((l.q α - l.q (cls i)) / k + ν α)) := fun α i => by
    by_cases h : GlobalTheory.UT.coef (s i) g w α = 0
    · rw [h, norm_zero]; positivity
    obtain ⟨m, rfl⟩ := hsupp α i h
    rw [← hexp, ← (key _ _).1]
    exact le_v_term hϖ hv hQ (by omega) hw hl hω (vge_of_secScal (hs i _)) m
  refine ⟨_, Real.exp_pos _, fun α => ⟨hsupp α, hle α, ?_⟩⟩
  obtain ⟨i₀, m, rfl⟩ := hall α
  obtain ⟨⟨i, hi⟩, h⟩ := exists_v_term_le hϖ hv hLL u.complete hQ hk hw hl hω (hbas i₀) (fun i => s i)
    (fun i => hs i _) m
  refine ⟨i, le_antisymm (hle _ i) ?_⟩
  rw [hi, ← hexp, ← (key _ _).2]
  exact h

end GlobalTheory.TermSize
end
