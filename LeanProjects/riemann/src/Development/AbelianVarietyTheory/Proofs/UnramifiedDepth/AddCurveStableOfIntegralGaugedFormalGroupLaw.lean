import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

noncomputable section

open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds MvPowerSeries

namespace GlobalTheory.RowLaw.AddCurve

variable {C : Type} [Field C]

theorem intS_mul {V : VF C} {τ : Type} {f g : MvPowerSeries τ C} (hf : IntS V f) (hg : IntS V g) :
    IntS V (f * g) := by
  intro μ
  rw [coeff_mul]
  exact VF.Ge.sum fun p _ => (hf _).mul_int (hg _)

theorem intS_one {V : VF C} {τ : Type} : IntS V (1 : MvPowerSeries τ C) := by
  intro μ
  rw [coeff_one]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem intS_pow {V : VF C} {τ : Type} {f : MvPowerSeries τ C} (hf : IntS V f) (n : ℕ) : IntS V (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact intS_one
  | succ n ih => rw [pow_succ]; exact intS_mul ih hf

theorem intS_subst {V : VF C} {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {F : MvPowerSeries σ C} (hF : IntS V F) :
    IntS V (subst a F) := by
  intro μ
  have hS := hasSubst_of_constantCoeff_zero ha0
  rw [coeff_subst hS, finsum_eq_sum _ (coeff_subst_finite hS F μ)]
  refine VF.Ge.sum fun e _ => ?_
  rw [smul_eq_mul]
  refine (hF e).mul_int ?_
  have : IntS V (e.prod fun s m => a s ^ m) := by
    unfold Finsupp.prod
    exact Finset.prod_induction _ (IntS V) (fun _ _ => intS_mul) intS_one fun s _ => intS_pow (ha s) _
  exact this μ

theorem intS_pderiv {V : VF C} {τ : Type} {f : MvPowerSeries τ C} (hf : IntS V f) (t : τ) :
    IntS V (pderiv C t f) := by
  intro μ
  rw [coeff_pderiv, mul_comm, ← Nat.cast_succ]
  exact (VF.ge_natCast _).mul_int (hf _)

theorem subst_eq_zero_of_van {σ τ : Type} [Finite σ] {T : Set σ} {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (haT : ∀ s ∈ T, a s = 0) {f : MvPowerSeries σ C} (hf : Van T f) :
    subst a f = 0 := by
  have h : Van (∅ : Set τ) (subst a f) :=
    Van.subst T ha0 (fun s hs ν _ => by rw [haT s hs, map_zero]) hf
  ext ν
  rw [h ν (fun _ _ => Set.notMem_empty _), map_zero]

theorem coeff_mul_van {τ : Type} {T : Set τ} {f g : MvPowerSeries τ C} (hf : Van T f) (hg : Van T g)
    (ν : τ →₀ ℕ) (hν : ∀ w ∈ ν.support, w ∉ T) (t : τ) : coeff (ν + Finsupp.single t 1) (f * g) = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hab' : a + b = ν + Finsupp.single t 1 := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  by_cases h : ∀ w ∈ a.support, w ∉ T
  · simp [hf a h]
  · push Not at h
    obtain ⟨w, hw, hwT⟩ := h
    have hb : ∀ w' ∈ b.support, w' ∉ T := by
      intro w' hw' hw'T
      have h1 := Finsupp.mem_support_iff.1 hw
      have h2 := Finsupp.mem_support_iff.1 hw'
      have n1 : ν w = 0 := by
        by_contra hc
        exact hν w (Finsupp.mem_support_iff.2 hc) hwT
      have n2 : ν w' = 0 := by
        by_contra hc
        exact hν w' (Finsupp.mem_support_iff.2 hc) hw'T
      have e1 := DFunLike.congr_fun hab' w
      have e2 := DFunLike.congr_fun hab' w'
      simp only [Finsupp.add_apply, n1, n2, Finsupp.single_apply] at e1 e2
      have t1 : t = w := by
        by_contra hc
        rw [if_neg hc] at e1
        omega
      have t2 : t = w' := by
        by_contra hc
        rw [if_neg hc] at e2
        omega
      subst t1
      subst t2
      rw [if_pos rfl] at e1
      omega
    simp [hg b hb]

theorem van_pderiv_mvExp {τ : Type} {T : Set τ} {H : MvPowerSeries τ C} (hH : Van T H) (t : τ) :
    Van T (pderiv C t (mvExp H) - pderiv C t H) := by
  intro ν hν
  rw [map_sub, coeff_pderiv, coeff_pderiv, ← sub_mul]
  have : coeff (ν + Finsupp.single t 1) (mvExp H) = coeff (ν + Finsupp.single t 1) H := by
    show ∑ k ∈ Finset.range ((ν + Finsupp.single t 1).degree + 1),
      coeff (ν + Finsupp.single t 1) (H ^ k) / (k.factorial : C) = _
    rw [Finset.sum_eq_single 1]
    · simp
    · intro k _ hk
      rcases k with _ | _ | k
      · rw [pow_zero, coeff_one, if_neg, zero_div]
        intro h
        have := DFunLike.congr_fun h t
        simp at this
      · exact absurd rfl hk
      · rw [pow_succ', pow_succ', coeff_mul_van hH (hH.mul_right _) ν hν t, zero_div]
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range, map_add, Finsupp.degree_single]
      omega
  rw [this, sub_self, zero_mul]

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def fstEmb (κ : Type) : κ ↪ Fin 2 × κ := ⟨fun x => (0, x), fun _ _ h => (Prod.ext_iff.1 h).2⟩

theorem subst_killCompl {τ : Type} {γ : κ → MvPowerSeries τ C} (hγ : ∀ s, constantCoeff (γ s) = 0)
    (F : MvPowerSeries (Fin 2 × κ) C) :
    subst γ (killCompl (fstEmb κ) F) = subst (fun p : Fin 2 × κ => if p.1 = 0 then γ p.2 else 0) F := by
  have h0 : ∀ p : Fin 2 × κ, constantCoeff (if p.1 = 0 then γ p.2 else 0) = 0 := by
    intro p
    split_ifs
    · exact hγ _
    · exact map_zero _
  have hS := hasSubst_of_constantCoeff_zero h0
  have hv : Van {p : Fin 2 × κ | p.1 ≠ 0} (F - rename (fstEmb κ) (killCompl (fstEmb κ) F)) := by
    intro ν hν
    have : ν ∈ Set.range (Finsupp.embDomain (fstEmb κ)) := by
      rw [Finsupp.mem_range_embDomain_iff]
      intro w hw
      have h1 : w.1 = 0 := by simpa using hν w hw
      exact ⟨w.2, Prod.ext h1.symm rfl⟩
    obtain ⟨μ, rfl⟩ := this
    rw [map_sub, coeff_embDomain_rename, coeff_killCompl, sub_self]
  have hz := subst_eq_zero_of_van h0 (fun s (hs : s.1 ≠ 0) => if_neg hs) hv
  rw [subst_sub hS, sub_eq_zero] at hz
  rw [hz, rename_eq_subst, subst_comp_subst_apply (HasSubst.X_comp _) hS]
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [subst_X hS]
  exact (if_pos rfl).symm

theorem sg_eq (X : RawChart C d I κ) (v : κ → C) :
    X.sg v = -∑ i, v i • killCompl (fstEmb κ) (pderiv C ((1 : Fin 2), i) X.h) := by
  ext μ
  rw [map_neg, map_sum]
  show -∑ i, v i * coeff
    (μ.mapDomain (fun x : κ => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), i) 1) X.h = _
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_smul, coeff_killCompl, coeff_pderiv, Finsupp.embDomain_notin_range, Finsupp.embDomain_eq_mapDomain]
  · rw [Nat.cast_zero, zero_add, mul_one]
    rfl
  · rintro ⟨x, hx⟩
    have : (0 : Fin 2) = 1 := (Prod.ext_iff.1 hx).1
    exact absurd this (by decide)

theorem subst_sg (X : RawChart C d I κ) (v : κ → C) {τ : Type} {γ : κ → MvPowerSeries τ C}
    (hγ : ∀ s, constantCoeff (γ s) = 0) :
    subst γ (X.sg v) = -∑ i, v i •
      subst (fun p : Fin 2 × κ => if p.1 = 0 then γ p.2 else 0) (pderiv C ((1 : Fin 2), i) X.h) := by
  have hS := hasSubst_of_constantCoeff_zero hγ
  rw [sg_eq, FormalCalc.subst_neg' hS, FormalCalc.subst_sum' hS]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [subst_smul hS, subst_killCompl hγ]

theorem pair_const {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (hb : ∀ s, constantCoeff (b s) = 0) (p : Fin 2 × κ) :
    constantCoeff (if p.1 = 0 then a p.2 else b p.2) = 0 := by
  split_ifs
  · exact ha _
  · exact hb _

theorem gp_const {n : ℕ} (j : Fin n) (x : κ) : constantCoeff (gp C κ j x) = 0 := constantCoeff_X _

theorem subst_pderiv_hAt (X : RawChart C d I κ) {τ : Type} {A : κ → MvPowerSeries (Fin 3 × κ) C}
    (hA : ∀ s, constantCoeff (A s) = 0) (i : κ) (hA' : ∀ x, pderiv C ((2 : Fin 3), i) (A x) = 0)
    {a : Fin 3 × κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) (ha2 : ∀ x, a (2, x) = 0) :
    subst a (pderiv C ((2 : Fin 3), i) (hAt X A (gp C κ 2))) =
      subst (fun p : Fin 2 × κ => if p.1 = 0 then subst a (A p.2) else 0) (pderiv C ((1 : Fin 2), i) X.h) := by
  have hS := hasSubst_of_constantCoeff_zero ha
  have hP := hasSubst_of_constantCoeff_zero (pair_const hA (gp_const (C := C) (κ := κ) (2 : Fin 3)))
  unfold hAt
  rw [FormalCalc.pderiv_subst hP, Finset.sum_eq_single ((1 : Fin 2), i)]
  · have : pderiv C ((2 : Fin 3), i) (if ((1 : Fin 2), i).1 = 0 then A ((1 : Fin 2), i).2
        else gp C κ (2 : Fin 3) ((1 : Fin 2), i).2) = 1 := by
      rw [if_neg (by simp)]
      exact pderiv_X_self
    rw [this, mul_one, subst_comp_subst_apply hP hS]
    congr 1
    funext p
    split_ifs
    · rfl
    · unfold gp
      rw [subst_X hS, ha2]
  · rintro ⟨g, x⟩ _ hb
    split_ifs with hg
    · rw [hA', mul_zero]
    · have hg1 : g = 1 := by
        have : g ≠ 0 := hg
        omega
      subst hg1
      unfold gp
      rw [pderiv_X_of_ne, mul_zero]
      intro h
      apply hb
      have := (Prod.ext_iff.1 h).2
      simp only at this
      rw [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem pderiv_subst_eq_zero {σ τ : Type} [Fintype σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {t : τ} (h : ∀ s, pderiv C t (a s) = 0) (f : MvPowerSeries σ C) :
    pderiv C t (subst a f) = 0 := by
  rw [FormalCalc.pderiv_subst (hasSubst_of_constantCoeff_zero ha)]
  simp [h]

theorem lg_const {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) (i : κ) : constantCoeff (X.lg i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, h.lin i 0 (by simp), coeff_zero_eq_constantCoeff_apply,
    constantCoeff_X]

theorem sum_const {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (x : κ) :
    constantCoeff (subst a (X.lg x) + subst b (X.lg x)) = 0 := by
  rw [map_add, constantCoeff_subst_zero ha (lg_const h x), constantCoeff_subst_zero hb (lg_const h x), add_zero]

theorem formalAdd_const {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (x : κ) :
    constantCoeff (addP X a b x) = 0 :=
  constantCoeff_subst_zero (sum_const h ha hb) (h.exc x)

theorem subst_addP {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {τ ρ : Type} [Finite τ]
    {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    {c : τ → MvPowerSeries ρ C} (hc : ∀ s, constantCoeff (c s) = 0) (x : κ) :
    subst c (addP X a b x) = addP X (fun y => subst c (a y)) (fun y => subst c (b y)) x := by
  have hS := hasSubst_of_constantCoeff_zero hc
  unfold addP
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (sum_const h ha hb)) hS]
  congr 1
  funext y
  rw [subst_add hS, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) hS,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hb) hS]

theorem lg_addP {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (i : κ) :
    subst (addP X a b) (X.lg i) = subst a (X.lg i) + subst b (X.lg i) := by
  have hS := hasSubst_of_constantCoeff_zero (sum_const h ha hb)
  have := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h.exc) hS (X.lg i)
  rw [h.lgex, subst_X hS] at this
  exact this.symm

theorem intS_addP {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    (hai : ∀ s, IntS V (a s)) (hbi : ∀ s, IntS V (b s)) (x : κ) : IntS V (addP X a b x) := by
  have hc := pair_const ha hb
  have hS := hasSubst_of_constantCoeff_zero hc
  have h1 := intS_subst hc (fun p => by split_ifs; exacts [hai _, hbi _]) (h.addInt x)
  rw [subst_addP h (gp_const 0) (gp_const 1) hc] at h1
  simpa [gp, subst_X hS] using h1

theorem intS_cocycle {X : RawChart C d I κ} {V : VF C} (h : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    (hai : ∀ s, IntS V (a s)) (hbi : ∀ s, IntS V (b s)) {v : κ → C} (hv : ∀ i, V.Ge 0 (v i)) :
    IntS V (subst (addP X a b) (X.sg v) - subst a (X.sg v) - subst b (X.sg v)) := by
  let c : Fin 3 × κ → MvPowerSeries τ C := fun p => if p.1 = 0 then a p.2 else if p.1 = 1 then b p.2 else 0
  have hc : ∀ p, constantCoeff (c p) = 0 := fun p => by
    simp only [c]
    split_ifs
    exacts [ha _, hb _, map_zero _]
  have hci : ∀ p, IntS V (c p) := fun p => by
    simp only [c]
    split_ifs
    exacts [hai _, hbi _, fun μ => by rw [map_zero]; exact VF.Ge.zero 0]
  have hc2 : ∀ x, c (2, x) = 0 := fun x => by simp [c]
  have hS := hasSubst_of_constantCoeff_zero hc
  have s0 : ∀ x, subst c (gp C κ (0 : Fin 3) x) = a x := fun x => by simp [gp, subst_X hS, c]
  have s1 : ∀ x, subst c (gp C κ (1 : Fin 3) x) = b x := fun x => by simp [gp, subst_X hS, c]
  have sA : ∀ x, subst c (addP X (gp C κ (0 : Fin 3)) (gp C κ 1) x) = addP X a b x := fun x => by
    rw [subst_addP h (gp_const 0) (gp_const 1) hc]
    simp only [s0, s1]
  have hvan : ∀ A : κ → MvPowerSeries (Fin 3 × κ) C, (∀ s, constantCoeff (A s) = 0) →
      Van {p : Fin 3 × κ | p.1 = 2} (hAt X A (gp C κ 2)) := by
    intro A hA
    refine Van.subst {s : Fin 2 × κ | s.1 = 1} (pair_const hA (gp_const 2)) ?_ (h.axes 1)
    rintro ⟨g, x⟩ (hg : g = 1)
    subst hg
    rw [if_neg (by simp)]
    intro ν hν
    unfold gp
    rw [coeff_X, if_neg]
    intro e
    exact hν (2, x) (by rw [e]; simp) rfl
  have hAc := formalAdd_const h (gp_const (C := C) (κ := κ) (0 : Fin 3)) (gp_const 1)
  have hH : Van {p : Fin 3 × κ | p.1 = 2} (hAt X (gp C κ (0 : Fin 3)) (gp C κ 2) + hAt X (gp C κ 1) (gp C κ 2) -
      hAt X (addP X (gp C κ 0) (gp C κ 1)) (gp C κ 2)) := by
    intro ν hν
    rw [map_sub, map_add, hvan _ (gp_const 0) ν hν, hvan _ (gp_const 1) ν hν, hvan _ hAc ν hν]
    simp
  have key : ∀ i, IntS V
      (subst (fun p : Fin 2 × κ => if p.1 = 0 then a p.2 else 0) (pderiv C ((1 : Fin 2), i) X.h) +
        subst (fun p : Fin 2 × κ => if p.1 = 0 then b p.2 else 0) (pderiv C ((1 : Fin 2), i) X.h) -
        subst (fun p : Fin 2 × κ => if p.1 = 0 then addP X a b p.2 else 0) (pderiv C ((1 : Fin 2), i) X.h)) := by
    intro i
    have d0 : ∀ x, pderiv C ((2 : Fin 3), i) (gp C κ (0 : Fin 3) x) = 0 := fun x =>
      pderiv_X_of_ne (by simp)
    have d1 : ∀ x, pderiv C ((2 : Fin 3), i) (gp C κ (1 : Fin 3) x) = 0 := fun x =>
      pderiv_X_of_ne (by simp)
    have dA : ∀ x, pderiv C ((2 : Fin 3), i) (addP X (gp C κ (0 : Fin 3)) (gp C κ 1) x) = 0 := fun x =>
      pderiv_subst_eq_zero (sum_const h (gp_const 0) (gp_const 1)) (fun y => by
        rw [map_add, pderiv_subst_eq_zero (gp_const 0) d0, pderiv_subst_eq_zero (gp_const 1) d1, add_zero]) _
    have h1 := intS_subst hc hci (intS_pderiv h.ph1 ((2 : Fin 3), i))
    have h2 := subst_eq_zero_of_van hc (fun s (hs : s.1 = 2) => by
      rw [show s = (2, s.2) from Prod.ext hs rfl]; exact hc2 _) (van_pderiv_mvExp hH ((2 : Fin 3), i))
    rw [subst_sub hS, sub_eq_zero] at h2
    rw [h2, map_sub, map_add, subst_sub hS, subst_add hS, subst_pderiv_hAt X (gp_const 0) i d0 hc hc2,
      subst_pderiv_hAt X (gp_const 1) i d1 hc hc2, subst_pderiv_hAt X hAc i dA hc hc2] at h1
    simpa only [s0, s1, sA] using h1
  rw [subst_sg X v (formalAdd_const h ha hb), subst_sg X v ha, subst_sg X v hb]
  intro μ
  have := VF.Ge.sum (s := Finset.univ) fun i _ => (hv i).mul_int (key i μ)
  convert this using 1
  simp only [map_sub, map_add, map_neg, map_sum, coeff_smul, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  ring

theorem intS_iff {V : VF C} {f : PowerSeries C} :
    IntS V (σ := Unit) f ↔ ∀ n, V.Ge 0 (PowerSeries.coeff n f) := by
  constructor
  · intro h n
    exact h (Finsupp.single () n)
  · intro h μ
    rw [Finsupp.unique_single μ]
    exact h _

end GlobalTheory.RowLaw.AddCurve

namespace GlobalTheory.RowLaw

open AddCurve

theorem addCvSt_of_rlaw (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)]
    (κ : Type) [Fintype κ] (X : RawChart C d I κ) (h : RLaw X V) : X.AddCvSt V := by
  intro γ γ' hγ hγ'
  have ha : ∀ s, constantCoeff (σ := Unit) (γ s) = 0 := fun s => (hγ s).1
  have hb : ∀ s, constantCoeff (σ := Unit) (γ' s) = 0 := fun s => (hγ' s).1
  have hai : ∀ s, IntS V (σ := Unit) (γ s) := fun s => intS_iff.2 (hγ s).2
  have hbi : ∀ s, IntS V (σ := Unit) (γ' s) := fun s => intS_iff.2 (hγ' s).2
  refine ⟨addP X (τ := Unit) γ γ', fun i => ⟨formalAdd_const h ha hb i, intS_iff.1 (intS_addP h ha hb hai hbi i)⟩,
    fun i => lg_addP h ha hb i, fun v hv => ⟨?_, intS_iff.1 (intS_cocycle h ha hb hai hbi hv)⟩⟩
  have h0 := X.constantCoeff_sg (h.axes 0) v
  show constantCoeff (σ := Unit) (subst (addP X (τ := Unit) γ γ') (X.sg v) - subst γ (X.sg v) - subst γ' (X.sg v)) = 0
  rw [map_sub, map_sub, constantCoeff_subst_zero (formalAdd_const h ha hb) h0, constantCoeff_subst_zero ha h0,
    constantCoeff_subst_zero hb h0]
  simp

end GlobalTheory.RowLaw
