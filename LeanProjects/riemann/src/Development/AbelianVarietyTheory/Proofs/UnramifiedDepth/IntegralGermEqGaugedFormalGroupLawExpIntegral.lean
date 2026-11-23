import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder

noncomputable section

open scoped BigOperators
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.FormalInv MvPowerSeries

namespace GlobalTheory.RowLaw.GermRing

variable {C : Type} [Field C]

def intRing (V : VF C) : Subring C where
  carrier := {a | V.Ge 0 a}
  mul_mem' ha hb := VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' ha hb := VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' ha := VF.Ge.neg ha

theorem intS_subst {V : VF C} {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (h0 : ∀ s, constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C} (hf : IntS V f) :
    IntS V (subst a f) := fun μ =>
  mem_coeffsInDeg.1 (subst_mem_coeffsInDeg (S := intRing V) (g := μ.degree + 1) h0
    (fun s => mem_coeffsInDeg.2 fun d _ => ha s d) (mem_coeffsInDeg.2 fun d _ => hf d)) μ (Nat.lt_succ_self _)

theorem intS_X {V : VF C} {σ : Type} (s : σ) : IntS V (X s : MvPowerSeries σ C) := fun μ => by
  rw [coeff_X]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem intS_sum_smul {V : VF C} {σ ι : Type} [Fintype ι] {w : ι → C} (hw : ∀ i, V.Ge 0 (w i))
    {f : ι → MvPowerSeries σ C} (hf : ∀ i, IntS V (f i)) : IntS V (∑ i, w i • f i) := fun μ => by
  rw [map_sum]
  exact VF.Ge.sum fun i _ => by rw [map_smul, smul_eq_mul]; exact (hw i).mul_int (hf i μ)

theorem subst_sum_smul {σ τ ι : Type} {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (s : Finset ι) (w : ι → C)
    (f : ι → MvPowerSeries σ C) : subst a (∑ i ∈ s, w i • f i) = ∑ i ∈ s, w i • subst a (f i) := by
  rw [← coe_substAlgHom ha, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul _ _ _

theorem subst_sum {σ τ ι : Type} {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (s : Finset ι)
    (f : ι → MvPowerSeries σ C) : subst a (∑ i ∈ s, f i) = ∑ i ∈ s, subst a (f i) := by
  rw [← coe_substAlgHom ha, map_sum]

theorem coeff_pow_eq_zero {τ : Type} {t : MvPowerSeries τ C} (ht : constantCoeff t = 0) {μ : τ →₀ ℕ} {n : ℕ}
    (hn : μ.degree < n) : coeff μ (t ^ n) = 0 :=
  coeff_eq_zero_of_constantCoeff_nilpotent (m := 1) (by simpa using ht) (by omega)

theorem coeff_subst_tyS {τ : Type} {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) {t : MvPowerSeries τ C}
    (ht : constantCoeff t = 0) (μ : τ →₀ ℕ) :
    coeff μ (PowerSeries.subst t (tyS l a)) = ∑ s ∈ Finset.range (μ.degree + 1), a s * coeff μ (t ^ (l ^ s)) := by
  have hs : PowerSeries.HasSubst t := PowerSeries.HasSubst.of_constantCoeff_zero ht
  rw [PowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset (s := Finset.range (μ.degree + 1))]
  · have h1 : ∀ n ∈ Finset.range (μ.degree + 1), PowerSeries.coeff n (tyS l a) • coeff μ (t ^ n) =
        ∑ s ∈ Finset.range (μ.degree + 1), if l ^ s = n then a s * coeff μ (t ^ (l ^ s)) else 0 := by
      intro n hn
      by_cases h : ∃ s, l ^ s = n
      · obtain ⟨s, rfl⟩ := h
        rw [coeff_tyS_pow hl, Finset.sum_eq_single s]
        · simp
        · intro s' _ hs'
          rw [if_neg fun e => hs' (Nat.pow_right_injective hl e)]
        · intro hs'
          exfalso
          apply hs'
          have := Nat.lt_pow_self (n := s) (show 1 < l by omega)
          rw [Finset.mem_range] at hn ⊢
          omega
      · push Not at h
        rw [coeff_tyS_of_ne a n h, zero_smul]
        exact (Finset.sum_eq_zero fun s _ => if_neg (h s)).symm
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · rw [coeff_pow_eq_zero ht (by rw [Finset.mem_range] at h; omega), mul_zero]
  · intro n hn
    by_contra h
    apply hn
    have : μ.degree < n := by simpa using h
    simp only [coeff_pow_eq_zero ht this, smul_zero]

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ} {V : VF C}

theorem lg_const (hY : RLaw Y V) (i : κ) : constantCoeff (Y.lg i) = 0 := by
  have := hY.lin i 0 (by simp)
  simpa using this

theorem linearPart_lg (hY : RLaw Y V) : linearPart Y.lg = 1 := by
  rw [← linearPart_X (σ := κ) (R := C)]
  ext i j
  exact hY.lin i _ (by simp)

theorem lg_ex (hY : RLaw Y V) {τ : Type} {z : κ → MvPowerSeries τ C} (hz : ∀ i, constantCoeff (z i) = 0) (i : κ) :
    subst (fun x => subst z (Y.ex x)) (Y.lg i) = z i := by
  have hz' := hasSubst_of_constantCoeff_zero hz
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hY.exc) hz', hY.lgex, subst_X hz']

theorem ex_lg (hY : RLaw Y V) {τ : Type} {a : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (i : κ) :
    subst (fun x => subst a (Y.lg x)) (Y.ex i) = a i := by
  have ha' := hasSubst_of_constantCoeff_zero ha
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (lg_const hY)) ha', hY.exlg, subst_X ha']

theorem log_add_const (hY : RLaw Y V) {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (x : κ) : constantCoeff (subst a (Y.lg x) + subst b (Y.lg x)) = 0 := by
  rw [map_add, constantCoeff_subst_zero ha (lg_const hY x), constantCoeff_subst_zero hb (lg_const hY x), add_zero]

theorem intS_addP (hY : RLaw Y V) {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (ia : ∀ i, IntS V (a i)) (ib : ∀ i, IntS V (b i)) (i : κ) :
    IntS V (addP Y a b i) := by
  set ab : Fin 2 × κ → MvPowerSeries τ C := fun p => if p.1 = 0 then a p.2 else b p.2 with hab
  have h0 : ∀ p, constantCoeff (ab p) = 0 := fun p => by
    simp only [hab]; split_ifs; exacts [ha _, hb _]
  have hi : ∀ p, IntS V (ab p) := fun p => by
    simp only [hab]; split_ifs; exacts [ia _, ib _]
  have hs := hasSubst_of_constantCoeff_zero h0
  have hg : ∀ (j : Fin 2) x, constantCoeff (gp C κ j x) = 0 := fun j x => constantCoeff_X _
  have key : addP Y a b i = subst ab (addP Y (gp C κ (0 : Fin 2)) (gp C κ 1) i) := by
    unfold addP
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (log_add_const hY (hg 0) (hg 1))) hs]
    congr 1
    funext x
    rw [subst_add hs, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (hg 0)) hs,
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (hg 1)) hs]
    have e0 : (fun s => subst ab (gp C κ (0 : Fin 2) s)) = a := funext fun s => by
      rw [gp, subst_X hs]; simp [hab]
    have e1 : (fun s => subst ab (gp C κ (1 : Fin 2) s)) = b := funext fun s => by
      rw [gp, subst_X hs]; simp [hab]
    rw [e0, e1]
  rw [key]
  exact intS_subst h0 hi (hY.addInt i)

theorem exists_sum_point (hY : RLaw Y V) {τ ι : Type} (s : Finset ι) (a : ι → κ → MvPowerSeries τ C)
    (ha : ∀ c i, constantCoeff (a c i) = 0) (ia : ∀ c i, IntS V (a c i)) :
    ∃ Φ : κ → MvPowerSeries τ C, (∀ i, constantCoeff (Φ i) = 0) ∧ (∀ i, IntS V (Φ i)) ∧
      ∀ i, subst Φ (Y.lg i) = ∑ c ∈ s, subst (a c) (Y.lg i) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, fun _ => map_zero _, fun _ μ => by simpa using VF.Ge.zero (V := V) 0, fun i => ?_⟩
    rw [Finset.sum_empty]
    exact subst_zero_of_constantCoeff_zero (lg_const hY i)
  | insert c s hc ih =>
    obtain ⟨Φ, h0, hi, hl⟩ := ih
    refine ⟨addP Y (a c) Φ, fun i => constantCoeff_subst_zero (log_add_const hY (ha c) h0) (hY.exc i),
      intS_addP hY (ha c) h0 (ia c) hi, fun i => ?_⟩
    rw [Finset.sum_insert hc, ← hl]
    exact lg_ex hY (log_add_const hY (ha c) h0) i

theorem inv_int {σ : Type} [Fintype σ] (A : Matrix σ σ C) (hA : ∀ i j, V.Ge 0 (A i j)) (hd : V.v A.det = 0) :
    IsUnit A ∧ ∀ i j, V.Ge 0 (A⁻¹ i j) := by
  have hne : A.det ≠ 0 := fun h => by
    rw [h, V.v.map_zero] at hd
    exact WithTop.top_ne_zero hd
  refine ⟨(Matrix.isUnit_iff_isUnit_det A).2 hne.isUnit, fun i j => ?_⟩
  have hinv : V.Ge 0 (A.det)⁻¹ := by
    have h := V.v.map_mul A.det (A.det)⁻¹
    rw [mul_inv_cancel₀ hne, V.v.map_one, hd, zero_add] at h
    unfold VF.Ge
    rw [← h]
    simp
  let B : Matrix σ σ (intRing V) := Matrix.of fun i j => ⟨A i j, hA i j⟩
  have hB : A = (intRing V).subtype.mapMatrix B := by ext; rfl
  have hadj : V.Ge 0 (A.adjugate i j) := by
    rw [hB, ← RingHom.map_adjugate]
    exact (B.adjugate i j).2
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact hinv.mul_int hadj

theorem one_group (hY : RLaw Y V) (g : Fin 2) (H : Y.CartHyp V g) (S : Sys (RawChart.cart H))
    (t : I g → MvPowerSeries (I g) C) (ht : S.IsT t) (E : κ → MvPowerSeries (I g) C)
    (hE : ∀ x, E x = subst (fun i : κ => ∑ c : I g, Y.u g c i • (X c : MvPowerSeries (I g) C)) (Y.ex x)) :
    (∃ Φ : κ → MvPowerSeries (I g) C, (∀ x, constantCoeff (Φ x) = 0) ∧ (∀ x, IntS V (Φ x)) ∧
      ∀ x, E x = subst t (Φ x)) ∧
    ∃ Ψ : I g → MvPowerSeries κ C, (∀ c, constantCoeff (Ψ c) = 0) ∧ (∀ c, IntS V (Ψ c)) ∧
      ∀ c, t c = subst E (Ψ c) := by
  have hl : 2 ≤ V.l := V.l_prime.two_le
  have hts := hasSubst_of_constantCoeff_zero ht.1
  have hc : ∀ c, S.cur c ∈ Y.TySet V g := fun c => (S.curve c).1
  choose γ lam hγ _ hlog _ using hc
  have hX : ∀ c : I g, PowerSeries.HasSubst (X c : MvPowerSeries (I g) C) := fun c =>
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X c)
  have hX0 : ∀ c : I g, ∀ _ : Unit, constantCoeff (X c : MvPowerSeries (I g) C) = 0 := fun c _ => constantCoeff_X c
  obtain ⟨Φ, h0, hi, hΦ⟩ := exists_sum_point hY Finset.univ
    (fun (c : I g) i => PowerSeries.subst (X c : MvPowerSeries (I g) C) (γ c i))
    (fun c i => constantCoeff_subst_zero (hX0 c) (hγ c i).1)
    (fun c i => intS_subst (hX0 c) (fun _ => intS_X c) fun μ => by
      have := (hγ c i).2 (μ ())
      rwa [PowerSeries.coeff_def rfl] at this)
  have hΦs := hasSubst_of_constantCoeff_zero h0
  have hΦ' : ∀ i, subst Φ (Y.lg i) = ∑ x : I g, Y.u g x i •
      ∑ c : I g, PowerSeries.subst (X c : MvPowerSeries (I g) C) (tyS V.l fun s => S.al c s x) := by
    intro i
    rw [hΦ]
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun j => (hγ c j).1) (hX c).const (Y.lg i)
    have e2 := hlog c i
    unfold alongCv at e2
    unfold PowerSeries.subst
    rw [← e, e2]
    exact subst_sum_smul (hX c).const _ _ _
  have hT : ∀ x, subst t (∑ c : I g, PowerSeries.subst (X c : MvPowerSeries (I g) C) (tyS V.l fun s => S.al c s x)) =
      (X x : MvPowerSeries (I g) C) := by
    intro x
    rw [subst_sum hts]
    ext μ
    rw [map_sum, coeff_X, ← ht.2 x μ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← coeff_subst_tyS hl _ (ht.1 c)]
    unfold PowerSeries.subst
    rw [subst_comp_subst_apply (hX c).const hts, subst_X hts]
  have hEΦ : ∀ x, E x = subst t (Φ x) := by
    intro x
    rw [hE, ← ex_lg hY (fun i => constantCoeff_subst_zero ht.1 (h0 i)) x]
    congr 1
    funext i
    rw [← subst_comp_subst_apply hΦs hts, hΦ', subst_sum_smul hts]
    simp only [hT]
  refine ⟨⟨Φ, h0, hi, hEΦ⟩, ?_⟩
  obtain ⟨w, hw, hsat⟩ := hY.sat g
  have hlin : ∀ i j, linearPart Φ i j = ∑ x : I g, Y.u g x i * S.tan j x := by
    intro i j
    have e := linearPart_subst (lg_const hY) h0
    rw [linearPart_lg hY, Matrix.one_mul] at e
    rw [← e]
    show coeff (Finsupp.single j 1) (subst Φ (Y.lg i)) = _
    rw [hΦ', map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, smul_eq_mul, map_sum, Finset.sum_eq_single j]
    · rw [coeff_subst_tyS hl _ (constantCoeff_X j)]
      have h1 : S.al j 0 x = S.tan j x := by
        unfold Sys.al
        rw [(S.curve j).2.1]; rfl
      have h2 : ¬ (1 = V.l) := by omega
      have h3 : coeff (Finsupp.single j 1) ((X j : MvPowerSeries (I g) C) ^ V.l) = 0 := by
        rw [coeff_X_pow, if_neg]
        intro e'
        have := DFunLike.congr_fun e' j
        simp only [Finsupp.single_eq_same] at this
        exact h2 this
      rw [Finsupp.degree_single, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, pow_one, h3, h1,
        coeff_index_single_self_X, mul_one, mul_zero, add_zero]
    · intro c _ hcj
      rw [coeff_subst_tyS hl _ (constantCoeff_X c)]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [coeff_X_pow, if_neg, mul_zero]
      intro e'
      have := DFunLike.congr_fun e' j
      simp [hcj] at this
    · simp
  set Θ : I g → MvPowerSeries (I g) C := fun c => ∑ x, w x c • Φ x with hΘ
  have hΘ0 : ∀ c, constantCoeff (Θ c) = 0 := fun c => by
    simp [hΘ, map_sum, h0]
  have hΘi : ∀ c, IntS V (Θ c) := fun c => intS_sum_smul (fun x => hw x c) hi
  have hΘl : linearPart Θ = (Matrix.of S.tan).transpose := by
    ext c j
    show coeff (Finsupp.single j 1) (∑ x, w x c • Φ x) = S.tan j c
    rw [map_sum]
    have e : ∀ i, coeff (Finsupp.single j 1) (w i c • Φ i) = ∑ x : I g, (Y.u g x i * w i c) * S.tan j x := by
      intro i
      rw [map_smul, smul_eq_mul, show coeff (Finsupp.single j 1) (Φ i) = _ from hlin i j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    simp only [e]
    rw [Finset.sum_comm, Finset.sum_eq_single c]
    · rw [← Finset.sum_mul, (hsat c c).1 rfl, one_mul]
    · intro x _ hx
      rw [← Finset.sum_mul, (hsat x c).2 hx, zero_mul]
    · simp
  obtain ⟨hU, hinv⟩ := inv_int (V := V) (linearPart Θ) (fun i j => hΘi i _)
    (by rw [hΘl, Matrix.det_transpose]; exact S.unimod)
  have hE0 : ∀ x, constantCoeff (E x) = 0 := fun x => by
    rw [hEΦ]; exact constantCoeff_subst_zero ht.1 (h0 x)
  have hEs := hasSubst_of_constantCoeff_zero hE0
  have hW0 : ∀ c, constantCoeff (∑ x, w x c • (X x : MvPowerSeries κ C)) = 0 := fun c => by
    simp [map_sum]
  refine ⟨fun c => subst (fun c' => ∑ x, w x c' • (X x : MvPowerSeries κ C)) (substInv Θ c),
    fun c => constantCoeff_subst_zero hW0 (constantCoeff_substInv hΘ0 c),
    fun c => intS_subst hW0 (fun c' => intS_sum_smul (fun x => hw x c') intS_X) fun μ =>
      coeff_substInv_mem (S := intRing V) (g := μ.degree + 1) hΘ0 hinv (fun i d _ => hΘi i d) c μ
        (Nat.lt_succ_self _), fun c => ?_⟩
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hW0) hEs]
  have e : (fun c' => subst E (∑ x, w x c' • (X x : MvPowerSeries κ C))) = fun c' => subst t (Θ c') := by
    funext c'
    rw [subst_sum_smul hEs, subst_sum_smul hts]
    exact Finset.sum_congr rfl fun x _ => by rw [subst_X hEs, hEΦ]
  rw [e, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hΘ0) hts, subst_substInv_left hΘ0 hU, subst_X hts]

theorem upG_subst (g : Fin 2) {σ : Type} [Finite σ] {a : σ → MvPowerSeries (I g) C}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ C) :
    upG g (subst a f) = subst (fun s => upG g (a s)) f :=
  subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha)
    (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) f

theorem upG_const (g : Fin 2) {f : MvPowerSeries (I g) C} (hf : constantCoeff f = 0) :
    constantCoeff (upG g f) = 0 :=
  constantCoeff_subst_zero (fun _ => constantCoeff_X _) hf

end GlobalTheory.RowLaw.GermRing

namespace GlobalTheory.RowLaw

open GermRing

theorem intGerm_eq_expInt : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type)
    [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V →
    ∀ (H : ∀ g, X.CartHyp V g) (S : ∀ g, Sys (RawChart.cart (H g))) (t : ∀ g, I g → MvPowerSeries (I g) C),
    (∀ g, (S g).IsT (t g)) → IntGerm V t = ExpInt X V := by
  intro C _ V d _ I _ κ _ Y hY H S t ht
  let E : ∀ g, κ → MvPowerSeries (I g) C := fun g x =>
    subst (fun i : κ => ∑ c : I g, Y.u g c i • (X c : MvPowerSeries (I g) C)) (Y.ex x)
  have hL : ∀ g (i : κ), constantCoeff (∑ c : I g, Y.u g c i • (X c : MvPowerSeries (I g) C)) = 0 := fun g i => by
    simp [map_sum]
  have hE0 : ∀ g x, constantCoeff (E g x) = 0 := fun g x => constantCoeff_subst_zero (hL g) (hY.exc x)
  have hexp : ∀ g x, Y.expPt g x = upG g (E g x) := by
    intro g x
    rw [upG_subst g (hL g)]
    unfold RawChart.expPt
    congr 1
    funext i
    have hs : HasSubst (fun x : I g => (X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    unfold upG
    rw [subst_sum_smul hs]
    simp only [subst_X hs]
  have key := fun g => one_group hY g (H g) (S g) (t g) (ht g) (E g) fun _ => rfl
  choose Φ hΦ0 hΦi hΦ using fun g => (key g).1
  choose Ψ hΨ0 hΨi hΨ using fun g => (key g).2
  have hts : HasSubst (fun w : WV I => upG w.1 (t w.1 w.2)) :=
    hasSubst_of_constantCoeff_zero fun w => upG_const _ ((ht w.1).1 _)
  have hes : HasSubst (fun p : Fin 2 × κ => Y.expPt p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => by rw [hexp]; exact upG_const _ (hE0 _ _)
  ext F
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    have hx : ∀ (g : Fin 2) (x : κ), constantCoeff (X (g, x) : MvPowerSeries (Fin 2 × κ) C) = 0 :=
      fun _ _ => constantCoeff_X _
    have h0 : ∀ w : WV I, constantCoeff (subst (fun x : κ => (X (w.1, x) : MvPowerSeries (Fin 2 × κ) C))
        (Ψ w.1 w.2)) = 0 := fun w => constantCoeff_subst_zero (hx _) (hΨ0 _ _)
    refine ⟨_, intS_subst h0 (fun w => intS_subst (hx _) (fun _ => intS_X _) (hΨi _ _)) hγ, ?_⟩
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) hes]
    congr 1
    funext w
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (hx _)) hes, hΨ, upG_subst _ (hE0 _)]
    congr 1
    funext x
    rw [subst_X hes, hexp]
  · rintro ⟨f, hf, rfl⟩
    have h0 : ∀ p : Fin 2 × κ, constantCoeff (upG p.1 (Φ p.1 p.2)) = 0 := fun p => upG_const _ (hΦ0 _ _)
    refine ⟨_, intS_subst h0
      (fun p => intS_subst (fun _ => constantCoeff_X _) (fun _ => intS_X _) (hΦi _ _)) hf, ?_⟩
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) hts]
    congr 1
    funext p
    rw [hexp, hΦ, upG_subst _ (ht _).1]
    conv_rhs => unfold upG
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
    · congr 1
      funext c
      exact (subst_X hts (⟨p.1, c⟩ : WV I)).symm
    · exact hts

end GlobalTheory.RowLaw
