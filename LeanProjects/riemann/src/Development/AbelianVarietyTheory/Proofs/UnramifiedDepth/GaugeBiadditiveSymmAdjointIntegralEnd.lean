import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import Formalism.LocalToGlobal.CharacterGerms.RowTieAxes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne

noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowVal.EndCalc

open MvPowerSeries

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  {X : RawChart C d I κ}

theorem comp_cc {σ τ υ : Type} [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ C} {b : τ → MvPowerSeries υ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (f : MvPowerSeries σ C) :
    subst b (subst a f) = subst (fun s => subst b (a s)) f :=
  subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) (hasSubst_of_constantCoeff_zero hb) f

theorem subst_lin {σ τ ι : Type} [Finite σ] [Fintype ι] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (c : ι → C) (f : ι → MvPowerSeries σ C) :
    subst a (∑ y, c y • f y) = ∑ y, c y • subst a (f y) := by
  have hs := hasSubst_of_constantCoeff_zero ha
  rw [← substAlgHom_apply hs, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [substAlgHom_apply, subst_smul hs]

theorem lg_cc (H : RLaw X V) (i : κ) : constantCoeff (X.lg i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, H.lin i 0 (by simp), coeff_zero_eq_constantCoeff_apply, constantCoeff_X]

theorem lin_cc (H : RLaw X V) {τ : Type} {a : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (A : Matrix κ κ C) (x : κ) : constantCoeff (∑ y, A x y • subst a (X.lg y)) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [constantCoeff_smul, cc_subst ha, lg_cc H, smul_zero]

theorem add_cc (H : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (hb : ∀ s, constantCoeff (b s) = 0) (x : κ) :
    constantCoeff (subst a (X.lg x) + subst b (X.lg x)) = 0 := by
  rw [map_add, cc_subst ha, cc_subst hb, lg_cc H, add_zero]

theorem constantCoeff_expMulLog (H : RLaw X V) {τ : Type} {a : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (A : Matrix κ κ C) (i : κ) : constantCoeff (endP X A a i) = 0 := by
  unfold endP
  rw [cc_subst (lin_cc H ha A), H.exc]

theorem formalAdd_constantCoeff (H : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (hb : ∀ s, constantCoeff (b s) = 0) (i : κ) : constantCoeff (addP X a b i) = 0 := by
  unfold addP
  rw [cc_subst (add_cc H ha hb), H.exc]

theorem pair_cc {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (hb : ∀ s, constantCoeff (b s) = 0) (p : Fin 2 × κ) :
    constantCoeff (if p.1 = 0 then a p.2 else b p.2) = 0 := by
  split_ifs
  · exact ha _
  · exact hb _

theorem h_cc (H : RLaw X V) : constantCoeff X.h = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact H.axes 0 0 (by simp)

theorem hAt_cc (H : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (hb : ∀ s, constantCoeff (b s) = 0) : constantCoeff (hAt X a b) = 0 := by
  unfold hAt
  rw [cc_subst (pair_cc ha hb), h_cc H]

theorem lg_ex (H : RLaw X V) {τ : Type} {z : κ → MvPowerSeries τ C} (hz : ∀ s, constantCoeff (z s) = 0) (y : κ) :
    subst (fun i => subst z (X.ex i)) (X.lg y) = z y := by
  rw [← comp_cc H.exc hz, H.lgex, subst_X (hasSubst_of_constantCoeff_zero hz)]

theorem lg_endP (H : RLaw X V) {τ : Type} {a : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (A : Matrix κ κ C) (x : κ) : subst (endP X A a) (X.lg x) = ∑ y, A x y • subst a (X.lg y) :=
  lg_ex H (lin_cc H ha A) x

theorem subst_endP (H : RLaw X V) {τ υ : Type} [Finite τ] {a : κ → MvPowerSeries τ C} {b : τ → MvPowerSeries υ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (A : Matrix κ κ C) (i : κ) :
    subst b (endP X A a i) = endP X A (fun s => subst b (a s)) i := by
  unfold endP
  rw [comp_cc (lin_cc H ha A) hb]
  congr 1
  funext x
  rw [subst_lin hb]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [comp_cc ha hb]

theorem subst_addP (H : RLaw X V) {τ υ : Type} [Finite τ] {a a' : κ → MvPowerSeries τ C} {b : τ → MvPowerSeries υ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (ha' : ∀ s, constantCoeff (a' s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    (i : κ) :
    subst b (addP X a a' i) = addP X (fun s => subst b (a s)) (fun s => subst b (a' s)) i := by
  unfold addP
  rw [comp_cc (add_cc H ha ha') hb]
  congr 1
  funext x
  rw [subst_add (hasSubst_of_constantCoeff_zero hb), comp_cc ha hb, comp_cc ha' hb]

theorem subst_hAt {τ υ : Type} [Finite τ] {a a' : κ → MvPowerSeries τ C} {b : τ → MvPowerSeries υ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (ha' : ∀ s, constantCoeff (a' s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) :
    subst b (hAt X a a') = hAt X (fun s => subst b (a s)) (fun s => subst b (a' s)) := by
  unfold hAt
  rw [comp_cc (pair_cc ha ha') hb]
  congr 1
  funext p
  split_ifs <;> rfl

theorem expMulLog_expMulLog (H : RLaw X V) {τ : Type} {a : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (M A : Matrix κ κ C) : endP X M (endP X A a) = endP X (M * A) a := by
  funext i
  show subst (fun x => ∑ y, M x y • subst (endP X A a) (X.lg y)) (X.ex i) =
    subst (fun x => ∑ y, (M * A) x y • subst a (X.lg y)) (X.ex i)
  congr 1
  funext x
  simp only [lg_endP H ha, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem formalAdd_endP (H : RLaw X V) {τ : Type} {a : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (A B : Matrix κ κ C) : addP X (endP X A a) (endP X B a) = endP X (A + B) a := by
  funext i
  show subst (fun x => subst (endP X A a) (X.lg x) + subst (endP X B a) (X.lg x)) (X.ex i) =
    subst (fun x => ∑ y, (A + B) x y • subst a (X.lg y)) (X.ex i)
  congr 1
  funext x
  simp only [lg_endP H ha, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem subst_van {σ τ : Type} [Finite σ] (T : Set σ) {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (haT : ∀ s ∈ T, a s = 0) {f : MvPowerSeries σ C} (hf : Van T f) :
    subst a f = 0 := by
  have h : Van (∅ : Set τ) (subst a f) :=
    Van.subst T ha0 (fun s hs ν _ => by rw [haT s hs, map_zero]) hf
  ext ν
  rw [h ν (fun w _ => Set.notMem_empty w), map_zero]

theorem expMulLog_zero (H : RLaw X V) {τ : Type} (a : κ → MvPowerSeries τ C) : endP X 0 a = fun _ => 0 := by
  funext i
  refine subst_van Set.univ (fun s => by simp) (fun s _ => by simp) ?_
  intro e he
  have he0 : e = 0 := by
    rw [← Finsupp.support_eq_empty]
    exact Finset.eq_empty_of_forall_notMem fun s hs => he s hs (Set.mem_univ s)
  rw [he0, coeff_zero_eq_constantCoeff_apply]
  exact H.exc i

theorem hAt_zero_right (H : RLaw X V) {τ : Type} {a : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) :
    hAt X a (fun _ => 0) = 0 := by
  refine subst_van {s : Fin 2 × κ | s.1 = 1} (pair_cc ha (fun _ => map_zero _)) ?_ (H.axes 1)
  intro s hs
  have hs' : s.1 = 1 := hs
  simp [hs']

theorem hAt_zero_left (H : RLaw X V) {τ : Type} {a : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) :
    hAt X (fun _ => 0) a = 0 := by
  refine subst_van {s : Fin 2 × κ | s.1 = 0} (pair_cc (fun _ => map_zero _) ha) ?_ (H.axes 0)
  intro s hs
  have hs' : s.1 = 0 := hs
  simp [hs']

theorem gp_cc {n : ℕ} (j : Fin n) (s : κ) : constantCoeff (gp C κ j s) = 0 := constantCoeff_X _

theorem subst_gp {n : ℕ} {τ : Type} {P : Fin n → κ → MvPowerSeries τ C} (hP : ∀ j s, constantCoeff (P j s) = 0)
    (j : Fin n) : (fun s => subst (fun p : Fin n × κ => P p.1 p.2) (gp C κ j s)) = P j := by
  funext s
  exact subst_X (hasSubst_of_constantCoeff_zero (a := fun p : Fin n × κ => P p.1 p.2) fun p => hP p.1 p.2) (j, s)

theorem formalAdd_integral (H : RLaw X V) {τ : Type} {P : Fin 2 → κ → MvPowerSeries τ C}
    (hP : ∀ j s, constantCoeff (P j s) = 0) (hI : ∀ j s, IntS V (P j s)) (i : κ) :
    IntS V (addP X (P 0) (P 1) i) := by
  have h := intS_subst (a := fun p : Fin 2 × κ => P p.1 p.2) (fun p => hP p.1 p.2) (fun p => hI p.1 p.2) (H.addInt i)
  rwa [subst_addP H (gp_cc 0) (gp_cc 1) (fun p => hP p.1 p.2), subst_gp hP, subst_gp hP] at h

theorem expMulLog_integral (H : RLaw X V) {A : Matrix κ κ C} (hA : IntEnd X V A) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hi : ∀ s, IntS V (a s)) (i : κ) : IntS V (endP X A a i) := by
  have h := intS_subst ha hi (hA i)
  rw [subst_endP H (fun s => constantCoeff_X s) ha] at h
  simpa only [subst_X (hasSubst_of_constantCoeff_zero ha)] using h

variable [CharZero C]

theorem add_left_log (H : RLaw X V) {τ : Type} {P : Fin 3 → κ → MvPowerSeries τ C}
    (hP : ∀ j s, constantCoeff (P j s) = 0) (hI : ∀ j s, IntS V (P j s)) :
    hAt X (P 0) (P 2) + hAt X (P 1) (P 2) - hAt X (addP X (P 0) (P 1)) (P 2) ∈ logInt V τ := by
  have hb : ∀ p : Fin 3 × κ, constantCoeff (P p.1 p.2) = 0 := fun p => hP p.1 p.2
  have hs := hasSubst_of_constantCoeff_zero hb
  have hadd := formalAdd_constantCoeff H (gp_cc (C := C) (κ := κ) (0 : Fin 3)) (gp_cc 1)
  have h := logInt_subst hb (fun p => hI p.1 p.2) (mem_logInt.2 ⟨by
    rw [map_sub, map_add, hAt_cc H (gp_cc 0) (gp_cc 2), hAt_cc H (gp_cc 1) (gp_cc 2), hAt_cc H hadd (gp_cc 2)]
    simp, H.ph1⟩)
  rw [subst_sub hs, subst_add hs, subst_hAt (gp_cc 0) (gp_cc 2) hb, subst_hAt (gp_cc 1) (gp_cc 2) hb,
    subst_hAt hadd (gp_cc 2) hb] at h
  simpa only [subst_addP H (gp_cc 0) (gp_cc 1) hb, subst_gp hP] using h

theorem add_right_log (H : RLaw X V) {τ : Type} {P : Fin 3 → κ → MvPowerSeries τ C}
    (hP : ∀ j s, constantCoeff (P j s) = 0) (hI : ∀ j s, IntS V (P j s)) :
    hAt X (P 0) (P 1) + hAt X (P 0) (P 2) - hAt X (P 0) (addP X (P 1) (P 2)) ∈ logInt V τ := by
  have hb : ∀ p : Fin 3 × κ, constantCoeff (P p.1 p.2) = 0 := fun p => hP p.1 p.2
  have hs := hasSubst_of_constantCoeff_zero hb
  have hadd := formalAdd_constantCoeff H (gp_cc (C := C) (κ := κ) (1 : Fin 3)) (gp_cc 2)
  have h := logInt_subst hb (fun p => hI p.1 p.2) (mem_logInt.2 ⟨by
    rw [map_sub, map_add, hAt_cc H (gp_cc 0) (gp_cc 1), hAt_cc H (gp_cc 0) (gp_cc 2), hAt_cc H (gp_cc 0) hadd]
    simp, H.ph2⟩)
  rw [subst_sub hs, subst_add hs, subst_hAt (gp_cc 0) (gp_cc 1) hb, subst_hAt (gp_cc 0) (gp_cc 2) hb,
    subst_hAt (gp_cc 0) hadd hb] at h
  simpa only [subst_addP H (gp_cc 1) (gp_cc 2) hb, subst_gp hP] using h

theorem symm_log (H : RLaw X V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    (ia : ∀ s, IntS V (a s)) (ib : ∀ s, IntS V (b s)) :
    hAt X b a - hAt X a b ∈ logInt V τ := by
  have hp := pair_cc ha hb
  have hs := hasSubst_of_constantCoeff_zero hp
  have h := logInt_subst hp (fun p => by split_ifs; exacts [ia _, ib _]) (mem_logInt.2 ⟨by
    rw [map_sub, hAt_cc H (gp_cc 1) (gp_cc 0), h_cc H]
    simp, H.sy⟩)
  rw [subst_sub hs, subst_hAt (gp_cc 1) (gp_cc 0) hp] at h
  simp only [gp, subst_X hs] at h
  exact h

theorem adj_log (H : RLaw X V) {M M' : Matrix κ κ C} (hM : IsEnd X V M M') {τ : Type}
    {P : Fin 2 → κ → MvPowerSeries τ C}
    (hP : ∀ j s, constantCoeff (P j s) = 0) (hI : ∀ j s, IntS V (P j s)) :
    hAt X (endP X M (P 0)) (P 1) - hAt X (P 0) (endP X M' (P 1)) ∈ logInt V τ := by
  have hb : ∀ p : Fin 2 × κ, constantCoeff (P p.1 p.2) = 0 := fun p => hP p.1 p.2
  have hs := hasSubst_of_constantCoeff_zero hb
  have h0 := constantCoeff_expMulLog H (gp_cc (C := C) (κ := κ) (0 : Fin 2)) M
  have h1 := constantCoeff_expMulLog H (gp_cc (C := C) (κ := κ) (1 : Fin 2)) M'
  have h := logInt_subst hb (fun p => hI p.1 p.2) (mem_logInt.2 ⟨by
    rw [map_sub, hAt_cc H h0 (gp_cc 1), hAt_cc H (gp_cc 0) h1]
    simp, hM.2.2⟩)
  rw [subst_sub hs, subst_hAt h0 (gp_cc 1) hb, subst_hAt (gp_cc 0) h1 hb] at h
  simpa only [subst_endP H (gp_cc 0) hb, subst_endP H (gp_cc 1) hb, subst_gp hP] using h

theorem end_calc : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → IntEnd X V 0 ∧ (∀ A B, IntEnd X V A → IntEnd X V B → IntEnd X V (A + B)) ∧ (∀ A B, IntEnd X V A → IntEnd X V B → IntEnd X V (A * B)) ∧ (∀ A, hEnd X A 0 = 0 ∧ hEnd X 0 A = 0) ∧ (∀ A A' B, IntEnd X V A → IntEnd X V A' → IntEnd X V B → hEnd X A B + hEnd X A' B - hEnd X (A + A') B ∈ logInt V κ ∧ hEnd X B A + hEnd X B A' - hEnd X B (A + A') ∈ logInt V κ) ∧ (∀ A B, IntEnd X V A → IntEnd X V B → hEnd X B A - hEnd X A B ∈ logInt V κ) ∧ (∀ M M' A B, IsEnd X V M M' → IntEnd X V A → IntEnd X V B → hEnd X (M * A) B - hEnd X A (M' * B) ∈ logInt V κ) := by
  intro C _ _ V d I _ κ _ X H
  have hX : ∀ s : κ, constantCoeff (MvPowerSeries.X s : MvPowerSeries κ C) = 0 := fun s => constantCoeff_X s
  have hc : ∀ A s, constantCoeff (endP X A (MvPowerSeries.X : κ → MvPowerSeries κ C) s) = 0 :=
    fun A => constantCoeff_expMulLog H hX A
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [expMulLog_zero H]
    exact intS_zero
  · intro A B hA hB i
    rw [← formalAdd_endP H hX]
    exact formalAdd_integral H (P := ![endP X A MvPowerSeries.X, endP X B MvPowerSeries.X])
      (fun j => by fin_cases j <;> exact hc _) (fun j => by fin_cases j; exacts [hA, hB]) i
  · intro A B hA hB i
    rw [← expMulLog_expMulLog H hX]
    exact expMulLog_integral H hA (hc B) hB i
  · intro A
    unfold hEnd
    rw [expMulLog_zero H]
    exact ⟨hAt_zero_right H (hc A), hAt_zero_left H (hc A)⟩
  · intro A A' B hA hA' hB
    unfold hEnd
    rw [← formalAdd_endP H hX]
    exact ⟨add_left_log H (P := ![endP X A MvPowerSeries.X, endP X A' MvPowerSeries.X, endP X B MvPowerSeries.X])
      (fun j => by fin_cases j <;> exact hc _) (fun j => by fin_cases j; exacts [hA, hA', hB]),
      add_right_log H (P := ![endP X B MvPowerSeries.X, endP X A MvPowerSeries.X, endP X A' MvPowerSeries.X])
      (fun j => by fin_cases j <;> exact hc _) (fun j => by fin_cases j; exacts [hB, hA, hA'])⟩
  · intro A B hA hB
    exact symm_log H (hc A) (hc B) hA hB
  · intro M M' A B hM hA hB
    unfold hEnd
    rw [← expMulLog_expMulLog H hX, ← expMulLog_expMulLog H hX]
    exact adj_log H hM (P := ![endP X A MvPowerSeries.X, endP X B MvPowerSeries.X])
      (fun j => by fin_cases j <;> exact hc _) (fun j => by fin_cases j; exacts [hA, hB])

end GlobalTheory.RowVal.EndCalc
