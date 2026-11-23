import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothA

set_option autoImplicit false

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def lt (ε : Fin n → Bool) (p : Fin n × Fin n) (b : Bool) : Matrix (Fin n) (Fin n) ℂ :=
  if b then S7.cpart2 ε (Matrix.single p.1 p.2 1) else S7.cpart1 ε (Matrix.single p.1 p.2 1)

theorem lt_inG (ε : Fin n → Bool) (p : Fin n × Fin n) (b : Bool) : inG ε (lt ε p b) := by
  unfold lt
  split
  · exact SmDerA.inG_cpart2 ε _
  · exact SmDerA.inG_cpart1 ε _

def wordOf (ε : Fin n → Bool) (w : List (Fin n × Fin n)) (s : Fin w.length → Bool) : List (Matrix (Fin n) (Fin n) ℂ) :=
  List.ofFn fun i => lt ε (w.get i) (s i)

def coefOf (w : List (Fin n × Fin n)) (s : Fin w.length → Bool) : ℂ :=
  ∏ i, if s i then Complex.I else 1

theorem dSW_smooth {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) :
    ∀ (W : List (Matrix (Fin n) (Fin n) ℂ)), (∀ X ∈ W, inG ε X) → ∀ {v : H}, IsSmoothVecU ε σ v →
      IsSmoothVecU ε σ (dSW σ W v)
  | [], _, _, hv => hv
  | X :: W, hW, _, hv => IsSmoothVecU.dS hσ (hW X (List.mem_cons_self ..))
      (dSW_smooth hσ W (fun Y hY => hW Y (List.mem_cons_of_mem _ hY)) hv)

theorem dS_fsum {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → H)
    (hv : ∀ i, IsSmoothVecU ε σ (v i)) : dS σ X (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • dS σ X (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := dS_smul_vec (σ := σ) (0 : ℂ) X (0 : H)
    simpa using this
  | @insert i s hi ih =>
    have h1 : IsSmoothVecU ε σ (c i • v i) := IsSmoothVecU.smul (c i) (hv i)
    have h2 : IsSmoothVecU ε σ (∑ j ∈ s, c j • v j) :=
      (SmDerA.smSub ε σ).sum_mem fun j _ => (SmDerA.smSub ε σ).smul_mem (c j) (hv j)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, dS_add_vec hσ hX h1 h2, dS_smul_vec, ih]

theorem coef_cons (p : Fin n × Fin n) (w : List (Fin n × Fin n)) (b : Bool) (s : Fin w.length → Bool) :
    coefOf (p :: w) (Fin.cons b s : Fin (w.length + 1) → Bool) = (if b then Complex.I else 1) * coefOf w s := by
  unfold coefOf
  exact Fin.prod_univ_succ _

theorem word_cons (ε : Fin n → Bool) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) (b : Bool)
    (s : Fin w.length → Bool) :
    wordOf ε (p :: w) (Fin.cons b s : Fin (w.length + 1) → Bool) = lt ε p b :: wordOf ε w s := by
  unfold wordOf
  exact List.ofFn_succ

theorem wAct_expand {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (x : smD ε σ) : ∀ w : List (Fin n × Fin n),
      ((wAct (smE ε σ) w x : smD ε σ) : H) = ∑ s : Fin w.length → Bool, coefOf w s • dSW σ (wordOf ε w s) x
  | [] => by simp [wAct, wordOf, coefOf, dSW]
  | p :: w => by
    have hx : IsSmoothVecU ε σ (x : H) := (mem_smD_iff ε σ _).mp x.2
    have ih := wAct_expand hσ x w
    have hsm : ∀ s : Fin w.length → Bool, IsSmoothVecU ε σ (dSW σ (wordOf ε w s) x) := fun s =>
      dSW_smooth hσ _ (fun X hX => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hX
        exact lt_inG ε _ _) hx
    show ((smE ε σ p.1 p.2 (wAct (smE ε σ) w x) : smD ε σ) : H) = _
    rw [smE_apply hσ, ih, dS_fsum hσ (SmDerA.inG_cpart1 ε _) _ _ _ hsm,
      dS_fsum hσ (SmDerA.inG_cpart2 ε _) _ _ _ hsm, Finset.smul_sum]
    show _ = ∑ s : Fin (w.length + 1) → Bool, coefOf (p :: w) s • dSW σ (wordOf ε (p :: w) s) (x : H)
    rw [← (Fin.consEquiv fun _ : Fin (w.length + 1) => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun s _ => ?_
      show _ = coefOf (p :: w) (Fin.cons true s : Fin (w.length + 1) → Bool) •
        dSW σ (wordOf ε (p :: w) (Fin.cons true s : Fin (w.length + 1) → Bool)) (x : H)
      rw [coef_cons, word_cons]
      simp [lt, dSW, smul_smul]
    · refine Finset.sum_congr rfl fun s _ => ?_
      show _ = coefOf (p :: w) (Fin.cons false s : Fin (w.length + 1) → Bool) •
        dSW σ (wordOf ε (p :: w) (Fin.cons false s : Fin (w.length + 1) → Bool)) (x : H)
      rw [coef_cons, word_cons]
      simp [lt, dSW]

theorem coefOf_norm (w : List (Fin n × Fin n)) (s : Fin w.length → Bool) : ‖coefOf w s‖ = 1 := by
  unfold coefOf
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  split <;> simp

theorem sum_flatMap_map {α β : Type*} (L : List α) (g : α → List β) (f : β → ℝ) :
    ((L.flatMap g).map f).sum = (L.map fun a => ((g a).map f).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

private lemma toList_map_sum_eq_finset_sum {α : Type*} (s : Finset α) (f : α → ℝ) : (s.toList.map f).sum = ∑ a ∈ s, f a := by
  rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList s, Multiset.map_coe, Multiset.sum_coe]

theorem NE_le_nuJ {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) (j : ℕ) :
    ∃ (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ),
      (∀ w ∈ Ws, w.length ≤ j ∧ ∀ X ∈ w, inG ε X) ∧
      ∀ x : smD ε σ, NE (smE ε σ) j x ≤ C * nuJ σ Ws (x : H) := by
  classical
  refine ⟨(Finset.range (j + 1)).toList.flatMap fun l =>
      (Finset.univ : Finset (Fin l → Fin n × Fin n)).toList.flatMap fun w =>
        (Finset.univ : Finset (Fin (List.ofFn w).length → Bool)).toList.map fun s => wordOf ε (List.ofFn w) s,
    1, ?_, ?_⟩
  · intro W hW
    simp only [List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
      Finset.mem_range] at hW
    obtain ⟨l, hl, w, s, rfl⟩ := hW
    refine ⟨?_, ?_⟩
    · simp only [wordOf, List.length_ofFn]
      omega
    · intro X hX
      simp only [wordOf, List.mem_ofFn] at hX
      obtain ⟨i, rfl⟩ := hX
      exact lt_inG _ _ _
  · intro x
    rw [one_mul]
    simp only [nuJ, sum_flatMap_map, List.map_map, Function.comp_def, toList_map_sum_eq_finset_sum]
    unfold NE
    apply Finset.sum_le_sum
    intro l _
    apply Finset.sum_le_sum
    intro w _
    rw [wAct_expand hσ x]
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro s _
    rw [norm_smul, coefOf_norm, one_mul]

end ReciprocityTheory.ChartRestriction.DS.DecInf
