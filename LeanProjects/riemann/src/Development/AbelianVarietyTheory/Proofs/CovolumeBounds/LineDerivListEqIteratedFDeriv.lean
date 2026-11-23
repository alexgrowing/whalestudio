import Mathlib

open Filter Topology
open scoped ContDiff

namespace GlobalTheory

section Def

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

noncomputable def lineDerivList : List E → (E → V) → E → V
  | [], F => F
  | v :: l, F => fun z => lineDeriv 𝕜 (lineDerivList l F) z v

variable {𝕜}

@[simp] theorem lineDerivList_nil (F : E → V) : lineDerivList 𝕜 [] F = F := rfl

theorem lineDerivList_cons (v : E) (l : List E) (F : E → V) :
    lineDerivList 𝕜 (v :: l) F = fun z => lineDeriv 𝕜 (lineDerivList 𝕜 l F) z v := rfl

theorem lineDerivList_append (l₁ l₂ : List E) (F : E → V) :
    lineDerivList 𝕜 (l₁ ++ l₂) F = lineDerivList 𝕜 l₁ (lineDerivList 𝕜 l₂ F) := by
  induction l₁ with
  | nil => rfl
  | cons v l ih => simp only [List.cons_append, lineDerivList_cons, ih]

theorem lineDerivList_const_smul (l : List E) (c : 𝕜) (F : E → V) :
    lineDerivList 𝕜 l (fun z => c • F z) = fun z => c • lineDerivList 𝕜 l F z := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    simp only [lineDerivList_cons, ih, lineDeriv]
    exact deriv_fun_const_smul_field c _

@[simp] theorem lineDerivList_zero (l : List E) :
    lineDerivList 𝕜 l (fun _ => (0 : V)) = fun _ => 0 := by
  simpa using lineDerivList_const_smul l (0 : 𝕜) (fun _ => (0 : V))

theorem lineDerivList_comp_linearMap {E' : Type*} [AddCommGroup E'] [Module 𝕜 E']
    (L : E' →ₗ[𝕜] E) (l : List E') (F : E → V) :
    lineDerivList 𝕜 l (fun z => F (L z)) = fun z => lineDerivList 𝕜 (l.map L) F (L z) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    simp only [lineDerivList_cons, ih, lineDeriv, List.map_cons, map_add, map_smul]

theorem lineDerivList_comp_add_const (c : E) (l : List E) (F : E → V) :
    lineDerivList 𝕜 l (fun z => F (z + c)) = fun z => lineDerivList 𝕜 l F (z + c) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    simp only [lineDerivList_cons, ih, lineDeriv, add_right_comm]

theorem lineDerivList_map_smul {κ : Type*} (c : κ → 𝕜) (e : κ → E) (l : List κ) (F : E → V) :
    lineDerivList 𝕜 (l.map fun k => c k • e k) F
      = fun z => (l.map c).prod • lineDerivList 𝕜 (l.map e) F z := by
  induction l with
  | nil => simp
  | cons v l ih =>
    funext z
    simp only [List.map_cons, lineDerivList_cons, ih, lineDeriv_smul, List.prod_cons, mul_smul]
    congr 1
    simp only [lineDeriv]
    exact deriv_fun_const_smul_field _ _

theorem lineDerivList_replicate (n : ℕ) (v : E) (F : E → V) (z : E) (t : 𝕜) :
    lineDerivList 𝕜 (List.replicate n v) F (z + t • v)
      = iteratedDeriv n (fun s : 𝕜 => F (z + s • v)) t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, lineDerivList_cons, iteratedDeriv_succ]
    simp only [lineDeriv, add_assoc, ← add_smul, ih]
    rw [deriv_comp_const_add (f := iteratedDeriv n (fun s : 𝕜 => F (z + s • v))), add_zero]

end Def

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

theorem lineDerivList_congr {F G : E → V} {a : E} (h : F =ᶠ[𝓝 a] G) (l : List E) :
    lineDerivList 𝕜 l F =ᶠ[𝓝 a] lineDerivList 𝕜 l G := by
  induction l with
  | nil => exact h
  | cons v l ih =>
    filter_upwards [ih.eventuallyEq_nhds] with z hz
    exact hz.lineDeriv_eq

variable [CompleteSpace V]

theorem analyticAt_lineDeriv {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (v : E) :
    AnalyticAt 𝕜 (fun z => lineDeriv 𝕜 F z v) a := by
  have h1 : AnalyticAt 𝕜 (fun z => fderiv 𝕜 F z v) a :=
    ((ContinuousLinearMap.apply 𝕜 V v).analyticAt _).comp h.fderiv
  refine h1.congr ?_
  filter_upwards [h.eventually_analyticAt] with z hz
  exact hz.differentiableAt.lineDeriv_eq_fderiv.symm

theorem analyticAt_lineDerivList {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (l : List E) :
    AnalyticAt 𝕜 (lineDerivList 𝕜 l F) a := by
  induction l with
  | nil => exact h
  | cons v l ih => exact analyticAt_lineDeriv ih v

theorem lineDerivList_ofFn {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) {n : ℕ} (m : Fin n → E) :
    lineDerivList 𝕜 (List.ofFn m) F a = iteratedFDeriv 𝕜 n F a m := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have hev : lineDerivList 𝕜 (List.ofFn fun i => m i.succ) F
        =ᶠ[𝓝 a] fun z => iteratedFDeriv 𝕜 n F z (Fin.tail m) := by
      filter_upwards [h.eventually_analyticAt] with z hz
      exact ih hz _
    have hd : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n F) a :=
      (h.contDiffAt (n := ω)).differentiableAt_iteratedFDeriv (by simp)
    rw [List.ofFn_succ, lineDerivList_cons, iteratedFDeriv_succ_apply_left]
    dsimp only
    rw [(analyticAt_lineDerivList h _).differentiableAt.lineDeriv_eq_fderiv, hev.fderiv_eq,
      fderiv_continuousMultilinear_apply_const_apply hd]

theorem lineDerivList_eq_iteratedFDeriv {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (l : List E) :
    lineDerivList 𝕜 l F a = iteratedFDeriv 𝕜 l.length F a l.get := by
  rw [← lineDerivList_ofFn h, List.ofFn_get]

theorem lineDerivList_swap {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (v w : E) :
    lineDerivList 𝕜 [v, w] F a = lineDerivList 𝕜 [w, v] F a := by
  have h1 := lineDerivList_ofFn h ![v, w]
  have h2 := lineDerivList_ofFn h ![w, v]
  have h3 := (h.contDiffAt (n := ω)).iteratedFDeriv_comp_perm ![v, w] (Equiv.swap 0 1)
  have h4 : ![v, w] ∘ (Equiv.swap (0 : Fin 2) 1) = ![w, v] := by
    funext i; fin_cases i <;> simp
  rw [h4] at h3
  simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] at h1 h2
  rw [h1, h2, h3]

theorem lineDerivList_perm {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) {l₁ l₂ : List E}
    (hl : l₁.Perm l₂) : lineDerivList 𝕜 l₁ F a = lineDerivList 𝕜 l₂ F a := by
  induction hl generalizing a with
  | nil => rfl
  | cons v _ ih =>
    refine Filter.EventuallyEq.lineDeriv_eq ?_
    filter_upwards [h.eventually_analyticAt] with z hz
    exact ih hz
  | swap v w l => exact lineDerivList_swap (analyticAt_lineDerivList h l) w v
  | trans _ _ ih₁ ih₂ => exact (ih₁ h).trans (ih₂ h)

theorem lineDerivList_add {F G : E → V} {a : E} (hF : AnalyticAt 𝕜 F a) (hG : AnalyticAt 𝕜 G a)
    (l : List E) :
    lineDerivList 𝕜 l (fun z => F z + G z) a
      = lineDerivList 𝕜 l F a + lineDerivList 𝕜 l G a := by
  have hFG : AnalyticAt 𝕜 (fun z => F z + G z) a := hF.add hG
  rw [lineDerivList_eq_iteratedFDeriv hFG, lineDerivList_eq_iteratedFDeriv hF,
    lineDerivList_eq_iteratedFDeriv hG,
    fun_iteratedFDeriv_add_apply (hF.contDiffAt) (hG.contDiffAt)]
  rfl

theorem lineDerivList_sum {κ : Type*} (s : Finset κ) {F : κ → E → V} {a : E}
    (hF : ∀ k ∈ s, AnalyticAt 𝕜 (F k) a) (l : List E) :
    lineDerivList 𝕜 l (fun z => ∑ k ∈ s, F k z) a = ∑ k ∈ s, lineDerivList 𝕜 l (F k) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hs : ∀ k ∈ s, AnalyticAt 𝕜 (F k) a := fun k hk => hF k (Finset.mem_insert_of_mem hk)
    simp only [Finset.sum_insert hj]
    rw [lineDerivList_add (hF j (Finset.mem_insert_self _ _)) (Finset.analyticAt_fun_sum _ hs),
      ih hs]

end Analytic

end GlobalTheory
