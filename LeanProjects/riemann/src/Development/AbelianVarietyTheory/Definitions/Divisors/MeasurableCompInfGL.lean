import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothSpanLeMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry

noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def htInf (y : GL (Fin a) (Cinf E)) : ℝ :=
  ∏ w : InfinitePlace E, htGL (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) y)

def kerInf {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E))
    (F : GA E a → ℂ) (g : GA E a) : ℂ := ∫ x, k x * F (g * infGL E a (γ x)) ∂ν

def rspan (π : CuspSub E a) : Submodule ℂ (GA E a → ℂ) :=
  sInf {S | (∀ φ ∈ π.V, φ.1 ∈ S) ∧ (∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S) ∧
    (∀ F ∈ S, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ S)}

theorem mem_rspan {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ π.V) : φ.1 ∈ rspan π :=
  Submodule.mem_sInf.2 fun _ hS => hS.1 φ h

theorem rt_mem_rspan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ rspan π) (h : GA E a) :
    (fun g => F (g * h)) ∈ rspan π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h

theorem kerInf_mem_rspan {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ rspan π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ rspan π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.2 F (Submodule.mem_sInf.1 hF S hS) X ν k γ hk

theorem rspan_le {π : CuspSub E a} {S : Submodule ℂ (GA E a → ℂ)} (h₁ : ∀ φ ∈ π.V, φ.1 ∈ S)
    (h₂ : ∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S)
    (h₃ : ∀ F ∈ S, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ S) : rspan π ≤ S :=
  sInf_le ⟨h₁, h₂, h₃⟩

theorem one_le_htInf (y : GL (Fin a) (Cinf E)) : 1 ≤ htInf y := by
  unfold htInf
  calc (1 : ℝ) = ∏ _w : InfinitePlace E, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem htInf_pos (y : GL (Fin a) (Cinf E)) : 0 < htInf y := lt_of_lt_of_le one_pos (one_le_htInf y)

theorem htGL_le_htInf (y : GL (Fin a) (Cinf E)) (w : InfinitePlace E) :
    htGL (Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w) y) ≤ htInf y := by
  classical
  unfold htInf
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
  refine le_mul_of_one_le_right (htGL_pos _).le ?_
  calc (1 : ℝ) = ∏ _w ∈ Finset.univ.erase w, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun w _ => one_le_htGL _

theorem norm_entry_le_htInf (y : GL (Fin a) (Cinf E)) (i j : Fin a) (w : InfinitePlace E) :
    ‖(y : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ≤ htInf y ∧
      ‖((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ≤ htInf y := by
  set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ := Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
  refine ⟨(norm_entry_le_htGL (p y) i j).trans (htGL_le_htInf y w), ?_⟩
  have e : ((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) i j w =
      (((p y)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j := by
    rw [← map_inv]; rfl
  rw [e]
  exact (norm_entry_le_htGL _ i j).trans ((htGL_inv (p y)).le.trans (htGL_le_htInf y w))

theorem height_le_htInf (y : GL (Fin a) (Cinf E)) : height y ≤ 3 * htInf y := by
  have h0 := (htInf_pos y).le
  have h1 : ‖toL y.val‖ ≤ htInf y :=
    pi_norm_le_iff_of_nonneg h0 |>.2 fun i => pi_norm_le_iff_of_nonneg h0 |>.2 fun j =>
      pi_norm_le_iff_of_nonneg h0 |>.2 fun w => (norm_entry_le_htInf y i j w).1
  have h2 : ‖toL (y⁻¹).val‖ ≤ htInf y :=
    pi_norm_le_iff_of_nonneg h0 |>.2 fun i => pi_norm_le_iff_of_nonneg h0 |>.2 fun j =>
      pi_norm_le_iff_of_nonneg h0 |>.2 fun w => (norm_entry_le_htInf y i j w).2
  unfold height
  linarith [one_le_htInf y]

theorem IsRapidInf.of_htInf {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : Measurable k) (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)) i j)
    (hm : ∀ N : ℕ, Integrable (fun x => ‖k x‖ * htInf (γ x) ^ N) ν) : IsRapidInf ν k γ := by
  refine ⟨hk, measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hγ i j, fun N => ?_⟩
  refine ((hm N).const_mul (3 ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine (hk.norm.mul ?_).aestronglyMeasurable
    have hm' : Measurable fun x => toL (γ x).val :=
      measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => hγ i j
    have hi : Measurable fun x => toL ((γ x)⁻¹).val := by
      refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun w => ?_
      set p : GL (Fin a) (Cinf E) →* GL (Fin a) ℂ :=
        Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)
      have e : (fun x => toL ((γ x)⁻¹).val i j w) =
          fun x => (((p (γ x))⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j := by
        funext x
        rw [← map_inv]; rfl
      rw [e]
      exact measurable_comp_GL (F := fun g : GL (Fin a) ℂ => ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)
        ((Units.continuous_coe_inv : Continuous fun g : GL (Fin a) ℂ =>
          ((g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)).matrix_elem i j)
        fun i' j' => (measurable_pi_apply w).comp (hγ i' j')
    unfold height
    exact ((measurable_const.add hm'.norm).add hi.norm).pow_const N
  · have h0 : 0 ≤ height (γ x) := by unfold height; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖k x‖ * height (γ x) ^ N ≤ ‖k x‖ * (3 * htInf (γ x)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (height_le_htInf _) N) (norm_nonneg _)
      _ = 3 ^ N * (‖k x‖ * htInf (γ x) ^ N) := by rw [mul_pow]; ring

theorem measurable_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) : Measurable (chart φ g) := by
  classical
  have e : chart φ g = (invSet E a).piecewise (chart φ g) (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ invSet E a
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      exact dif_neg hx
  rw [e]
  exact (hφ g).continuousOn.measurable_piecewise continuousOn_const isOpen_invSet.measurableSet

theorem measurable_comp_infGL {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun x => φ (g * infGL E a (γ x)) := by
  have h : Measurable fun x => toL (γ x).val := hγ
  have e : (fun x => φ (g * infGL E a (γ x))) = fun x => chart φ g (toL (γ x).val) :=
    funext fun x => (chart_val φ g (γ x)).symm
  rw [e]
  exact (measurable_chart hφ g).comp h

theorem IsRapidInf.integrable {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) {g : GA E a}
    (hg : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * height y ^ N) :
    Integrable (fun x => k x * φ (g * infGL E a (γ x))) ν := by
  obtain ⟨C, N, hC⟩ := hg
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N := pow_pos (by unfold height; positivity) N
    exact nonneg_of_mul_nonneg_left h hp
  refine ((hk.2.2 N).const_mul C).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hk.1.mul (measurable_comp_infGL hφ g hk.2.1)).aestronglyMeasurable
  · rw [norm_mul]
    calc ‖k x‖ * ‖φ (g * infGL E a (γ x))‖ ≤ ‖k x‖ * (C * height (γ x) ^ N) :=
          mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
      _ = C * (‖k x‖ * height (γ x) ^ N) := by ring

theorem rspan_ne_bot (π : CuspSub E a) : rspan π ≠ ⊥ := by
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  intro hb
  have h := mem_rspan hφ
  rw [hb, Submodule.mem_bot] at h
  exact h0 (Subtype.ext h)

theorem rspan_le_leftInv (π : CuspSub E a) : rspan π ≤ SpanModel.leftInv E a := by
  refine rspan_le (fun φ hφ => (π.cusp φ hφ).1.left) (fun F hF h γ g => ?_) fun F hF X _ ν _ k γ _ γ' g => ?_
  · change F (ratGL E a γ * g * h) = F (g * h)
    rw [mul_assoc]; exact hF γ _
  · change kerInf ν k γ F (ratGL E a γ' * g) = kerInf ν k γ F g
    simp only [kerInf, mul_assoc]
    congr 1
    funext x
    rw [hF γ']

theorem rspan_left (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ rspan π) (γ : GL (Fin a) E) (g : GA E a) :
    F (ratGL E a γ * g) = F g :=
  rspan_le_leftInv π hF γ g

theorem rspan_eq_mspanR (π : CuspSub E a) : rspan π = mspanR π := by
  refine le_antisymm (rspan_le ?_ ?_ ?_) ?_
  · exact fun φ hφ => Submodule.mem_sInf.2 fun _ hS => hS.1 φ hφ
  · exact fun F hF h => Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h
  · exact fun F hF X _ ν _ k γ hk => Submodule.mem_sInf.2 fun S hS => hS.2.2 F (Submodule.mem_sInf.1 hF S hS) X _ ν inferInstance k γ hk
  · refine sInf_le ⟨fun φ hφ => mem_rspan hφ, fun F hF h => rt_mem_rspan hF h, fun F hF X _ ν _ k γ hk => ?_⟩
    exact kerInf_mem_rspan hF ν hk

open Classical in

def plS (w : InfinitePlace E) : ℂ →ₙ+* Cinf E where
  toFun z := Pi.single w z
  map_mul' z z' := by ext w'; by_cases h : w' = w <;> simp [Pi.single_apply, h]
  map_zero' := by ext w'; simp [Pi.single_apply]
  map_add' z z' := by ext w'; by_cases h : w' = w <;> simp [Pi.single_apply, h]

def plGL (w : InfinitePlace E) : GL (Fin a) ℂ →* GL (Fin a) (Cinf E) := cornerGL a (plS w)

open Classical in

theorem plGL_apply (w : InfinitePlace E) (g : GL (Fin a) ℂ) (i j : Fin a) (w' : InfinitePlace E) :
    (plGL w g : Matrix (Fin a) (Fin a) (Cinf E)) i j w' =
      if w' = w then (g : Matrix (Fin a) (Fin a) ℂ) i j else (1 : Matrix (Fin a) (Fin a) ℂ) i j := by
  change (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w' - (Pi.single w ((1 : Matrix (Fin a) (Fin a) ℂ) i j) : Cinf E) w' +
    (Pi.single w ((g : Matrix (Fin a) (Fin a) ℂ) i j) : Cinf E) w' = _
  simp only [Pi.single_apply, Matrix.one_apply]
  split_ifs <;> simp_all

open Classical in

theorem map_plGL (w : InfinitePlace E) (g : GL (Fin a) ℂ) (w' : InfinitePlace E) :
    Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w') (plGL w g) =
      if w' = w then g else 1 := by
  classical
  ext i j
  change (plGL w g : Matrix (Fin a) (Fin a) (Cinf E)) i j w' = _
  rw [plGL_apply]
  split_ifs <;> rfl

theorem isRapidInf_dirac (y : GL (Fin a) (Cinf E)) :
    IsRapidInf (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => y) :=
  ⟨measurable_const, measurable_const, fun _ => integrable_const _⟩

theorem kerInf_dirac (y : GL (Fin a) (Cinf E)) (F : GA E a → ℂ) (g : GA E a) :
    kerInf (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => y) F g = F (g * infGL E a y) := by
  simp [kerInf]

example (π : CuspSub E a) : 1 ≤ htInf (1 : GL (Fin a) (Cinf E)) ∧ rspan π ≠ ⊥ := ⟨one_le_htInf 1, rspan_ne_bot π⟩

example (π : CuspSub E a) {F : GA E a → ℂ} (hF : F ∈ rspan π) (y : GL (Fin a) (Cinf E)) :
    (fun g => F (g * infGL E a y)) ∈ rspan π := by
  have h := kerInf_mem_rspan hF (Measure.dirac ()) (isRapidInf_dirac y)
  rwa [show kerInf (Measure.dirac ()) (fun _ : Unit => (1 : ℂ)) (fun _ => y) F = fun g => F (g * infGL E a y) from
    funext (kerInf_dirac y F)] at h

example (w : InfinitePlace E) : htInf (plGL (a := a) w 1) = htGL (1 : GL (Fin a) ℂ) ^ Fintype.card (InfinitePlace E) := by
  rw [map_one]
  unfold htInf
  simp

end GlobalTheory.JSW
