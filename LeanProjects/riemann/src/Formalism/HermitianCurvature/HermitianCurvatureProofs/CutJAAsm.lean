import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAQQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP Classical

noncomputable section

section van

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem rdV_van {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {F : B.Mat k r → E'} {U : Set (B.Mat k r)}
    (hU : IsOpen U) (hF : ∀ g ∈ U, F g = 0) (X : B.Mat k r) : ∀ g ∈ U, RdV X F g = 0 := by
  intro g hg
  unfold RdV
  have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) ∈ U := by rw [Formalism.FourierDecayAlt.P.B5.curve_zero]; exact hg
  have hev : (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[nhds 0] fun _ => (0 : E') := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)] with t ht
    exact hF _ ht
  rw [hev.deriv_eq]
  simp

theorem rw_van {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {F : B.Mat k r → E'} {U : Set (B.Mat k r)}
    (hU : IsOpen U) (hF : ∀ g ∈ U, F g = 0) (w : List (B.Mat k r)) : ∀ g ∈ U, B.Rw w F g = 0 := by
  induction w with
  | nil => exact hF
  | cons X w ih => exact rdV_van hU ih X

theorem opApply_van {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (Θ : B.DiffOp k r Wp' Wq') {J : B.Mat k r → (Wq' →L[ℂ] Wp')}
    {U : Set (B.Mat k r)} (hU : IsOpen U) (hJ : ∀ g ∈ U, J g = 0) : ∀ g ∈ U, B.opApply Θ J g = 0 := by
  intro g hg
  unfold B.opApply
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨Tm, -, rfl⟩ := List.mem_map.1 hx
  rw [rw_van hU hJ Tm.word g hg, map_zero]

end van

theorem list_sum_flatMap {α M : Type} [AddCommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem list_sum_map_flatMap {α β M : Type} [AddCommMonoid M] (l : List α) (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

section pair

theorem list_sum_map_add {α M : Type} [AddCommMonoid M] (l : List α) (f g : α → M) :
    (l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; abel

theorem list_sum_comm {α β M : Type} [AddCommMonoid M] (l₁ : List α) (l₂ : List β) (g : α → β → M) :
    (l₁.map fun a => (l₂.map fun b => g a b).sum).sum = (l₂.map fun b => (l₁.map fun a => g a b).sum).sum := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [list_sum_map_add]

theorem list_mul_sum {α : Type} (l : List α) (a : ℂ) (f : α → ℂ) :
    a * (l.map f).sum = (l.map fun x => a * f x).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

variable (P : M.Par)

def PI (U V : M.Ty P → MA.SmQ P.r P.TT) : Prop :=
  ∀ π, Integrable (fun q => MA.evQ P (U π) q * conj (MA.evQ P (V π) q)) (MA.mu0 P.r P.TT)

variable {P}

theorem ipA_eq (U V : M.Ty P → MA.SmQ P.r P.TT) :
    MA.ipA P U V = ∑ π, ∫ q, MA.evQ P (U π) q * conj (MA.evQ P (V π) q) ∂MA.mu0 P.r P.TT := rfl

theorem evQ_add (a b : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) : MA.evQ P (a + b) q = MA.evQ P a q + MA.evQ P b q := rfl
theorem evQ_smul (c : ℂ) (a : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) : MA.evQ P (c • a) q = c * MA.evQ P a q := rfl
theorem evQ_zero (q : MA.Qp P.r P.TT) : MA.evQ P (0 : MA.SmQ P.r P.TT) q = 0 := rfl

theorem PI_add_left {U U' V : M.Ty P → MA.SmQ P.r P.TT} (h : PI P U V) (h' : PI P U' V) : PI P (U + U') V := by
  intro π
  have e : (fun q => MA.evQ P ((U + U') π) q * conj (MA.evQ P (V π) q)) =
      (fun q => MA.evQ P (U π) q * conj (MA.evQ P (V π) q)) + (fun q => MA.evQ P (U' π) q * conj (MA.evQ P (V π) q)) := by
    funext q; simp only [Pi.add_apply, evQ_add]; ring
  rw [e]; exact (h π).add (h' π)

theorem PI_smul_left {U V : M.Ty P → MA.SmQ P.r P.TT} (c : ℂ) (h : PI P U V) : PI P (c • U) V := by
  intro π
  have e : (fun q => MA.evQ P ((c • U) π) q * conj (MA.evQ P (V π) q)) =
      fun q => c * (MA.evQ P (U π) q * conj (MA.evQ P (V π) q)) := by
    funext q; simp only [Pi.smul_apply, evQ_smul]; ring
  rw [e]; exact (h π).const_mul c

theorem PI_zero_left (V : M.Ty P → MA.SmQ P.r P.TT) : PI P 0 V := by
  intro π
  have e : (fun q => MA.evQ P ((0 : M.Ty P → MA.SmQ P.r P.TT) π) q * conj (MA.evQ P (V π) q)) = fun _ => 0 := by
    funext q; simp only [Pi.zero_apply, evQ_zero, zero_mul]
  rw [e]; exact integrable_zero _ _ _

theorem PI_add_right {U V V' : M.Ty P → MA.SmQ P.r P.TT} (h : PI P U V) (h' : PI P U V') : PI P U (V + V') := by
  intro π
  have e : (fun q => MA.evQ P (U π) q * conj (MA.evQ P ((V + V') π) q)) =
      (fun q => MA.evQ P (U π) q * conj (MA.evQ P (V π) q)) + (fun q => MA.evQ P (U π) q * conj (MA.evQ P (V' π) q)) := by
    funext q; simp only [Pi.add_apply, evQ_add, map_add]; ring
  rw [e]; exact (h π).add (h' π)

theorem PI_smul_right {U V : M.Ty P → MA.SmQ P.r P.TT} (c : ℂ) (h : PI P U V) : PI P U (c • V) := by
  intro π
  have e : (fun q => MA.evQ P (U π) q * conj (MA.evQ P ((c • V) π) q)) =
      fun q => conj c * (MA.evQ P (U π) q * conj (MA.evQ P (V π) q)) := by
    funext q; simp only [Pi.smul_apply, evQ_smul, map_mul]; ring
  rw [e]; exact (h π).const_mul _

theorem PI_zero_right (U : M.Ty P → MA.SmQ P.r P.TT) : PI P U 0 := by
  intro π
  have e : (fun q => MA.evQ P (U π) q * conj (MA.evQ P ((0 : M.Ty P → MA.SmQ P.r P.TT) π) q)) = fun _ => 0 := by
    funext q; simp only [Pi.zero_apply, evQ_zero, map_zero, mul_zero]
  rw [e]; exact integrable_zero _ _ _

theorem ipA_add_left {U U' V : M.Ty P → MA.SmQ P.r P.TT} (h : PI P U V) (h' : PI P U' V) :
    MA.ipA P (U + U') V = MA.ipA P U V + MA.ipA P U' V := by
  simp only [ipA_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← integral_add (h π) (h' π)]
  congr 1; funext q; simp only [Pi.add_apply, evQ_add]; ring

theorem ipA_smul_left (c : ℂ) (U V : M.Ty P → MA.SmQ P.r P.TT) : MA.ipA P (c • U) V = c * MA.ipA P U V := by
  simp only [ipA_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← integral_const_mul]
  congr 1; funext q; simp only [Pi.smul_apply, evQ_smul]; ring

theorem ipA_zero_left (V : M.Ty P → MA.SmQ P.r P.TT) : MA.ipA P 0 V = 0 := by
  simp only [ipA_eq]
  refine Finset.sum_eq_zero fun π _ => ?_
  simp [evQ_zero]

theorem ipA_add_right {U V V' : M.Ty P → MA.SmQ P.r P.TT} (h : PI P U V) (h' : PI P U V') :
    MA.ipA P U (V + V') = MA.ipA P U V + MA.ipA P U V' := by
  simp only [ipA_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← integral_add (h π) (h' π)]
  congr 1; funext q; simp only [Pi.add_apply, evQ_add, map_add]; ring

theorem ipA_smul_right (c : ℂ) (U V : M.Ty P → MA.SmQ P.r P.TT) :
    MA.ipA P U (c • V) = conj c * MA.ipA P U V := by
  simp only [ipA_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← integral_const_mul]
  congr 1; funext q; simp only [Pi.smul_apply, evQ_smul, map_mul]; ring

theorem ipA_zero_right (U : M.Ty P → MA.SmQ P.r P.TT) : MA.ipA P U 0 = 0 := by
  simp only [ipA_eq]
  refine Finset.sum_eq_zero fun π _ => ?_
  simp [evQ_zero]

theorem ipA_sum_left {ι : Type} (l : List ι) (c : ι → ℂ) (u : ι → M.Ty P → MA.SmQ P.r P.TT)
    (V : M.Ty P → MA.SmQ P.r P.TT) (h : ∀ i ∈ l, PI P (u i) V) :
    MA.ipA P ((l.map fun i => c i • u i).sum) V = (l.map fun i => c i * MA.ipA P (u i) V).sum ∧
      PI P ((l.map fun i => c i • u i).sum) V := by
  induction l with
  | nil => exact ⟨by simpa using ipA_zero_left V, by simpa using PI_zero_left V⟩
  | cons i l ih =>
    obtain ⟨h1, h2⟩ := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
    have hi : PI P (c i • u i) V := PI_smul_left (c i) (h i (List.mem_cons_self ..))
    simp only [List.map_cons, List.sum_cons]
    exact ⟨by rw [ipA_add_left hi h2, ipA_smul_left, h1], PI_add_left hi h2⟩

theorem ipA_sum_right {ι : Type} (U : M.Ty P → MA.SmQ P.r P.TT) (l : List ι) (c : ι → ℂ)
    (u : ι → M.Ty P → MA.SmQ P.r P.TT) (h : ∀ i ∈ l, PI P U (u i)) :
    MA.ipA P U ((l.map fun i => c i • u i).sum) = (l.map fun i => conj (c i) * MA.ipA P U (u i)).sum ∧
      PI P U ((l.map fun i => c i • u i).sum) := by
  induction l with
  | nil => exact ⟨by simpa using ipA_zero_right U, by simpa using PI_zero_right U⟩
  | cons i l ih =>
    obtain ⟨h1, h2⟩ := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
    have hi : PI P U (c i • u i) := PI_smul_right (c i) (h i (List.mem_cons_self ..))
    simp only [List.map_cons, List.sum_cons]
    exact ⟨by rw [ipA_add_right hi h2, ipA_smul_right, h1], PI_add_right hi h2⟩

theorem pairing_integrable_of_square_integrable {U V : M.Ty P → MA.SmQ P.r P.TT} {ε : ℝ}
    (hU0 : ∀ π q, MA.Gq P q < ε → MA.evQ P (U π) q = 0)
    (hU2 : ∀ π, IntegrableOn (fun q => ‖MA.evQ P (U π) q‖ ^ 2) {q | ε ≤ MA.Gq P q} (MA.mu0 P.r P.TT))
    (hV2 : ∀ π, IntegrableOn (fun q => ‖MA.evQ P (V π) q‖ ^ 2) {q | ε ≤ MA.Gq P q} (MA.mu0 P.r P.TT)) : PI P U V := by
  intro π
  have hs : MeasurableSet {q : MA.Qp P.r P.TT | ε ≤ MA.Gq P q} := measurableSet_le measurable_const (MA.Gq_meas P)
  have hmU := jd_evQ_meas P (U π)
  have hmV := jd_evQ_meas P (V π)
  have hm : AEStronglyMeasurable (fun q => MA.evQ P (U π) q * conj (MA.evQ P (V π) q)) (MA.mu0 P.r P.TT) :=
    hmU.mul (Complex.continuous_conj.comp_aestronglyMeasurable hmV)
  have hOn : IntegrableOn (fun q => MA.evQ P (U π) q * conj (MA.evQ P (V π) q)) {q | ε ≤ MA.Gq P q}
      (MA.mu0 P.r P.TT) := by
    refine Integrable.mono' (((hU2 π).add (hV2 π)).div_const 2) hm.restrict (Filter.Eventually.of_forall fun q => ?_)
    simp only [norm_mul, Complex.norm_conj, Pi.add_apply]
    nlinarith [sq_nonneg (‖MA.evQ P (U π) q‖ - ‖MA.evQ P (V π) q‖)]
  have heq : (fun q => MA.evQ P (U π) q * conj (MA.evQ P (V π) q)) =
      Set.indicator {q | ε ≤ MA.Gq P q} (fun q => MA.evQ P (U π) q * conj (MA.evQ P (V π) q)) := by
    funext q
    by_cases hq : q ∈ {q : MA.Qp P.r P.TT | ε ≤ MA.Gq P q}
    · rw [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_notMem hq, hU0 π q (not_le.1 hq), zero_mul]
  rw [heq]
  exact (integrable_indicator_iff hs).2 hOn

end pair

theorem ja_arith (Cj Cl Cgr Sg R n N A AB : ℝ) (hCj : 0 ≤ Cj) (hSg : 0 ≤ Sg) (hR : 0 ≤ R) (hn : 1 ≤ n) (hN : 0 ≤ N)
    (hAB : AB ≤ 2 * n * (R + 1) + 1)
    (hA : 200 * (1 + |Cl| + |Cgr|) * (1 + Cj) * (1 + Sg) * ((R + 1) ^ 4 * (N * n ^ 2 + n ^ 3)) ≤ A) :
    Cl * (R + 1) * n ^ 2 + 6 * R * (Cj * n) + Cj * (R + 1) * n + 2 * (Sg * (R + 1)) * (Cj * n + 1) ≤
        A - (2 * N + 2) * (Cj * (R + 1) * n + 2 * (Sg * (R + 1)) * (Cj * n)) ∧
      AB + Cgr * (R + 1) * n ^ 2 + 6 * R * (Cj * n + 5) + Cj * (R + 1) * n + 2 * (Sg * (R + 1)) * (Cj * n + 5) ≤
        A - (2 * N + 2) * (Cj * (R + 1) * n + 2 * (Sg * (R + 1)) * (Cj * n)) ∧
      Cl * (R + 1) ^ 2 * n + 5 * (Sg * (R + 1)) ≤
        A - (2 * N + 2) * (Cj * (R + 1) * n + 2 * (Sg * (R + 1)) * (Cj * n)) := by
  set W : ℝ := (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) with hW
  have hX : 1 ≤ R + 1 := by linarith
  have hX0 : 0 ≤ R + 1 := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hX4 : R + 1 ≤ (R + 1) ^ 4 := le_self_pow₀ hX (by norm_num)
  have hX24 : (R + 1) ^ 2 ≤ (R + 1) ^ 4 := pow_le_pow_right₀ hX (by norm_num)
  have hn2 : n ≤ n ^ 2 := le_self_pow₀ hn (by norm_num)
  have hn3 : n ≤ n ^ 3 := le_self_pow₀ hn (by norm_num)
  have hn23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn (by norm_num)
  have h1n3 : 1 ≤ n ^ 3 := one_le_pow₀ hn
  have hNn : 0 ≤ N * n ^ 2 := by positivity
  have hY : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ≤ (R + 1) ^ 4 → b ≤ n ^ 3 → a * b ≤ W := by
    intro a b ha hb h1 h2
    calc a * b ≤ (R + 1) ^ 4 * n ^ 3 := mul_le_mul h1 h2 hb (by positivity)
      _ ≤ W := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have f1 : (R + 1) * n ^ 2 ≤ W := hY _ _ hX0 (by positivity) hX4 hn23
  have f2 : (R + 1) ^ 2 * n ≤ W := hY _ _ (by positivity) hn0 hX24 hn3
  have f3 : (R + 1) * n ≤ W := hY _ _ hX0 hn0 hX4 hn3
  have f4 : R * n ≤ W := hY _ _ hR hn0 (by linarith) hn3
  have f5 : R + 1 ≤ W := by have := hY _ _ hX0 (by norm_num : (0:ℝ) ≤ 1) hX4 h1n3; linarith
  have f6 : 1 ≤ W := le_trans hX f5
  have f8 : R ≤ W := by linarith
  have f7 : (N + 1) * ((R + 1) * n) ≤ W := by
    have h1' : N * n ≤ N * n ^ 2 := mul_le_mul_of_nonneg_left hn2 hN
    have h2' : (R + 1) * (N * n + n) ≤ (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) :=
      mul_le_mul hX4 (by linarith) (by positivity) (by positivity)
    have e : (N + 1) * ((R + 1) * n) = (R + 1) * (N * n + n) := by ring
    rw [e, hW]; exact h2'
  have hW0 : 0 ≤ W := by linarith
  have hM : (2 * N + 2) * (Cj * (R + 1) * n + 2 * (Sg * (R + 1)) * (Cj * n)) ≤ (2 * Cj + 4 * Cj * Sg) * W := by
    have e : (2 * N + 2) * (Cj * (R + 1) * n + 2 * (Sg * (R + 1)) * (Cj * n)) =
        (2 * Cj + 4 * Cj * Sg) * ((N + 1) * ((R + 1) * n)) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left f7 (by positivity)
  have g1 : Cl * ((R + 1) * n ^ 2) ≤ |Cl| * W :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self Cl) (by positivity)) (mul_le_mul_of_nonneg_left f1 (abs_nonneg _))
  have g1' : Cgr * ((R + 1) * n ^ 2) ≤ |Cgr| * W :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self Cgr) (by positivity)) (mul_le_mul_of_nonneg_left f1 (abs_nonneg _))
  have g2 : Cl * ((R + 1) ^ 2 * n) ≤ |Cl| * W :=
    le_trans (mul_le_mul_of_nonneg_right (le_abs_self Cl) (by positivity)) (mul_le_mul_of_nonneg_left f2 (abs_nonneg _))
  have g3 : Cj * (R * n) ≤ Cj * W := mul_le_mul_of_nonneg_left f4 hCj
  have g4 : Cj * ((R + 1) * n) ≤ Cj * W := mul_le_mul_of_nonneg_left f3 hCj
  have g5 : Sg * Cj * ((R + 1) * n) ≤ Sg * Cj * W := mul_le_mul_of_nonneg_left f3 (by positivity)
  have g6 : Sg * (R + 1) ≤ Sg * W := mul_le_mul_of_nonneg_left f5 hSg
  have g7 : n * (R + 1) ≤ W := by linarith
  have hAbs : 0 ≤ |Cl| + |Cgr| := by positivity
  have hK : (40 + |Cl| + |Cgr| + 10 * Cj + 10 * Sg + 10 * Cj * Sg) * W ≤
      200 * (1 + |Cl| + |Cgr|) * (1 + Cj) * (1 + Sg) * W := by
    apply mul_le_mul_of_nonneg_right _ hW0
    have h1 : 0 ≤ (|Cl| + |Cgr|) * Cj := by positivity
    have h2 : 0 ≤ (|Cl| + |Cgr|) * Sg := by positivity
    have h3 : 0 ≤ Cj * Sg := by positivity
    have h4 : 0 ≤ (|Cl| + |Cgr|) * Cj * Sg := by positivity
    have e : 200 * (1 + |Cl| + |Cgr|) * (1 + Cj) * (1 + Sg) = 200 + 200 * (|Cl| + |Cgr|) + 200 * Cj + 200 * Sg +
        200 * ((|Cl| + |Cgr|) * Cj) + 200 * ((|Cl| + |Cgr|) * Sg) + 200 * (Cj * Sg) + 200 * ((|Cl| + |Cgr|) * Cj * Sg) := by
      ring
    rw [e]
    have : 0 ≤ |Cl| + |Cgr| := hAbs
    linarith
  have hA' : (40 + |Cl| + |Cgr| + 10 * Cj + 10 * Sg + 10 * Cj * Sg) * W ≤ A := le_trans hK (by rw [hW] at hA ⊢; linarith)
  have hAbs1 : 0 ≤ |Cl| := abs_nonneg _
  have hAbs2 : 0 ≤ |Cgr| := abs_nonneg _
  have hCjW : 0 ≤ Cj * W := by positivity
  have hSgW : 0 ≤ Sg * W := by positivity
  have hCSW : 0 ≤ Cj * Sg * W := by positivity
  have hClW : 0 ≤ |Cl| * W := by positivity
  have hCgW : 0 ≤ |Cgr| * W := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have e : Cl * (R + 1) * n ^ 2 + 6 * R * (Cj * n) + Cj * (R + 1) * n + 2 * (Sg * (R + 1)) * (Cj * n + 1) =
        Cl * ((R + 1) * n ^ 2) + 6 * (Cj * (R * n)) + Cj * ((R + 1) * n) + 2 * (Sg * Cj * ((R + 1) * n)) +
          2 * (Sg * (R + 1)) := by ring
    rw [e]; linarith
  · have e : AB + Cgr * (R + 1) * n ^ 2 + 6 * R * (Cj * n + 5) + Cj * (R + 1) * n + 2 * (Sg * (R + 1)) * (Cj * n + 5) =
        AB + Cgr * ((R + 1) * n ^ 2) + 6 * (Cj * (R * n)) + 30 * R + Cj * ((R + 1) * n) +
          2 * (Sg * Cj * ((R + 1) * n)) + 10 * (Sg * (R + 1)) := by ring
    rw [e]
    have hABW : AB ≤ 3 * W := by linarith
    have h30 : 30 * R ≤ 30 * W := by linarith
    linarith
  · have e : Cl * (R + 1) ^ 2 * n + 5 * (Sg * (R + 1)) = Cl * ((R + 1) ^ 2 * n) + 5 * (Sg * (R + 1)) := by ring
    rw [e]; linarith

section place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

abbrev OpT (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Type := B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))

variable {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))} {v : Fin S.f}

def Van (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (ε : ℝ) (J : GFn S v) : Prop :=
  ∀ g, GfP S T v g < ε → J g = 0

theorem van_opApply (Θ : OpT S v) {ε : ℝ} {J : GFn S v} (h : Van S T v ε J) : Van S T v ε (B.opApply Θ J) := by
  have hU : IsOpen {g : B.Mat S.G.k S.G.r | GfP S T v g < ε} :=
    isOpen_lt (Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _) continuous_const
  intro g hg
  exact opApply_van Θ hU (fun g hg => h g hg) g hg

theorem van_applyL (l : List (OpT S v)) {ε : ℝ} {J : GFn S v} (h : Van S T v ε J) :
    Van S T v ε (applyL S v l J) := by
  induction l with
  | nil => exact h
  | cons Θ l ih => exact van_opApply Θ ih

theorem van_mulG {φ : ℝ → ℝ} {ε : ℝ} (hφ : ∀ x, x ≤ ε → φ x = 0) (J : GFn S v) : Van S T v ε (mulG S T v φ J) := by
  intro g hg
  simp [mulG, hφ _ hg.le]

theorem applyL_cons (Θ : OpT S v) (l : List (OpT S v)) (J : GFn S v) :
    applyL S v (Θ :: l) J = B.opApply Θ (applyL S v l J) := rfl

theorem applyL_append (l₁ l₂ : List (OpT S v)) (J : GFn S v) :
    applyL S v (l₁ ++ l₂) J = applyL S v l₁ (applyL S v l₂ J) := by
  unfold applyL; rw [List.foldr_append]

theorem adjL_cons (Θ : OpT S v) (l : List (OpT S v)) (J : GFn S v) :
    adjL S v (Θ :: l) J = adjL S v l (B.opAdj Θ J) := rfl

theorem apply_list_preserves_smooth_forms (hFF : ∀ Θ : OpT S v, IsAAOp S T v Θ → ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v)
    (l : List (OpT S v)) (hl : ∀ Θ ∈ l, IsAAOp S T v Θ) {J : GFn S v} (hJ : J ∈ smoothFormsPositiveCone S T v) : applyL S v l J ∈ smoothFormsPositiveCone S T v := by
  induction l with
  | nil => exact hJ
  | cons Θ l ih =>
    exact (hFF Θ (hl Θ (List.mem_cons_self ..)) _ (ih fun Θ' h => hl Θ' (List.mem_cons_of_mem _ h))).1

theorem adjoint_list_preserves_smooth_forms (hFF : ∀ Θ : OpT S v, IsAAOp S T v Θ → ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v)
    (l : List (OpT S v)) (hl : ∀ Θ ∈ l, IsAAOp S T v Θ) : ∀ {J : GFn S v}, J ∈ smoothFormsPositiveCone S T v → adjL S v l J ∈ smoothFormsPositiveCone S T v := by
  induction l with
  | nil => intro J hJ; exact hJ
  | cons Θ l ih =>
    intro J hJ
    exact ih (fun Θ' h => hl Θ' (List.mem_cons_of_mem _ h)) (hFF Θ (hl Θ (List.mem_cons_self ..)) J hJ).2

theorem trJ_van (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z')
    {ε : ℝ} {J : GFn S v} (h : Van S T v ε J) :
    ∀ π q, MA.Gq (D.parOf S v) q < ε → MA.evQ (D.parOf S v) (trJ S T v e J π) q = 0 := by
  intro π q hq
  have hζ : Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' < Complex.normSq q.1.2 := by
    rw [← hTT]; exact q.2.2
  have hGq : GfP S T v (B.gq (T v).base q.1) = MA.Gq (D.parOf S v) q := by
    unfold GfP MA.Gq
    rw [cutTr_Gf_gq (T v).base q.2.1 hζ, ← hTT]
  have hJ0 : J (B.gq (T v).base q.1) = 0 := h _ (hGq ▸ hq)
  unfold trJ MA.toSm MA.evQ
  split_ifs with hs
  · have h0 : B.hsVec (0 : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) = 0 := by
      have := hsVec_smul (0 : ℂ) (0 : Wq (S.pl v) →L[ℂ] Wp (S.pl v))
      simpa using this
    simp [hJ0, h0]
  · rfl

def Lt (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Bg : ℝ) (Θ : OpT S v) : Prop :=
  B.opOrder Θ = 0 ∧ CutCoef S T v Θ 0 Bg

def Good (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Bg Dh Oh : ℝ) (Θ : OpT S v) : Prop :=
  IsAAOp S T v Θ ∧ (Lt S T v Bg Θ ∨ (CutCoef S T v Θ Dh Bg ∧ (B.opOrder Θ : ℝ) ≤ Oh))

def heavy (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Bg : ℝ) (l : List (OpT S v)) : ℕ :=
  l.countP fun Θ => decide (¬ Lt S T v Bg Θ)

theorem heavy_append (Bg : ℝ) (l₁ l₂ : List (OpT S v)) :
    heavy S T v Bg (l₁ ++ l₂) = heavy S T v Bg l₁ + heavy S T v Bg l₂ := by
  unfold heavy; rw [List.countP_append]

theorem heavy_cons (Bg : ℝ) (Θ : OpT S v) (l : List (OpT S v)) :
    heavy S T v Bg (Θ :: l) = heavy S T v Bg l + (if Lt S T v Bg Θ then 0 else 1) := by
  unfold heavy
  rw [List.countP_cons]
  by_cases h : Lt S T v Bg Θ <;> simp [h]

def Rz (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (Bg Dh Oh : ℝ) (k : ℕ)
    (y : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) : Prop :=
  ∃ ts : List (ℂ × List (OpT S v)), (∀ t ∈ ts, (∀ Θ ∈ t.2, Good S T v Bg Dh Oh Θ) ∧ heavy S T v Bg t.2 ≤ k) ∧
    ∀ J ∈ smoothFormsPositiveCone S T v, MA.actA (D.parOf S v) y (trJ S T v e J) =
      (ts.map fun t => t.1 • trJ S T v e (applyL S v t.2 J)).sum

variable {e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {Bg Dh Oh : ℝ}

theorem Rz_mono {k k' : ℕ} (hk : k ≤ k') {y : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))}
    (h : Rz S T v e Bg Dh Oh k y) : Rz S T v e Bg Dh Oh k' y := by
  obtain ⟨ts, h1, h2⟩ := h
  exact ⟨ts, fun t ht => ⟨(h1 t ht).1, le_trans (h1 t ht).2 hk⟩, h2⟩

theorem Rz_one : Rz S T v e Bg Dh Oh 0 1 := by
  refine ⟨[((1 : ℂ), [])], ?_, ?_⟩
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨fun Θ h => absurd h (List.not_mem_nil), by simp [heavy]⟩
  · intro J _
    simp [actA_one, applyL]

theorem Rz_mul (hFF : ∀ Θ : OpT S v, IsAAOp S T v Θ → ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v)
    {k₁ k₂ : ℕ} {x y : MA.A (D.parOf S v) (MA.DQ (D.parOf S v))}
    (hx : Rz S T v e Bg Dh Oh k₁ x) (hy : Rz S T v e Bg Dh Oh k₂ y) : Rz S T v e Bg Dh Oh (k₁ + k₂) (x * y) := by
  obtain ⟨tx, hx1, hx2⟩ := hx
  obtain ⟨ty, hy1, hy2⟩ := hy
  refine ⟨ty.flatMap (fun t' => tx.map (fun t => (t.1 * t'.1, t.2 ++ t'.2))), ?_, ?_⟩
  · intro t ht
    rw [List.mem_flatMap] at ht
    obtain ⟨t', ht', ht2⟩ := ht
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht2
    refine ⟨fun Θ hΘ => ?_, ?_⟩
    · rcases List.mem_append.1 hΘ with h | h
      · exact (hx1 t0 ht0).1 Θ h
      · exact (hy1 t' ht').1 Θ h
    · show heavy S T v Bg (t0.2 ++ t'.2) ≤ k₁ + k₂
      rw [heavy_append]
      exact Nat.add_le_add (hx1 t0 ht0).2 (hy1 t' ht').2
  · intro J hJ
    rw [actA_mul, hy2 J hJ, jd_actA_listsum, list_sum_map_flatMap]
    congr 1
    refine List.map_congr_left fun t' ht' => ?_
    have hJ' : applyL S v t'.2 J ∈ smoothFormsPositiveCone S T v :=
      apply_list_preserves_smooth_forms hFF _ (fun Θ h => ((hy1 t' ht').1 Θ h).1) hJ
    rw [jd_actA_smulR, hx2 _ hJ', List.smul_sum, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp, smul_smul, applyL_append, mul_comm]

variable {L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r}

theorem Rz_closure
    (hFF : ∀ Θ : OpT S v, IsAAOp S T v Θ → ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v)
    (hBddR : ∀ b ∈ MA.bddSet (D.parOf S v) L, ∃ Θ : OpT S v, Good S T v Bg Dh Oh Θ ∧ Lt S T v Bg Θ ∧
      ∀ J ∈ smoothFormsPositiveCone S T v, MA.actA (D.parOf S v) b (trJ S T v e J) = trJ S T v e (B.opApply Θ J)) :
    ∀ b ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L), Rz S T v e Bg Dh Oh 0 b := by
  intro b hb
  induction hb using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨Θ, hG, hLt, hΘ⟩ := hBddR x hx
    refine ⟨[((1 : ℂ), [Θ])], ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      refine ⟨fun Θ' h => ?_, ?_⟩
      · simp only [List.mem_singleton] at h
        subst h
        exact hG
      · show heavy S T v Bg [Θ] ≤ 0
        rw [heavy_cons]
        simp [heavy, hLt]
    · intro J hJ
      rw [hΘ J hJ]
      simp [applyL]
  | one => exact Rz_one
  | mul x y _ _ hx hy => exact Rz_mono (by norm_num) (Rz_mul hFF hx hy)

theorem Rz_hat
    (hFF : ∀ Θ : OpT S v, IsAAOp S T v Θ → ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v)
    (hBddR : ∀ b ∈ MA.bddSet (D.parOf S v) L, ∃ Θ : OpT S v, Good S T v Bg Dh Oh Θ ∧ Lt S T v Bg Θ ∧
      ∀ J ∈ smoothFormsPositiveCone S T v, MA.actA (D.parOf S v) b (trJ S T v e J) = trJ S T v e (B.opApply Θ J))
    (hHatR : ∀ X ∈ MA.hatSet (D.parOf S v) L, ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × OpT S v),
      (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ Good S T v Bg Dh Oh t.2) ∧
      ∀ J ∈ smoothFormsPositiveCone S T v, MA.actA (D.parOf S v) X (trJ S T v e J) =
        (ts.map fun t => MA.actA (D.parOf S v) t.1 (trJ S T v e (B.opApply t.2 J))).sum) :
    ∀ X ∈ MA.hatSet (D.parOf S v) L, Rz S T v e Bg Dh Oh 1 X := by
  intro X hX
  obtain ⟨ts0, h1, h2⟩ := hHatR X hX
  have hb : ∀ t ∈ ts0, Rz S T v e Bg Dh Oh 0 t.1 := fun t ht => Rz_closure hFF hBddR t.1 (h1 t ht).1
  let tsb : MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × OpT S v → List (ℂ × List (OpT S v)) :=
    fun t => if h : t ∈ ts0 then Classical.choose (hb t h) else []
  have hsb : ∀ t ∈ ts0, (∀ s ∈ tsb t, (∀ Θ ∈ s.2, Good S T v Bg Dh Oh Θ) ∧ heavy S T v Bg s.2 ≤ 0) ∧
      ∀ J ∈ smoothFormsPositiveCone S T v, MA.actA (D.parOf S v) t.1 (trJ S T v e J) =
        ((tsb t).map fun s => s.1 • trJ S T v e (applyL S v s.2 J)).sum := by
    intro t ht
    simp only [tsb, dif_pos ht]
    exact Classical.choose_spec (hb t ht)
  refine ⟨ts0.flatMap (fun t => (tsb t).map (fun s => (s.1, s.2 ++ [t.2]))), ?_, ?_⟩
  · intro u hu
    rw [List.mem_flatMap] at hu
    obtain ⟨t, ht, hu2⟩ := hu
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hu2
    refine ⟨fun Θ hΘ => ?_, ?_⟩
    · rcases List.mem_append.1 hΘ with h | h
      · exact ((hsb t ht).1 s hs).1 Θ h
      · simp only [List.mem_singleton] at h
        subst h
        exact (h1 t ht).2
    · show heavy S T v Bg (s.2 ++ [t.2]) ≤ 1
      rw [heavy_append]
      have h3 := ((hsb t ht).1 s hs).2
      have h4 : heavy S T v Bg [t.2] ≤ 1 := by
        rw [heavy_cons]
        split_ifs <;> simp [heavy]
      omega
  · intro J hJ
    rw [h2 J hJ, list_sum_map_flatMap]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    have hJ' : B.opApply t.2 J ∈ smoothFormsPositiveCone S T v := (hFF t.2 (h1 t ht).2.1 J hJ).1
    rw [(hsb t ht).2 _ hJ', List.map_map]
    congr 1
    refine List.map_congr_left fun s _ => ?_
    simp only [Function.comp, applyL_append]
    rfl

theorem Rz_word
    (hFF : ∀ Θ : OpT S v, IsAAOp S T v Θ → ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v)
    (hHat1 : ∀ X ∈ MA.hatSet (D.parOf S v) L, Rz S T v e Bg Dh Oh 1 X) :
    ∀ w : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))), (∀ a ∈ w, a ∈ MA.hatSet (D.parOf S v) L) →
      Rz S T v e Bg Dh Oh w.length w.prod := by
  intro w
  induction w with
  | nil => intro _; simpa using (Rz_one : Rz S T v e Bg Dh Oh 0 1)
  | cons a w ih =>
    intro h
    rw [List.prod_cons, List.length_cons]
    exact Rz_mono (by omega) (Rz_mul hFF (hHat1 a (h a (List.mem_cons_self ..)))
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb)))

structure Ctx (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) where
  Bg : ℝ
  Dh : ℝ
  Oh : ℝ
  Cl : ℝ
  Cgr : ℝ
  hBg : 0 ≤ Bg
  hDh : 0 ≤ Dh
  hOh : 0 ≤ Oh
  hFF : ∀ Θ : OpT S v, IsAAOp S T v Θ → ∀ J ∈ smoothFormsPositiveCone S T v, B.opApply Θ J ∈ smoothFormsPositiveCone S T v ∧ B.opAdj Θ J ∈ smoothFormsPositiveCone S T v
  hOp : ∀ (Θ : OpT S v) (d A : ℝ) (J : GFn S v), 0 ≤ d → IsAAOp S T v Θ → CutCoef S T v Θ d Bg →
    Cl * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
      2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
    LocCC S T v A Bg J → B.opApply Θ J ∈ smoothFormsPositiveCone S T v → LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opApply Θ J)
  hAdj : ∀ (Θ : OpT S v) (d A : ℝ) (J : GFn S v), 0 ≤ d → IsAAOp S T v Θ → CutCoef S T v Θ d Bg →
    Cl * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
      2 * Bg * ((B.opOrder Θ : ℝ) + 1) ≤ A →
    LocCC S T v A Bg J → B.opAdj Θ J ∈ smoothFormsPositiveCone S T v → LocCC S T v (A - d - 2 * Bg * (B.opOrder Θ : ℝ)) Bg (B.opAdj Θ J)
  hMono : ∀ (A A' : ℝ) (J : GFn S v), A' ≤ A → LocCC S T v A Bg J → LocCC S T v A' Bg J
  hGA : ∀ (Θ : OpT S v) (d : ℝ), 0 ≤ d → IsAAOp S T v Θ → CutCoef S T v Θ d Bg →
    ∀ ε : ℝ, 0 < ε → ∀ J₁ J₂ : GFn S v,
      LocCC S T v (B.AB S.G.k S.G.r + Cgr * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
        6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg J₁ →
      LocCC S T v (B.AB S.G.k S.G.r + Cgr * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
        6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * Bg * ((B.opOrder Θ : ℝ) + 5)) Bg J₂ →
      (∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, GfP S T v (B.gq (T v).base x) < ε → J₁ (B.gq (T v).base x) = 0) →
      B.opApply Θ J₁ ∈ smoothFormsPositiveCone S T v → B.opAdj Θ J₂ ∈ smoothFormsPositiveCone S T v →
      MA.ipA (D.parOf S v) (trJ S T v e (B.opApply Θ J₁)) (trJ S T v e J₂) =
        MA.ipA (D.parOf S v) (trJ S T v e J₁) (trJ S T v e (B.opAdj Θ J₂))

namespace Ctx

variable (c : Ctx S T v e)

def Ch : ℝ := c.Dh + 2 * c.Bg * c.Oh

def Top : ℝ := c.Cl * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * c.Oh + c.Dh + 2 * c.Bg * (c.Oh + 1)

def Tga : ℝ := B.AB S.G.k S.G.r + c.Cgr * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
  6 * (S.G.r : ℝ) * (c.Oh + 5) + c.Dh + 2 * c.Bg * (c.Oh + 5)

theorem Ch_nonneg : 0 ≤ c.Ch := by
  unfold Ch; have := c.hBg; have := c.hDh; have := c.hOh; positivity

theorem one_op {Θ : OpT S v} (hΘ : Good S T v c.Bg c.Dh c.Oh Θ) :
    ∃ d : ℝ, 0 ≤ d ∧ CutCoef S T v Θ d c.Bg ∧
      c.Cl * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d +
        2 * c.Bg * ((B.opOrder Θ : ℝ) + 1) ≤ c.Top ∧
      B.AB S.G.k S.G.r + c.Cgr * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 +
        6 * (S.G.r : ℝ) * ((B.opOrder Θ : ℝ) + 5) + d + 2 * c.Bg * ((B.opOrder Θ : ℝ) + 5) ≤ c.Tga ∧
      d + 2 * c.Bg * (B.opOrder Θ : ℝ) ≤ (if Lt S T v c.Bg Θ then 0 else 1) * c.Ch := by
  have hR : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
  have hBg := c.hBg
  have hDh := c.hDh
  have hOh := c.hOh
  by_cases hL : Lt S T v c.Bg Θ
  · refine ⟨0, le_rfl, hL.2, ?_, ?_, ?_⟩
    · rw [hL.1]; unfold Top; push_cast; nlinarith
    · rw [hL.1]; unfold Tga; push_cast; nlinarith
    · rw [if_pos hL, hL.1]; simp
  · rcases hΘ.2 with h | ⟨hc, ho⟩
    · exact absurd h hL
    · refine ⟨c.Dh, hDh, hc, ?_, ?_, ?_⟩
      · unfold Top; nlinarith
      · unfold Tga; nlinarith
      · rw [if_neg hL]; unfold Ch; nlinarith

theorem applyL_loc : ∀ (l : List (OpT S v)), (∀ Θ ∈ l, Good S T v c.Bg c.Dh c.Oh Θ) →
    ∀ (A : ℝ) (J : GFn S v), LocCC S T v A c.Bg J → J ∈ smoothFormsPositiveCone S T v → c.Top ≤ A - heavy S T v c.Bg l * c.Ch →
      LocCC S T v (A - heavy S T v c.Bg l * c.Ch) c.Bg (applyL S v l J) := by
  intro l
  induction l with
  | nil => intro _ A J hJ _ _; simpa [heavy, applyL] using hJ
  | cons Θ l ih =>
    intro hl A J hJ hJF hA
    have hΘ := hl Θ (List.mem_cons_self ..)
    have hl' : ∀ Θ' ∈ l, Good S T v c.Bg c.Dh c.Oh Θ' := fun Θ' h => hl Θ' (List.mem_cons_of_mem _ h)
    have hCh := c.Ch_nonneg
    obtain ⟨d, hd, hc, hT, -, hcost⟩ := c.one_op hΘ
    have hF1 : ∀ A', c.Top ≤ A' - heavy S T v c.Bg l * c.Ch → applyL S v l J ∈ smoothFormsPositiveCone S T v := fun _ _ =>
      apply_list_preserves_smooth_forms c.hFF l (fun Θ' h => (hl' Θ' h).1) hJF
    rw [heavy_cons] at hA ⊢
    by_cases hL : Lt S T v c.Bg Θ
    · simp only [if_pos hL, add_zero, zero_mul] at hA hcost ⊢
      have h1 := ih hl' A J hJ hJF hA
      have h2 := c.hOp Θ d _ _ hd hΘ.1 hc (le_trans hT hA) h1 (c.hFF Θ hΘ.1 _ (hF1 A hA)).1
      exact c.hMono _ _ _ (by linarith) h2
    · simp only [if_neg hL, one_mul, Nat.cast_add, Nat.cast_one] at hA hcost ⊢
      have e1 : ((heavy S T v c.Bg l : ℝ) + 1) * c.Ch = (heavy S T v c.Bg l : ℝ) * c.Ch + c.Ch := by ring
      rw [e1] at hA ⊢
      have hA' : c.Top ≤ A - heavy S T v c.Bg l * c.Ch := by linarith
      have h1 := ih hl' A J hJ hJF hA'
      have h2 := c.hOp Θ d _ _ hd hΘ.1 hc (le_trans hT hA') h1 (c.hFF Θ hΘ.1 _ (hF1 A hA')).1
      exact c.hMono _ _ _ (by linarith) h2

theorem adjL_loc : ∀ (l : List (OpT S v)), (∀ Θ ∈ l, Good S T v c.Bg c.Dh c.Oh Θ) →
    ∀ (A : ℝ) (J : GFn S v), LocCC S T v A c.Bg J → J ∈ smoothFormsPositiveCone S T v → c.Top ≤ A - heavy S T v c.Bg l * c.Ch →
      LocCC S T v (A - heavy S T v c.Bg l * c.Ch) c.Bg (adjL S v l J) := by
  intro l
  induction l with
  | nil => intro _ A J hJ _ _; simpa [heavy, adjL] using hJ
  | cons Θ l ih =>
    intro hl A J hJ hJF hA
    have hΘ := hl Θ (List.mem_cons_self ..)
    have hl' : ∀ Θ' ∈ l, Good S T v c.Bg c.Dh c.Oh Θ' := fun Θ' h => hl Θ' (List.mem_cons_of_mem _ h)
    have hCh := c.Ch_nonneg
    have hh0 : (0 : ℝ) ≤ heavy S T v c.Bg l := Nat.cast_nonneg _
    have hhC : 0 ≤ (heavy S T v c.Bg l : ℝ) * c.Ch := mul_nonneg hh0 hCh
    obtain ⟨d, hd, hc, hT, -, hcost⟩ := c.one_op hΘ
    have hF2 : B.opAdj Θ J ∈ smoothFormsPositiveCone S T v := (c.hFF Θ hΘ.1 J hJF).2
    rw [heavy_cons] at hA ⊢
    rw [adjL_cons]
    by_cases hL : Lt S T v c.Bg Θ
    · simp only [if_pos hL, add_zero, zero_mul] at hA hcost ⊢
      have hAT : c.Top ≤ A := by linarith
      have h1 := c.hAdj Θ d A J hd hΘ.1 hc (le_trans hT hAT) hJ hF2
      have h1' : LocCC S T v A c.Bg (B.opAdj Θ J) := c.hMono _ _ _ (by linarith) h1
      exact ih hl' A _ h1' hF2 hA
    · simp only [if_neg hL, one_mul, Nat.cast_add, Nat.cast_one] at hA hcost ⊢
      have e1 : ((heavy S T v c.Bg l : ℝ) + 1) * c.Ch = (heavy S T v c.Bg l : ℝ) * c.Ch + c.Ch := by ring
      rw [e1] at hA ⊢
      have hAT : c.Top ≤ A := by linarith
      have h1 := c.hAdj Θ d A J hd hΘ.1 hc (le_trans hT hAT) hJ hF2
      have h1' : LocCC S T v (A - c.Ch) c.Bg (B.opAdj Θ J) := c.hMono _ _ _ (by linarith) h1
      have h2 := ih hl' (A - c.Ch) _ h1' hF2 (by linarith)
      exact c.hMono _ _ _ (by linarith) h2

theorem chain {ε : ℝ} (hε : 0 < ε) : ∀ (l : List (OpT S v)), (∀ Θ ∈ l, Good S T v c.Bg c.Dh c.Oh Θ) →
    ∀ (A₁ A₂ : ℝ) (K J₂ : GFn S v), LocCC S T v A₁ c.Bg K → K ∈ smoothFormsPositiveCone S T v → Van S T v ε K →
      LocCC S T v A₂ c.Bg J₂ → J₂ ∈ smoothFormsPositiveCone S T v →
      c.Top ≤ A₁ - heavy S T v c.Bg l * c.Ch → c.Tga ≤ A₁ - heavy S T v c.Bg l * c.Ch →
      c.Top ≤ A₂ - heavy S T v c.Bg l * c.Ch → c.Tga ≤ A₂ - heavy S T v c.Bg l * c.Ch →
      MA.ipA (D.parOf S v) (trJ S T v e (applyL S v l K)) (trJ S T v e J₂) =
        MA.ipA (D.parOf S v) (trJ S T v e K) (trJ S T v e (adjL S v l J₂)) := by
  intro l
  induction l with
  | nil => intros; rfl
  | cons Θ l ih =>
    intro hl A₁ A₂ K J₂ hK hKF hKv hJ hJF h1T h1G h2T h2G
    have hΘ := hl Θ (List.mem_cons_self ..)
    have hl' : ∀ Θ' ∈ l, Good S T v c.Bg c.Dh c.Oh Θ' := fun Θ' h => hl Θ' (List.mem_cons_of_mem _ h)
    have hCh := c.Ch_nonneg
    have hh0 : (0 : ℝ) ≤ heavy S T v c.Bg l := Nat.cast_nonneg _
    have hhC : 0 ≤ (heavy S T v c.Bg l : ℝ) * c.Ch := mul_nonneg hh0 hCh
    obtain ⟨d, hd, hc, hT, hG, hcost⟩ := c.one_op hΘ
    have hF1 : applyL S v l K ∈ smoothFormsPositiveCone S T v := apply_list_preserves_smooth_forms c.hFF l (fun Θ' h => (hl' Θ' h).1) hKF
    have hv1 : Van S T v ε (applyL S v l K) := van_applyL l hKv
    have hF2 : B.opAdj Θ J₂ ∈ smoothFormsPositiveCone S T v := (c.hFF Θ hΘ.1 J₂ hJF).2
    rw [heavy_cons] at h1T h1G h2T h2G
    show MA.ipA (D.parOf S v) (trJ S T v e (B.opApply Θ (applyL S v l K))) (trJ S T v e J₂) =
      MA.ipA (D.parOf S v) (trJ S T v e K) (trJ S T v e (adjL S v l (B.opAdj Θ J₂)))
    by_cases hL : Lt S T v c.Bg Θ
    · simp only [if_pos hL, add_zero, zero_mul] at h1T h1G h2T h2G hcost
      have hL1 := c.applyL_loc l hl' A₁ K hK hKF h1T
      have hstep := c.hGA Θ d hd hΘ.1 hc ε hε (applyL S v l K) J₂ (c.hMono _ _ _ (le_trans hG h1G) hL1)
        (c.hMono _ _ _ (by linarith) hJ) (fun x _ hx => hv1 _ hx) (c.hFF Θ hΘ.1 _ hF1).1 hF2
      rw [hstep]
      have h2 := c.hAdj Θ d A₂ J₂ hd hΘ.1 hc (le_trans hT (by linarith)) hJ hF2
      exact ih hl' A₁ A₂ K _ hK hKF hKv (c.hMono _ _ _ (by linarith) h2) hF2 h1T h1G h2T h2G
    · simp only [if_neg hL, one_mul, Nat.cast_add, Nat.cast_one] at h1T h1G h2T h2G hcost
      have e1 : ((heavy S T v c.Bg l : ℝ) + 1) * c.Ch = (heavy S T v c.Bg l : ℝ) * c.Ch + c.Ch := by ring
      rw [e1] at h1T h1G h2T h2G
      have hL1 := c.applyL_loc l hl' A₁ K hK hKF (by linarith)
      have hstep := c.hGA Θ d hd hΘ.1 hc ε hε (applyL S v l K) J₂ (c.hMono _ _ _ (by linarith) hL1)
        (c.hMono _ _ _ (by linarith) hJ) (fun x _ hx => hv1 _ hx) (c.hFF Θ hΘ.1 _ hF1).1 hF2
      rw [hstep]
      have h2 := c.hAdj Θ d A₂ J₂ hd hΘ.1 hc (le_trans hT (by linarith)) hJ hF2
      exact ih hl' A₁ (A₂ - c.Ch) K _ hK hKF hKv (c.hMono _ _ _ (by linarith) h2) hF2 (by linarith) (by linarith)
        (by linarith) (by linarith)

end Ctx

theorem cutCoef_of_glob {Θ : OpT S v} {d Bg : ℝ} (hΘ : GlobCoef Θ d) (hBg : 0 ≤ Bg) : CutCoef S T v Θ d Bg := by
  intro Tm hTm ε _ m
  obtain ⟨-, -, h⟩ := hΘ Tm hTm
  obtain ⟨Cb, hCb⟩ := h m
  refine ⟨max Cb 0, fun u w hu hw hl g hg _ => ?_⟩
  have hg1 : 1 ≤ B.gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hpow : B.gN g ^ d ≤ B.gN g ^ (d + Bg * m) :=
    Real.rpow_le_rpow_of_exponent_le hg1 (by nlinarith)
  have hp0 : 0 ≤ B.gN g ^ d := Real.rpow_nonneg (by linarith) _
  obtain ⟨h1, h2⟩ := hCb u w hu hw hl g hg
  constructor
  · calc _ ≤ Cb * B.gN g ^ d := h1
      _ ≤ max Cb 0 * B.gN g ^ d := mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
      _ ≤ max Cb 0 * B.gN g ^ (d + Bg * m) := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
  · calc _ ≤ Cb * B.gN g ^ d := h2
      _ ≤ max Cb 0 * B.gN g ^ d := mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
      _ ≤ max Cb 0 * B.gN g ^ (d + Bg * m) := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)

theorem cutCoef_mono {Θ : OpT S v} {d Bg Bg' : ℝ} (hB : Bg ≤ Bg') (hΘ : CutCoef S T v Θ d Bg) :
    CutCoef S T v Θ d Bg' := by
  intro Tm hTm ε hε m
  obtain ⟨C, hC⟩ := hΘ Tm hTm ε hε m
  refine ⟨max C 0, fun u w hu hw hl g hg hGg => ?_⟩
  have hg1 : 1 ≤ B.gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hpow : B.gN g ^ (d + Bg * m) ≤ B.gN g ^ (d + Bg' * m) :=
    Real.rpow_le_rpow_of_exponent_le hg1 (by nlinarith)
  have hp0 : 0 ≤ B.gN g ^ (d + Bg * m) := Real.rpow_nonneg (by linarith) _
  obtain ⟨h1, h2⟩ := hC u w hu hw hl g hg hGg
  constructor
  · calc _ ≤ C * B.gN g ^ (d + Bg * m) := h1
      _ ≤ max C 0 * B.gN g ^ (d + Bg * m) := mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
      _ ≤ max C 0 * B.gN g ^ (d + Bg' * m) := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
  · calc _ ≤ C * B.gN g ^ (d + Bg * m) := h2
      _ ≤ max C 0 * B.gN g ^ (d + Bg * m) := mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
      _ ≤ max C 0 * B.gN g ^ (d + Bg' * m) := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)

end place

theorem mulφ_sum {P : M.Par} {ι : Type} (p : MA.SmQ P.r P.TT) (l : List ι) (c : ι → ℂ)
    (U : ι → M.Ty P → MA.SmQ P.r P.TT) :
    (fun π => p * ((l.map fun i => c i • U i).sum) π) = (l.map fun i => c i • fun π => p * U i π).sum := by
  induction l with
  | nil => funext π; simp
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    funext π
    simp only [Pi.add_apply, Pi.smul_apply, mul_add, mul_smul_comm]

theorem builtOW_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {C₁ C₂ : ℝ} (h : C₁ ≤ C₂) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ}
    {A₀ : ℝ} (hB : BuiltOW C₂ S T f χ ν' m₀ top A₀) : BuiltOW C₁ S T f χ ν' m₀ top A₀ :=
  ⟨isBuiltPlace_mono h hB.1, hB.2⟩

theorem weight_budget_linear_inequality (A K x a b : ℝ) (hx : 0 ≤ x) (hab : a + b ≤ K) : A - K * x ≤ A - a * x - b * x := by nlinarith

theorem quadratic_assembly_holds : JAAssembleQQ := by
  intro hHat _ _ _ _ _ hBdd _ _ hPhi hStar hGrp hLoc hFFs
  obtain ⟨Cj, hCj, hHat⟩ := hHat
  obtain ⟨Cb1, Cb, hCb, hBdd⟩ := hBdd
  obtain ⟨Cp, hPhi⟩ := hPhi
  obtain ⟨Cs, hStar⟩ := hStar
  obtain ⟨Cgr, Cg1, hCg1, hGrp⟩ := hGrp
  obtain ⟨Cl, Cg2, hCg2, hLoc⟩ := hLoc
  obtain ⟨Cf, hFFs⟩ := hFFs
  set Sg : ℝ := Cg1 + Cg2 + Cb with hSg
  set Kb : ℝ := 200 * (1 + |Cl| + |Cgr|) * (1 + Cj) * (1 + Sg) with hKb
  set Cbig : ℝ := max (max (max Cj Cb1) (max Cp Cs)) (max (max Cgr Cl) (max Cf Kb)) with hCbig
  refine ⟨Cbig, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL hJf
  have hSg0 : 0 ≤ Sg := by positivity
  have hR0 : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
  have hR1 : (0 : ℝ) ≤ (S.G.r : ℝ) + 1 := by linarith

  have hHatP := hHat E Wp Wq S T f χ ν' m₀ top A₀ (builtOW_mono (by simp [hCbig]) hB) v e L hFr hGa hQQ hL
  have hBddP := hBdd E Wp Wq S T f χ ν' m₀ top A₀ (builtOW_mono (by simp [hCbig]) hB) v e L hFr hGa hQQ hL
  have hPhiP := hPhi E Wp Wq S T f χ ν' m₀ top A₀ (builtOW_mono (by simp [hCbig]) hB) v e hFr
  have hStarP := hStar E Wp Wq S T f χ ν' m₀ top A₀ (builtOW_mono (by simp [hCbig]) hB) v e L hFr hGa hL
  have hGrpP := hGrp E Wp Wq S T f χ ν' m₀ top A₀ (builtOW_mono (by simp [hCbig]) hB) v e hFr
  obtain ⟨hLbase, hLop, hLadj, hLphi, -, -, hLmono, hLL2⟩ :=
    hLoc E Wp Wq S T f χ ν' m₀ top A₀ (builtOW_mono (by simp [hCbig]) hB) v
  have hFFP := hFFs E Wp Wq S T f χ ν' m₀ top A₀ (builtOW_mono (by simp [hCbig]) hB) v

  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hInCC : ∀ m : ℕ, B.InCC A₀ m (f v) := (hB.1.2.2.2.1.2 v).2.2.2.2.1
  have hCk : B.CkOn ⊤ (B.GV S.G.k S.G.r) (f v) := hB.1.2.2.2.2.2.2.2.2.2.1 v
  have hBud := hB.1.2.2.2.2.2.2.2.2.2.2.2.1

  set R : ℝ := (S.G.r : ℝ) with hR
  set n : ℝ := nDim S.G.k S.G.r with hn
  set N : ℝ := (S.Ntop : ℝ) with hN
  have hn1 : 1 ≤ n := by rw [hn]; unfold nDim; push_cast; linarith [(Nat.cast_nonneg S.G.k : (0:ℝ) ≤ S.G.k)]
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set Bg : ℝ := Sg * (R + 1) with hBg
  have hBg0 : 0 ≤ Bg := by positivity
  have hCg1B : Cg1 * (R + 1) ≤ Bg := mul_le_mul_of_nonneg_right (by linarith) hR1
  have hCg2B : Cg2 * (R + 1) ≤ Bg := mul_le_mul_of_nonneg_right (by linarith) hR1
  have hCbB : Cb * (R + 1) ≤ Bg := mul_le_mul_of_nonneg_right (by linarith) hR1
  obtain ⟨c, hcB, hcD, hcO, hcL, hcG⟩ : ∃ c : Ctx S T v e, c.Bg = Bg ∧ c.Dh = Cj * (R + 1) * n ∧ c.Oh = Cj * n ∧
      c.Cl = Cl ∧ c.Cgr = Cgr := ⟨
    { Bg := Bg, Dh := Cj * (R + 1) * n, Oh := Cj * n, Cl := Cl, Cgr := Cgr
      hBg := hBg0
      hDh := by positivity
      hOh := by positivity
      hFF := hFFP
      hOp := fun Θ d A J hd hΘ hc hT hJ hF => hLop Θ d Bg A J hd hCg2B hΘ hc hT hJ hF
      hAdj := fun Θ d A J hd hΘ hc hT hJ hF => hLadj Θ d Bg A J hd hCg2B hΘ hc hT hJ hF
      hMono := fun A A' J h hJ => hLmono Bg A A' J h hJ
      hGA := fun Θ d hd hΘ hc ε hε J₁ J₂ h1 h2 hv hF1 hF2 => hGrpP Θ d Bg hd hCg1B hΘ hc ε hε J₁ J₂ h1 h2 hv hF1 hF2 },
    rfl, rfl, rfl, rfl, rfl⟩

  have hBddR : ∀ b ∈ MA.bddSet (D.parOf S v) L, ∃ Θ : OpT S v, Good S T v c.Bg c.Dh c.Oh Θ ∧ Lt S T v c.Bg Θ ∧
      ∀ J ∈ smoothFormsPositiveCone S T v, MA.actA (D.parOf S v) b (trJ S T v e J) = trJ S T v e (B.opApply Θ J) := by
    intro b hb
    obtain ⟨Θ, h0, hA, hc, hJ⟩ := hBddP b hb
    have hc' : CutCoef S T v Θ 0 c.Bg := by rw [hcB]; exact cutCoef_mono hCbB hc
    exact ⟨Θ, ⟨hA, Or.inl ⟨h0, hc'⟩⟩, ⟨h0, hc'⟩, fun J hJF => (hJ J hJF).2.2⟩
  have hHatR : ∀ X ∈ MA.hatSet (D.parOf S v) L, ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × OpT S v),
      (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ Good S T v c.Bg c.Dh c.Oh t.2) ∧
      ∀ J ∈ smoothFormsPositiveCone S T v, MA.actA (D.parOf S v) X (trJ S T v e J) =
        (ts.map fun t => MA.actA (D.parOf S v) t.1 (trJ S T v e (B.opApply t.2 J))).sum := by
    intro X hX
    obtain ⟨ts, h1, h2⟩ := hHatP X hX
    refine ⟨ts, fun t ht => ?_, h2⟩
    obtain ⟨hb, hs, hcm, hg, ho⟩ := h1 t ht
    refine ⟨hb, ⟨hs, hcm⟩, Or.inr ⟨?_, ?_⟩⟩
    · rw [hcD, hcB]; exact cutCoef_of_glob hg hBg0
    · rw [hcO]; exact ho
  have hHat1 := Rz_hat c.hFF hBddR hHatR

  intro φ ε hε hφ h0 hld b hb X hX vw w hlen ha
  have hJfF : B.JF (T v).base (f v) ∈ smoothFormsPositiveCone S T v := hJf
  obtain ⟨tsU, hU1, hU2⟩ := Rz_mul c.hFF (Rz_closure c.hFF hBddR b hb)
    (Rz_word c.hFF hHat1 vw (fun a h => ha a (List.mem_append_left _ h)))
  obtain ⟨tsW, hW1, hW2⟩ := Rz_word c.hFF hHat1 w (fun a h => ha a (List.mem_append_right _ h))
  obtain ⟨tsX, hX1, hX2⟩ := hHat1 X hX

  have hAB : B.AB S.G.k S.G.r ≤ 2 * n * (R + 1) + 1 := by
    unfold B.AB
    rw [hn, hR]; unfold nDim; push_cast
    have hk : (0 : ℝ) ≤ S.G.k := Nat.cast_nonneg _
    nlinarith
  have hKbA : Kb * ((R + 1) ^ 4 * (N * n ^ 2 + n ^ 3)) ≤ A₀ := by
    have hW0 : 0 ≤ (R + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by positivity
    have hle : Kb ≤ Cbig := by simp [hCbig]
    calc Kb * ((R + 1) ^ 4 * (N * n ^ 2 + n ^ 3)) ≤ Cbig * ((R + 1) ^ 4 * (N * n ^ 2 + n ^ 3)) :=
          mul_le_mul_of_nonneg_right hle hW0
      _ ≤ A₀ := by
        have e : Cbig * ((R + 1) ^ 4 * (N * n ^ 2 + n ^ 3)) = Cbig * ((S.G.r : ℝ) + 1) ^ 4 *
            ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by
          rw [hn, hR, hN]; unfold nDim; push_cast; ring
        rw [e]; exact hBud
  obtain ⟨hTop, hTga, hL2⟩ := ja_arith Cj Cl Cgr Sg R n N A₀ (B.AB S.G.k S.G.r) hCj hSg0 hR0 hn1 hN0 hAB hKbA
  have hCh := c.Ch_nonneg
  have hChE : c.Ch = Cj * (R + 1) * n + 2 * (Sg * (R + 1)) * (Cj * n) := by unfold Ctx.Ch; rw [hcD, hcB, hcO]
  have hTop' : c.Top ≤ A₀ - (2 * N + 2) * c.Ch := by unfold Ctx.Top; rw [hChE, hcL, hcO, hcD, hcB]; exact hTop
  have hTga' : c.Tga ≤ A₀ - (2 * N + 2) * c.Ch := by unfold Ctx.Tga; rw [hChE, hcG, hcO, hcD, hcB]; exact hTga
  have hL2' : Cl * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r + 5 * c.Bg ≤ A₀ - (2 * N + 2) * c.Ch := by
    rw [hChE, hcB]; exact hL2
  have hlenR : (vw.length : ℝ) + w.length + 1 ≤ 2 * N + 2 := by
    have := hlen; rw [hN]; exact_mod_cast this
  have hbud : ∀ a b' : ℕ, (a : ℝ) + b' ≤ 2 * N + 2 → A₀ - (2 * N + 2) * c.Ch ≤ A₀ - a * c.Ch - b' * c.Ch :=
    fun a b' hab => weight_budget_linear_inequality A₀ (2 * N + 2) c.Ch a b' hCh hab

  have hJfL : LocCC S T v A₀ c.Bg (B.JF (T v).base (f v)) := by rw [hcB]; exact hLbase (f v) A₀ Bg hCk hInCC hJfF hBg0
  have hLt : ∀ t ∈ tsU, LocCC S T v (A₀ - heavy S T v c.Bg t.2 * c.Ch) c.Bg (applyL S v t.2 (B.JF (T v).base (f v))) ∧
      applyL S v t.2 (B.JF (T v).base (f v)) ∈ smoothFormsPositiveCone S T v := by
    intro t ht
    have hh : (heavy S T v c.Bg t.2 : ℝ) ≤ vw.length := by exact_mod_cast (by simpa using (hU1 t ht).2)
    refine ⟨c.applyL_loc t.2 (hU1 t ht).1 A₀ _ hJfL hJfF ?_, apply_list_preserves_smooth_forms c.hFF _ (fun Θ h => ((hU1 t ht).1 Θ h).1) hJfF⟩
    have := hbud (heavy S T v c.Bg t.2) 0 (by push_cast; linarith)
    push_cast at this; linarith

  have hWs : ∀ s ∈ tsW, LocCC S T v (A₀ - heavy S T v c.Bg s.2 * c.Ch) c.Bg (applyL S v s.2 (B.JF (T v).base (f v))) ∧
      applyL S v s.2 (B.JF (T v).base (f v)) ∈ smoothFormsPositiveCone S T v := by
    intro s hs
    have hh : (heavy S T v c.Bg s.2 : ℝ) ≤ w.length := by exact_mod_cast (hW1 s hs).2
    refine ⟨c.applyL_loc s.2 (hW1 s hs).1 A₀ _ hJfL hJfF ?_, apply_list_preserves_smooth_forms c.hFF _ (fun Θ h => ((hW1 s hs).1 Θ h).1) hJfF⟩
    have := hbud (heavy S T v c.Bg s.2) 0 (by push_cast; linarith)
    push_cast at this; linarith
  have hKt : ∀ t ∈ tsU, LocCC S T v (A₀ - heavy S T v c.Bg t.2 * c.Ch) c.Bg
        (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))) ∧
      mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v))) ∈ smoothFormsPositiveCone S T v ∧
      Van S T v ε (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))) := by
    intro t ht
    obtain ⟨h1, h2⟩ := hLt t ht
    have hF := (hPhiP φ hφ _ h2).1
    refine ⟨?_, hF, van_mulG h0 _⟩
    rw [hcB] at h1 ⊢
    exact hLphi φ Bg _ _ hφ hld hCg2B h1 hF
  have hL2c : ∀ (A : ℝ) (J : GFn S v), A₀ - (2 * N + 2) * c.Ch ≤ A → LocCC S T v A c.Bg J →
      ∀ π, IntegrableOn (fun q => ‖MA.evQ (D.parOf S v) (trJ S T v e J π) q‖ ^ 2)
        {q | ε ≤ MA.Gq (D.parOf S v) q} (MA.mu0 (D.parOf S v).r (D.parOf S v).TT) := by
    intro A J hA hJ
    rw [hcB] at hJ hL2'
    exact hLL2 Bg A ε J e hFr hBg0 hε (by linarith) hJ
  have key : ∀ t ∈ tsU, ∀ x ∈ tsX, ∀ s ∈ tsW,
      MA.ipA (D.parOf S v) (trJ S T v e (applyL S v x.2 (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v))))))
          (trJ S T v e (applyL S v s.2 (B.JF (T v).base (f v)))) =
        MA.ipA (D.parOf S v) (trJ S T v e (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))))
          (trJ S T v e (adjL S v x.2 (applyL S v s.2 (B.JF (T v).base (f v))))) ∧
      PI (D.parOf S v) (trJ S T v e (applyL S v x.2 (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v))))))
          (trJ S T v e (applyL S v s.2 (B.JF (T v).base (f v)))) ∧
      PI (D.parOf S v) (trJ S T v e (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))))
          (trJ S T v e (adjL S v x.2 (applyL S v s.2 (B.JF (T v).base (f v))))) := by
    intro t ht x hx s hs
    obtain ⟨hKL, hKF, hKv⟩ := hKt t ht
    obtain ⟨hHL, hHF⟩ := hWs s hs
    have ht' : (heavy S T v c.Bg t.2 : ℝ) ≤ vw.length := by exact_mod_cast (by simpa using (hU1 t ht).2)
    have hx' : (heavy S T v c.Bg x.2 : ℝ) ≤ 1 := by exact_mod_cast (hX1 x hx).2
    have hs' : (heavy S T v c.Bg s.2 : ℝ) ≤ w.length := by exact_mod_cast (hW1 s hs).2
    have b1 := hbud (heavy S T v c.Bg t.2) (heavy S T v c.Bg x.2) (by linarith)
    have b2 := hbud (heavy S T v c.Bg s.2) (heavy S T v c.Bg x.2) (by linarith)
    have b3 : A₀ - (2 * N + 2) * c.Ch ≤ A₀ - heavy S T v c.Bg s.2 * c.Ch := by
      have := hbud (heavy S T v c.Bg s.2) 0 (by push_cast; linarith)
      simpa using this
    have b4 : A₀ - (2 * N + 2) * c.Ch ≤ A₀ - heavy S T v c.Bg t.2 * c.Ch := by
      have := hbud (heavy S T v c.Bg t.2) 0 (by push_cast; linarith)
      simpa using this
    have hA1 := c.applyL_loc x.2 (hX1 x hx).1 _ _ hKL hKF (le_trans hTop' b1)
    have hA2 := c.adjL_loc x.2 (hX1 x hx).1 _ _ hHL hHF (le_trans hTop' b2)
    refine ⟨c.chain hε x.2 (hX1 x hx).1 _ _ _ _ hKL hKF hKv hHL hHF (le_trans hTop' b1) (le_trans hTga' b1)
      (le_trans hTop' b2) (le_trans hTga' b2), ?_, ?_⟩
    · exact pairing_integrable_of_square_integrable (trJ_van e hTT (van_applyL x.2 hKv)) (hL2c _ _ b1 hA1) (hL2c _ _ b3 hHL)
    · exact pairing_integrable_of_square_integrable (trJ_van e hTT hKv) (hL2c _ _ b4 hKL) (hL2c _ _ b2 hA2)

  have hStarX : ∀ J ∈ smoothFormsPositiveCone S T v, MA.actA (D.parOf S v) (star X) (trJ S T v e J) =
      (tsX.map fun x => (starRingEnd ℂ x.1) • trJ S T v e (adjL S v x.2 J)).sum :=
    hStarP X (Submonoid.subset_closure (Set.mem_union_left _ hX)) tsX (fun x hx Θ hΘ => ((hX1 x hx).1 Θ hΘ).1)
      (fun J hJ => ⟨fun x hx => ⟨apply_list_preserves_smooth_forms c.hFF _ (fun Θ h => ((hX1 x hx).1 Θ h).1) hJ,
        adjoint_list_preserves_smooth_forms c.hFF _ (fun Θ h => ((hX1 x hx).1 Θ h).1) hJ⟩, hX2 J hJ⟩)
  have hu : (fun π => MA.toSm (D.parOf S v) (fun q => (φ (MA.Gq (D.parOf S v) q) : ℂ)) *
        MA.actA (D.parOf S v) (b * vw.prod) (trJ S T v e (B.JF (T v).base (f v))) π) =
      (tsU.map fun t => t.1 • trJ S T v e (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v))))).sum := by
    rw [hU2 _ hJfF, mulφ_sum]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    congr 1
    exact ((hPhiP φ hφ _ (hLt t ht).2).2).symm
  have hwj := hW2 _ hJfF
  rw [hu, actA_mul, hwj, jd_actA_listsum (D.parOf S v) X, jd_actA_listsum (D.parOf S v) (star X)]
  have e1 : (tsU.map fun t => MA.actA (D.parOf S v) X
        (t.1 • trJ S T v e (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))))) =
      tsU.map fun t => t.1 • (tsX.map fun x =>
        x.1 • trJ S T v e (applyL S v x.2 (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))))).sum :=
    List.map_congr_left fun t ht => by rw [jd_actA_smulR, hX2 _ (hKt t ht).2.1]
  have e2 : (tsW.map fun s => MA.actA (D.parOf S v) (star X) (s.1 • trJ S T v e (applyL S v s.2 (B.JF (T v).base (f v))))) =
      tsW.map fun s => s.1 • (tsX.map fun x =>
        (starRingEnd ℂ x.1) • trJ S T v e (adjL S v x.2 (applyL S v s.2 (B.JF (T v).base (f v))))).sum :=
    List.map_congr_left fun s hs => by rw [jd_actA_smulR, hStarX _ (hWs s hs).2]
  rw [e1, e2]

  have hPIA : ∀ t ∈ tsU, ∀ x ∈ tsX, PI (D.parOf S v)
      (trJ S T v e (applyL S v x.2 (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v))))))
      ((tsW.map fun s => s.1 • trJ S T v e (applyL S v s.2 (B.JF (T v).base (f v)))).sum) :=
    fun t ht x hx => (ipA_sum_right _ tsW (fun s => s.1) _ (fun s hs => (key t ht x hx s hs).2.1)).2
  have hPIU : ∀ t ∈ tsU, PI (D.parOf S v)
      ((tsX.map fun x => x.1 • trJ S T v e (applyL S v x.2 (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))))).sum)
      ((tsW.map fun s => s.1 • trJ S T v e (applyL S v s.2 (B.JF (T v).base (f v)))).sum) :=
    fun t ht => (ipA_sum_left tsX (fun x => x.1) _ _ (hPIA t ht)).2
  have hPIB : ∀ t ∈ tsU, ∀ s ∈ tsW, PI (D.parOf S v)
      (trJ S T v e (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))))
      ((tsX.map fun x => (starRingEnd ℂ x.1) • trJ S T v e (adjL S v x.2 (applyL S v s.2 (B.JF (T v).base (f v))))).sum) :=
    fun t ht s hs => (ipA_sum_right _ tsX (fun x => starRingEnd ℂ x.1) _ (fun x hx => (key t ht x hx s hs).2.2)).2
  have hPIR : ∀ t ∈ tsU, PI (D.parOf S v)
      (trJ S T v e (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))))
      ((tsW.map fun s => s.1 • (tsX.map fun x =>
        (starRingEnd ℂ x.1) • trJ S T v e (adjL S v x.2 (applyL S v s.2 (B.JF (T v).base (f v))))).sum).sum) :=
    fun t ht => (ipA_sum_right _ tsW (fun s => s.1) _ (hPIB t ht)).2
  refine ((ipA_sum_left tsU (fun t => t.1) _ _ hPIU).1).trans (Eq.trans ?_ ((ipA_sum_left tsU (fun t => t.1) _ _ hPIR).1).symm)
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  refine congrArg (fun z => t.1 * z) ?_
  refine ((ipA_sum_left tsX (fun x => x.1) _ _ (hPIA t ht)).1).trans
    (Eq.trans ?_ ((ipA_sum_right _ tsW (fun s => s.1) _ (hPIB t ht)).1).symm)
  have hin : ∀ x ∈ tsX, MA.ipA (D.parOf S v)
      (trJ S T v e (applyL S v x.2 (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v))))))
      ((tsW.map fun s => s.1 • trJ S T v e (applyL S v s.2 (B.JF (T v).base (f v)))).sum) =
      (tsW.map fun s => starRingEnd ℂ s.1 * MA.ipA (D.parOf S v)
        (trJ S T v e (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))))
        (trJ S T v e (adjL S v x.2 (applyL S v s.2 (B.JF (T v).base (f v)))))).sum := by
    intro x hx
    refine ((ipA_sum_right _ tsW (fun s => s.1) _ (fun s hs => (key t ht x hx s hs).2.1)).1).trans ?_
    exact congrArg List.sum (List.map_congr_left fun s hs =>
      congrArg (fun z => starRingEnd ℂ s.1 * z) (key t ht x hx s hs).1)
  have hin2 : ∀ s ∈ tsW, MA.ipA (D.parOf S v)
      (trJ S T v e (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))))
      ((tsX.map fun x => (starRingEnd ℂ x.1) • trJ S T v e (adjL S v x.2 (applyL S v s.2 (B.JF (T v).base (f v))))).sum) =
      (tsX.map fun x => x.1 * MA.ipA (D.parOf S v)
        (trJ S T v e (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))))
        (trJ S T v e (adjL S v x.2 (applyL S v s.2 (B.JF (T v).base (f v)))))).sum := by
    intro s hs
    refine ((ipA_sum_right _ tsX (fun x => starRingEnd ℂ x.1) _ (fun x hx => (key t ht x hx s hs).2.2)).1).trans ?_
    exact congrArg List.sum (List.map_congr_left fun x _ =>
      congrArg (fun z => z * _) (Complex.conj_conj x.1))
  have hL1 : (tsX.map fun x => x.1 * MA.ipA (D.parOf S v)
        (trJ S T v e (applyL S v x.2 (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v))))))
        ((tsW.map fun s => s.1 • trJ S T v e (applyL S v s.2 (B.JF (T v).base (f v)))).sum)) =
      tsX.map fun x => x.1 * (tsW.map fun s => starRingEnd ℂ s.1 * MA.ipA (D.parOf S v)
        (trJ S T v e (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))))
        (trJ S T v e (adjL S v x.2 (applyL S v s.2 (B.JF (T v).base (f v)))))).sum :=
    List.map_congr_left fun x hx => congrArg (fun z => x.1 * z) (hin x hx)
  have hR1 : (tsW.map fun s => starRingEnd ℂ s.1 * MA.ipA (D.parOf S v)
        (trJ S T v e (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))))
        ((tsX.map fun x => (starRingEnd ℂ x.1) • trJ S T v e (adjL S v x.2 (applyL S v s.2 (B.JF (T v).base (f v))))).sum)) =
      tsW.map fun s => starRingEnd ℂ s.1 * (tsX.map fun x => x.1 * MA.ipA (D.parOf S v)
        (trJ S T v e (mulG S T v φ (applyL S v t.2 (B.JF (T v).base (f v)))))
        (trJ S T v e (adjL S v x.2 (applyL S v s.2 (B.JF (T v).base (f v)))))).sum :=
    List.map_congr_left fun s hs => congrArg (fun z => starRingEnd ℂ s.1 * z) (hin2 s hs)
  refine (congrArg List.sum hL1).trans (Eq.trans ?_ (congrArg List.sum hR1).symm)
  simp only [list_mul_sum]
  rw [list_sum_comm]
  refine congrArg List.sum (List.map_congr_left fun s _ => congrArg List.sum (List.map_congr_left fun x _ => ?_))
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.JA
