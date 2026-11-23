import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzLocallyConstantSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMatrixLeftFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnimodularCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepFunctionIndicatorSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNetIntegralMatricesStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg
open Classical

noncomputable section
namespace GlobalTheory.GJReg
namespace SpanLat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem intM_mul {A B : Matrix (Fin n) (Fin n) k} (hA : A ∈ intM k (Fin n) (Fin n)) (hB : B ∈ intM k (Fin n) (Fin n)) :
    A * B ∈ intM k (Fin n) (Fin n) := fun i j => by
  rw [Matrix.mul_apply]; exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hA i l) (hB l j)

theorem intM_add {A B : Matrix (Fin n) (Fin n) k} (hA : A ∈ intM k (Fin n) (Fin n)) (hB : B ∈ intM k (Fin n) (Fin n)) :
    A + B ∈ intM k (Fin n) (Fin n) := fun i j => Subring.add_mem _ (hA i j) (hB i j)

theorem intM_sub {A B : Matrix (Fin n) (Fin n) k} (hA : A ∈ intM k (Fin n) (Fin n)) (hB : B ∈ intM k (Fin n) (Fin n)) :
    A - B ∈ intM k (Fin n) (Fin n) := fun i j => Subring.sub_mem _ (hA i j) (hB i j)

theorem intM_neg {A : Matrix (Fin n) (Fin n) k} (hA : A ∈ intM k (Fin n) (Fin n)) :
    -A ∈ intM k (Fin n) (Fin n) := fun i j => Subring.neg_mem _ (hA i j)

theorem intM_smul {c : k} (hc : c ∈ 𝒪[k]) {A : Matrix (Fin n) (Fin n) k} (hA : A ∈ intM k (Fin n) (Fin n)) :
    c • A ∈ intM k (Fin n) (Fin n) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact Subring.mul_mem _ hc (hA i j)

theorem intM_one : (1 : Matrix (Fin n) (Fin n) k) ∈ intM k (Fin n) (Fin n) := fun i j => by
  rw [Matrix.one_apply]; split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem KO_intM {u : GL (Fin n) k} (hu : u ∈ KO k (Fin n)) : u.val ∈ intM k (Fin n) (Fin n) :=
  ((mem_KO_iff u).1 hu).1

theorem cancel_right {P Q : Matrix (Fin n) (Fin n) k} (h : GL (Fin n) k) (e : P * h.val = Q * h.val) : P = Q := by
  have := congrArg (· * (h⁻¹).val) e
  simpa only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] using this

theorem orbit {s : k} (hs : s ≠ 0) {X Y A B C D : Matrix (Fin n) (Fin n) k}
    (hA : A ∈ intM k (Fin n) (Fin n)) (hB : B ∈ intM k (Fin n) (Fin n)) (hC : C ∈ intM k (Fin n) (Fin n))
    (hD : D ∈ intM k (Fin n) (Fin n)) (hY : Y = A * X + s • B) (hX : X = C * Y + s • D) :
    ∃ u ∈ KO k (Fin n), ∃ E ∈ intM k (Fin n) (Fin n), Y = u.val * X + s • E := by
  obtain ⟨h, A₀, B₀, C₀, D₀, hA₀, hB₀, hC₀, hD₀, e1, e2, e3⟩ := GlobalTheory.T.integral_matrix_left_factor k n s hs X
  have sB : ∀ P : Matrix (Fin n) (Fin n) k, P * (D₀ * h.val) = s • P := fun P => by
    rw [← e3, Matrix.mul_smul, Matrix.mul_one]
  have r1 : A₀ * C₀ + B₀ * D₀ = 1 := cancel_right h (by
    rw [Matrix.one_mul, Matrix.add_mul, Matrix.mul_assoc, ← e2, Matrix.mul_assoc, sB, ← e1])
  obtain ⟨T, hT, u₁, hu₁, eu₁⟩ := GlobalTheory.T.integral_unimodular_completion k n C₀ D₀ A₀ B₀ hC₀ hD₀ hA₀ hB₀ r1
  have hY' : Y = (A * C₀ + B * D₀) * h.val := by
    rw [hY, Matrix.add_mul, Matrix.mul_assoc, ← e2, Matrix.mul_assoc, sB]
  have r2 : (A₀ * C) * (A * C₀ + B * D₀) + (A₀ * D + B₀) * D₀ = 1 := cancel_right h (by
    rw [Matrix.one_mul, Matrix.add_mul, Matrix.mul_assoc (A₀ * C), ← hY', Matrix.mul_assoc _ D₀, sB]
    rw [e1, hX]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, smul_add]
    abel)
  obtain ⟨T', hT', u₂, hu₂, eu₂⟩ := GlobalTheory.T.integral_unimodular_completion k n _ D₀ (A₀ * C) (A₀ * D + B₀)
    (intM_add (intM_mul hA hC₀) (intM_mul hB hD₀)) hD₀ (intM_mul hA₀ hC) (intM_add (intM_mul hA₀ hD) hB₀) r2
  have f1 : u₁.val * h.val = X + s • T := by
    rw [eu₁, Matrix.add_mul, ← e2, Matrix.mul_assoc, sB]
  have f2 : u₂.val * h.val = Y + s • T' := by
    rw [eu₂, Matrix.add_mul, ← hY', Matrix.mul_assoc, sB]
  have f3 : h.val = (u₁⁻¹).val * (X + s • T) := by
    rw [← f1, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hu : u₂ * u₁⁻¹ ∈ KO k (Fin n) := Subgroup.mul_mem _ hu₂ (Subgroup.inv_mem _ hu₁)
  refine ⟨u₂ * u₁⁻¹, hu, (u₂ * u₁⁻¹).val * T - T', intM_sub (intM_mul (KO_intM hu) hT) hT', ?_⟩
  have e4 : Y = u₂.val * h.val - s • T' := by rw [f2]; abel
  rw [e4, f3]
  simp only [Units.val_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, smul_sub]
  abel

theorem latInd_eq {t s : k} (ht : t ∈ 𝒪[k]) (hs : s ∈ 𝒪[k]) {N : ℕ} {a : Matrix (Fin n) (Fin n) k}
    (ha : t ^ N • a ∈ intM k (Fin n) (Fin n)) {h : GL (Fin n) k} {A B C D : Matrix (Fin n) (Fin n) k}
    (hA : A ∈ intM k (Fin n) (Fin n)) (hB : B ∈ intM k (Fin n) (Fin n)) (hC : C ∈ intM k (Fin n) (Fin n))
    (hD : D ∈ intM k (Fin n) (Fin n)) (e1 : h.val = A * a + s • B) (e2 : a = C * h.val)
    (e3 : s • (1 : Matrix (Fin n) (Fin n) k) = D * h.val) (X : Matrix (Fin n) (Fin n) k) :
    latInd h X = if t ^ N • X ∈ intM k (Fin n) (Fin n) ∧
      ∃ A' B', A' ∈ intM k (Fin n) (Fin n) ∧ B' ∈ intM k (Fin n) (Fin n) ∧ X = A' * a + s • B' then 1 else 0 := by
  have sB : ∀ P : Matrix (Fin n) (Fin n) k, P * (D * h.val) = s • P := fun P => by
    rw [← e3, Matrix.mul_smul, Matrix.mul_one]
  have hX : X = X * (h⁻¹).val * h.val := by
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  unfold latInd
  by_cases hm : X * (h⁻¹ : GL (Fin n) k).val ∈ intM k (Fin n) (Fin n)
  · rw [Set.indicator_of_mem hm, if_pos]
    · rfl
    refine ⟨?_, X * (h⁻¹).val * A, X * (h⁻¹).val * B, intM_mul hm hA, intM_mul hm hB, ?_⟩
    · have hth : t ^ N • h.val ∈ intM k (Fin n) (Fin n) := by
        rw [e1, smul_add, ← Matrix.mul_smul, smul_smul]
        exact intM_add (intM_mul hA ha) (intM_smul (Subring.mul_mem _ (Subring.pow_mem _ ht N) hs) hB)
      rw [hX, ← Matrix.mul_smul]; exact intM_mul hm hth
    · conv_lhs => rw [hX, e1]
      rw [Matrix.mul_add, Matrix.mul_smul]
      simp only [Matrix.mul_assoc]
  · rw [Set.indicator_of_notMem hm, if_neg]
    rintro ⟨_, A', B', hA', hB', eX⟩
    apply hm
    have : X = (A' * C + B' * D) * h.val := by
      rw [eX, Matrix.add_mul, Matrix.mul_assoc, ← e2, Matrix.mul_assoc, sB]
    rw [this, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    exact intM_add (intM_mul hA' hC) (intM_mul hB' hD)

end SpanLat

open SpanLat in

theorem span_latInd_lat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (φ : Matrix (Fin n) (Fin n) k → ℂ), φ ∈ SB (Matrix (Fin n) (Fin n) k) →
    (∀ g ∈ KO k (Fin n), ∀ X, φ (g.val * X) = φ X) →
    ∃ (m : ℕ) (c : Fin m → ℂ) (h : Fin m → GL (Fin n) k), φ = ∑ i, c i • latInd (h i) := by
  intro k _ _ _ _ n φ hφ hK
  obtain ⟨t, ht0, ht1⟩ : ∃ t : k, t ≠ 0 ∧ valuation k t < 1 := Valuation.IsNontrivial.exists_lt_one
  have htO : t ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 ht1.le
  obtain ⟨N, M, hsupp, hper⟩ := GlobalTheory.T.schwartz_locally_constant_support k n t ht0 ht1 φ hφ
  obtain ⟨R, hRB, hRcov⟩ := GlobalTheory.T.finite_net_integral_matrices k n t ht0 ht1 N M
  have hs0 : t ^ M ≠ 0 := pow_ne_zero _ ht0
  have hsO : t ^ M ∈ 𝒪[k] := Subring.pow_mem _ htO M
  let le : Matrix (Fin n) (Fin n) k → Matrix (Fin n) (Fin n) k → Prop := fun X Y =>
    ∃ A B, A ∈ intM k (Fin n) (Fin n) ∧ B ∈ intM k (Fin n) (Fin n) ∧ X = A * Y + t ^ M • B
  have htr : ∀ x y z, le x y → le y z → le x z := by
    rintro x y z ⟨A, B, hA, hB, rfl⟩ ⟨A', B', hA', hB', rfl⟩
    refine ⟨A * A', A * B' + B, intM_mul hA hA', intM_add (intM_mul hA hB') hB, ?_⟩
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, smul_add]
    abel
  let Bs : Set (Matrix (Fin n) (Fin n) k) := {X | t ^ N • X ∈ intM k (Fin n) (Fin n)}
  have hcov : ∀ x ∈ Bs, ∃ y ∈ R, le x y ∧ le y x := fun x hx => by
    obtain ⟨y, hy, E, hE, rfl⟩ := hRcov x hx
    refine ⟨y, hy, ⟨1, E, intM_one, hE, by rw [Matrix.one_mul]⟩, ⟨1, -E, intM_one, intM_neg hE, ?_⟩⟩
    rw [Matrix.one_mul, smul_neg, add_neg_cancel_right]
  have hcls : ∀ x ∈ Bs, ∀ y ∈ Bs, le x y → le y x → φ x = φ y := by
    rintro x - y - ⟨A, B, hA, hB, hxy⟩ ⟨C, D, hC, hD, hyx⟩
    obtain ⟨u, hu, E, hE, e⟩ := orbit hs0 hA hB hC hD hxy hyx
    rw [e, hper _ _ hE, hK u hu]
  obtain ⟨m, c, a, ha, hF⟩ := GlobalTheory.T.step_function_indicator_span _ le htr Bs R φ (fun y hy => hRB y hy) hcov hcls
  have hI : ∀ i, ∃ (h : GL (Fin n) k) (A B C D : Matrix (Fin n) (Fin n) k),
      A ∈ intM k (Fin n) (Fin n) ∧ B ∈ intM k (Fin n) (Fin n) ∧ C ∈ intM k (Fin n) (Fin n) ∧ D ∈ intM k (Fin n) (Fin n) ∧
      h.val = A * a i + t ^ M • B ∧ a i = C * h.val ∧ t ^ M • (1 : Matrix (Fin n) (Fin n) k) = D * h.val :=
    fun i => GlobalTheory.T.integral_matrix_left_factor k n (t ^ M) hs0 (a i)
  choose h A B C D hA hB hC hD e1 e2 e3 using hI
  refine ⟨m, c, h, funext fun X => ?_⟩
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, latInd_eq htO hsO (ha _) (hA _) (hB _) (hC _) (hD _) (e1 _) (e2 _) (e3 _)]
  by_cases hX : X ∈ Bs
  · rw [hF X hX]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact if_congr (and_iff_right (show t ^ N • X ∈ intM k (Fin n) (Fin n) from hX)).symm rfl rfl
  · have : φ X = 0 := by
      by_contra h0; exact hX (hsupp X h0)
    rw [this]
    refine (Finset.sum_eq_zero fun i _ => ?_).symm
    rw [if_neg fun h' => hX h'.1, mul_zero]

end GlobalTheory.GJReg
