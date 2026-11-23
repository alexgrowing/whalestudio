import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFieldIdealsPrincipalStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SzAdjoinRootOfUnity
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SzFieldRangeEmbedding
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCapitulationFieldSizeStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsImagQuadraticHostStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotoneStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SumSizesLeRingPolynomial
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HostXiOrderBoundsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeSupAddStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeWeberRay

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.SmallField

theorem sz_mono {F : IntermediateField ℚ ℂ} {a b a' b' : ℝ} (h : Sz F a b) (ha : a ≤ a') (hb : b ≤ b') :
    Sz F a' b' := GlobalTheory.T.field_size_monotone.1 F a b a' b' h ha hb

theorem sz_cyc (n : ℕ) : Sz ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯ (Real.log n) (Real.log n) := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · have h1 := sz_adjoin_rootOfUnity 1 one_pos
    simp only [Nat.cast_one, div_one, Complex.exp_two_pi_mul_I, Real.log_one] at h1
    simpa only [Nat.cast_zero, div_zero, Complex.exp_zero, Real.log_zero] using h1
  · exact sz_adjoin_rootOfUnity n h

theorem exists_roots (l : List ℕ) (F : IntermediateField ℚ ℂ) (a : ℝ) (h : Sz F a a) :
    ∃ F' : IntermediateField ℚ ℂ, F ≤ F' ∧
      Sz F' (a + (l.map fun N : ℕ => Real.log N).sum) (a + (l.map fun N : ℕ => Real.log N).sum) ∧
      ∀ N ∈ l, Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ F' := by
  induction l with
  | nil => exact ⟨F, le_rfl, by simpa using h, by simp⟩
  | cons n l ih =>
    obtain ⟨F', h1, h2, h3⟩ := ih
    refine ⟨F' ⊔ ℚ⟮Complex.exp (2 * Real.pi * Complex.I / n)⟯, h1.trans le_sup_left, ?_, ?_⟩
    · refine sz_mono (GlobalTheory.T.field_size_sup_add _ _ _ _ _ _ h2 (sz_cyc n)) (le_of_eq ?_) (le_of_eq ?_) <;>
      · simp only [List.map_cons, List.sum_cons]; ring
    · intro N hN
      rcases List.mem_cons.1 hN with rfl | hN
      · exact (le_sup_right : _ ≤ F' ⊔ _) (IntermediateField.mem_adjoin_simple_self ℚ _)
      · exact (le_sup_left : F' ≤ _) (h3 N hN)

theorem weberSet_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : ℕ) : weberSet L n = weberSet L' n := by
  have hG : ∀ k, L.G k = L'.G k := fun k => by unfold PeriodPair.G; rw [h]
  have h2 : L.g₂ = L'.g₂ := by unfold PeriodPair.g₂; rw [hG]
  have h3 : L.g₃ = L'.g₃ := by unfold PeriodPair.g₃; rw [hG]
  have hP : ∀ z, L.weierstrassP z = L'.weierstrassP z := fun z => by unfold PeriodPair.weierstrassP; rw [h]
  unfold weberSet
  simp only [h2, h3, hP, h]

theorem exists_chain (Q : ℕ → IntermediateField ℚ ℂ → Prop) (c : ℝ) (F : IntermediateField ℚ ℂ) (a : ℝ) (h : Sz F a a)
    (step : ∀ j (G : IntermediateField ℚ ℂ) (b : ℝ), F ≤ G → Sz G b b → ∃ G' : IntermediateField ℚ ℂ, G ≤ G' ∧
      Sz G' (b + c) (b + c) ∧ ∀ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K → G' ≤ K → Q j K) (m : ℕ) :
    ∃ F' : IntermediateField ℚ ℂ, F ≤ F' ∧ Sz F' (a + m * c) (a + m * c) ∧
      ∀ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K → F' ≤ K → ∀ j, 1 ≤ j → j ≤ m → Q j K := by
  induction m with
  | zero => exact ⟨F, le_rfl, by simpa using h, fun K _ _ j h1 h2 => by omega⟩
  | succ m ih =>
    obtain ⟨F', h1, h2, h3⟩ := ih
    obtain ⟨G, g1, g2, g3⟩ := step (m + 1) F' _ h1 h2
    refine ⟨G, h1.trans g1, sz_mono g2 (le_of_eq (by push_cast; ring)) (le_of_eq (by push_cast; ring)),
      fun K hK hG j j1 j2 => ?_⟩
    rcases j2.lt_or_eq with hlt | rfl
    · exact h3 K hK (g1.trans hG) j j1 (by omega)
    · exact g3 K hK hG

theorem log_mul_pred_le (g : ℕ) : Real.log ((g * (g - 1) : ℕ) : ℝ) ≤ 2 * Real.log g := by
  rcases Nat.lt_or_ge g 2 with h | h
  · interval_cases g <;> simp
  · have h1 : ((g * (g - 1) : ℕ) : ℝ) ≤ (g : ℝ) ^ 2 := by
      have : g * (g - 1) ≤ g ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left g (Nat.sub_le g 1)
      exact_mod_cast this
    have h0 : (0 : ℝ) < ((g * (g - 1) : ℕ) : ℝ) := by
      have : 0 < g * (g - 1) := Nat.mul_pos (by omega) (by omega)
      exact_mod_cast this
    simpa using Real.log_le_log h0 h1

end GlobalTheory.FieldSize.SmallField

namespace GlobalTheory.FieldSize

open SmallField GlobalTheory.Mem.BaseExt

end GlobalTheory.FieldSize
