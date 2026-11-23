import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallOpenCompactNormal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_open_compact_normal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m m₁ m₂ : ℕ) (h : m₁ + m₂ = m), ∀ U ∈ nhds (1 : GL (Fin m) k), ∃ (c : kˣ) (K : Subgroup (GL (Fin m) k)), IsOpen (K : Set (GL (Fin m) k)) ∧ IsCompact (K : Set (GL (Fin m) k)) ∧ (K : Set (GL (Fin m) k)) ⊆ U ∧ K ≤ KO k (Fin m) ∧ (∀ x ∈ KO k (Fin m), ∀ y ∈ K, x * y * x⁻¹ ∈ K) ∧ (∀ y ∈ box m₁ m₂ c, uni m 0 m₁ y ∈ K) ∧ (∀ g ∈ K, ∃ p ∈ parabLower k (two (stdSum h)), ∃ y ∈ box m₁ m₂ c, g = p * uni m 0 m₁ y) ∧ IsOpen (KO k (Fin m) : Set (GL (Fin m) k)) ∧ IsCompact (KO k (Fin m) : Set (GL (Fin m) k)) := by
  first | exact @GlobalTheory.GamMul.Cong.exists_cong_factor | exact GlobalTheory.GamMul.Cong.exists_cong_factor | (intros; apply GlobalTheory.GamMul.Cong.exists_cong_factor <;> assumption)
