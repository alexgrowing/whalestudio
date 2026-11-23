import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassTranslateSumMemSpanSelfDualLatticeVacua
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_class_translate_sum_mem_span_selfDual_lattice_vacua : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ C : Finset (Matrix (Fin n') (Fin n) L), ∃ c : Matrix (Fin n') (Fin n) L → ℂ, x ∈ C ∧
      (∀ y ∈ C, c y ≠ 0 ∧ GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ∧ GlobalTheory.Hk3.HoweG.GramEq σ JT x y) ∧
      (∀ y ∈ C, ∀ y' ∈ C, y ≠ y' → y - y' ∉ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ∧
      ∑ y ∈ C, c y • ρ y s ∈ Submodule.span ℂ {w : M | ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
        ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w} := by
  first | exact @GlobalTheory.Hk3.HoweG.gramClass_sum_mem_span_selfDual_vac | exact GlobalTheory.Hk3.HoweG.gramClass_sum_mem_span_selfDual_vac | (intros; apply GlobalTheory.Hk3.HoweG.gramClass_sum_mem_span_selfDual_vac <;> assumption)
