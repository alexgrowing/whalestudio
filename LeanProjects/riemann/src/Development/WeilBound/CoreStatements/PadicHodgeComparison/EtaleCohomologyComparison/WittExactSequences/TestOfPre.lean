import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.TensCompl
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.PerfectoidProd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.SpanMap
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.TowerSeq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.CechTens
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ColimLift
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
namespace CrystallineSemistableComparison.D.Leaf

theorem cov_tower : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Pf p A → IsRt p r → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ AIC B ∧ VAL (algebraMap A B (r 0)) ∧ Splits p (r 0) (algebraMap A B) := CrystallineSemistableComparison.D.cov_tower

theorem test_of_pre : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (r : ℕ → B), Pf p B → IsRt p r → AIC B → VAL (r 0) → ∃ (T : Type) (_ : CommRing T) (g : B →+* T), Pf p T ∧ AIC T ∧ VAL (g (r 0)) ∧ IsAdicComplete (Ideal.span {g (r 0)}) T ∧ g (r 0) ∈ nonZeroDivisors T ∧ (∀ (M : ℕ) (y : T), ∃ x, y - g x ∈ Ideal.span {g (r 0) ^ M}) ∧ (∀ (M : ℕ) (x : B), g x ∈ Ideal.span {g (r 0) ^ M} → ∀ k, r k * x ∈ Ideal.span {r 0 ^ M}) ∧ ∀ (T₁ : Type) [CommRing T₁] (x : B →+* T₁), IsAdicComplete (Ideal.span {x (r 0)}) T₁ → x (r 0) ∈ nonZeroDivisors T₁ → ∃! ψ : T →+* T₁, ψ.comp g = x := CrystallineSemistableComparison.D.test_of_pre

theorem cech_tens : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R) (N : Type) [AddCommGroup N] [Module R N] (A : Type) [CommRing A] [Algebra R A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] [∀ n, Algebra R (K n)] [∀ n, IsScalarTower R A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), IsRt p r → (∀ a : R, a ≠ 0 → ∃ M : ℕ, a ∣ r 0 ^ M) → Pf p A → Pf p B → Cov p (fun k => algebraMap R A (r k)) B → (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → (∀ w : N ⊗[R] K 0, ((alt (δ 0)).restrictScalars R).lTensor N w = 0 → ∀ k, r k • w = 0) ∧ ∀ (n : ℕ) (w : N ⊗[R] K (n + 1)), ((alt (δ (n + 1))).restrictScalars R).lTensor N w = 0 → ∀ k, r k • w ∈ LinearMap.range (((alt (δ n)).restrictScalars R).lTensor N) := CrystallineSemistableComparison.D.cech_tens

end CrystallineSemistableComparison.D.Leaf
