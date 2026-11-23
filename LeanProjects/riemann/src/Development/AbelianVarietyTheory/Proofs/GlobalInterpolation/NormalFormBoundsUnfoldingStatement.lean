import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormBoundsUnfolding
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_form_bounds_unfolding : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (n' n c j : ℕ), 1 ≤ c → ∀ (e' : ℕ → ℤ) (z' : Fin n' → E) (abelian₂ : Submodule (𝓞 E) (Fin (n + c) → E)) (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (r : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)) (e : Fin c → ℤ) (z : Fin n → E), r ∈ Loc.R1 E n c → (∀ i, 1 ≤ i → i ≤ c + 1 → -(j : ℤ) ≤ e' i ∧ e' i ≤ 0) → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.Bounds P e' z' abelian₂ xj → Loc.inX E n c (xj z') ∈ abelian₂ → r '' (abelian₂ : Set (Fin (n + c) → E)) = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P n c e z → (∀ i, -((j + 1 : ℕ) : ℤ) ≤ e i ∧ e i ≤ 0) ∧ IntV P z := by
  first | exact @GlobalTheory.Proof.normal_form_bounds_unfolding.read_normalForm | exact GlobalTheory.Proof.normal_form_bounds_unfolding.read_normalForm | (intros; apply GlobalTheory.Proof.normal_form_bounds_unfolding.read_normalForm <;> assumption)
