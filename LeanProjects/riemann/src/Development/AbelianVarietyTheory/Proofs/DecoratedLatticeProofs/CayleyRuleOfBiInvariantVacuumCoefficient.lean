import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrderDetOneAddOfIntegralInverseUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralHeisenbergInvariantFormsProportionalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSymmetricElementaryDivisorsUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCoset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.CayleyVac

theorem exists_cartanU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {n : ℕ} (g : GU σ n) :
    ∃ (d : Fin n → ℤ) (t : GU σ n), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) ∧
      ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g = k₁ * t * k₂ := by
  obtain ⟨d, hd, a, ha, b, hb, e⟩ := GlobalTheory.LFun.UnitaryDiv.exists_good_div L ϖ σ q n hU g
  obtain ⟨t, ht⟩ := GlobalTheory.InertThetaCompare.exists_diag (σ := σ) hU hd
  refine ⟨fun i => d.getD i.1 0, t, ht, ?_⟩
  refine GlobalTheory.UnramDoubleCoset.doubleCoset_GU_of_GL L ϖ σ q n hU t g a b ha hb ?_
  apply Units.ext
  simp only [Units.val_mul]
  rw [e, ht]

end GlobalTheory.ChainOnto.CayleyVac

namespace GlobalTheory.ChainOnto.CayleyVac

theorem cayley_of_coeff {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {M : Type} [AddCommGroup M] [Module ℂ M]
    {α β : Type} (ρ : Matrix α β L → Module.End ℂ M) {r N : ℕ} (π : GU σ r →* Module.End ℂ M) (s : M)
    (l : M →ₗ[ℂ] ℂ) (hls : l s ≠ 0)
    (hco : ∀ e : M →ₗ[ℂ] ℂ, (∀ u ∈ intMat L α β, ∀ m, e (ρ u m) = e m) → ∀ m, e m * l s = l m * e s)
    (φ : GU σ r → ℂ) (hφ : KerU ϖ q N ((-1) ^ N) φ) (hl : ∀ g, l (π g s) = φ g * l s) :
    CayleyRule q N ρ π s := by
  intro e he g hdet hint
  have h1 := hco e he (π g⁻¹ s)
  rw [hl] at h1
  have h2 : e (π g⁻¹ s) = φ g⁻¹ * e s := mul_right_cancel₀ hls (by rw [h1]; ring)
  rw [h2]
  congr 1
  obtain ⟨d, t, ht, k₁, hk₁, k₂, hk₂, hg⟩ := exists_cartanU hU g⁻¹
  have hord := GlobalTheory.T.order_det_one_add_of_integral_inverse_unitary L ϖ σ q hU r g t d ht k₁ hk₁ k₂ hk₂ hg hdet hint
  rw [hg, hφ d t ht k₁ hk₁ k₂ hk₂, hord, _root_.zpow_neg, ← _root_.inv_zpow]
  congr 1
  push_cast
  rw [_root_.mul_inv, ← _root_.inv_pow, ← _root_.inv_pow, _root_.inv_neg_one]

end GlobalTheory.ChainOnto.CayleyVac

open GlobalTheory.ChainOnto.CayleyVac in

theorem GlobalTheory.ChainOnto.cayleyRule_of_vacCoeff : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ l : M →ₗ[ℂ] ℂ, l s ≠ 0 → (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, l (ρ u m) = l m) → (∀ φ : GU σ n → ℂ, KerU ϖ q n' ((-1) ^ n') φ → (∀ g, l (ω (g, 1) s) = φ g * l s) → CayleyRule q n' ρ (ω.comp (MonoidHom.inl _ _)) s) ∧ ∀ φ : GU σ n' → ℂ, KerU ϖ q n ((-1) ^ n) φ → (∀ g, l (ω (1, g) s) = φ g * l s) → CayleyRule q n ρ (ω.comp (MonoidHom.inr _ _)) s := by
  intro L _ _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hs l hls hl
  have hU : IsUnramInv ϖ σ q := hs.1.unr
  have hco : ∀ e : M →ₗ[ℂ] ℂ, (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, e (ρ u m) = e m) → ∀ m, e m * l s = l m * e s :=
    fun e he => GlobalTheory.T.integral_heisenberg_invariant_forms_proportional L ϖ σ q δ ψ n n' M ρ ω s hs l e hl he
  refine ⟨fun φ hφ hc => cayley_of_coeff hU ρ _ s l hls hco φ hφ ?_, fun φ hφ hc => cayley_of_coeff hU ρ _ s l hls hco φ hφ ?_⟩
  · intro g; simpa using hc g
  · intro g; simpa using hc g

end
