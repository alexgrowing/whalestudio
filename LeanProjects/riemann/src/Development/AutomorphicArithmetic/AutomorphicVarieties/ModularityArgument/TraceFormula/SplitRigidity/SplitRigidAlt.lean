import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.SecondFromFirstStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.EvaluationAtUnitaryOne

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.RgJS Formalism.L2.Host

namespace UpperTheory.V.Z.Tf.SR

def SplitRigid : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CG E n, π.IsUnitary →
  ∀ (J : Type) [Fintype J] (a : J → ℕ) (P : ∀ j, CG E (a j)), (∀ j, 1 ≤ a j) → (∀ j, (P j).IsUnitary) →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w →
      ∃ b : J → Multiset ℂˣ, (∀ j, (P j).HasSat w (b j)) ∧ π.HasSat w (∑ j, b j)) →
    ∃ j, (⟨a j, P j⟩ : Σ m, CG E m) = ⟨n, π⟩

def ShareBd : Prop := ForSys fun q X _ A => ∀ (x : X) (I : Set _) (M : ℕ) (z : Fin M → X) (c : _ → ℂ), 1 ≤ M → Function.Injective z →
  (∀ w, ‖c w‖ = 1) → (∀ w ∈ I, c w = 1) → (∀ (i : Fin M) w (k : ℕ), ∑ b, A (z i) w b ^ k = c w ^ (i.val * k) * ∑ a, A x w a ^ k) →
  ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
    (∑' p : {p : _ × ℕ // p.1 ∈ I}, lterm q (A x) (A x) σ p.1).re ≤ -Real.log (σ - 1) / M + C

def AbsShare : Prop := ForSys fun q X _ A => ∀ (x : X) (I : Set _) (J : Type) [Fintype J] (y : J → X) (M : ℕ) (C : ℝ),
  16 * (Fintype.card J + 1) ^ 2 ≤ M →
  (∀ σ : ℝ, 1 < σ → σ ≤ 2 → (∑' p : {p : _ × ℕ // p.1 ∈ I}, lterm q (A x) (A x) σ p.1).re ≤ -Real.log (σ - 1) / M + C) →
  (∀ w ∉ I, ∀ k : ℕ, ∑ a, A x w a ^ k = ∑ j, ∑ b, A (y j) w b ^ k) → ∃ j, y j = x

def AntiTw : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∃ χ : HChar E,
  (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, χ.UnrAt w ∧ ‖((χ.val w : ℂˣ) : ℂ)‖ = 1 ∧ (¬ IsSplitAt w → χ.val w = 1)) ∧
  ∀ (n : ℕ) (π : CG E n), 1 ≤ n → π.IsUnitary →
    (∀ i : ℕ, (π.twist (χ ^ i)).IsUnitary) ∧ Function.Injective fun i : ℕ => π.twist (χ ^ i)

end UpperTheory.V.Z.Tf.SR

end
