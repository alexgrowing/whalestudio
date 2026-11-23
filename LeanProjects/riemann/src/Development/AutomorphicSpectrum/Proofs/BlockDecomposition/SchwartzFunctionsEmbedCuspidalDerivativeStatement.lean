import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionsEmbedCuspidalDerivative
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_functions_embed_cuspidal_derivative : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (m : ℕ) (a b : GRep k (m + 1))
    (hs : IsSmooth a.ρ) (hb : IsSmooth b.ρ) (hi : a.ρ.IsIrreducible) (hcu : IsCuspidal a.ρ),
    ∃ ι : SchF k (m + 1) b.V →ₗ[ℂ] (Rm ψ a b).V, Function.Injective ι ∧
      (∀ x f, ι (shiftF x f) = (Rm ψ a b).ρ (uM (m + 1) x) (ι f)) ∧
      (∀ g f, ι (actF (b.tw (-1 / 2)).ρ g f) = (Rm ψ a b).ρ (levi k (m + 1) g) (ι f)) ∧
      ∀ x v, (Rm ψ a b).ρ (uM (m + 1) x) v - v ∈ LinearMap.range ι := by
  first | exact @GlobalTheory.CompanionTheory.BZShellOpen.open_part | exact GlobalTheory.CompanionTheory.BZShellOpen.open_part | (intros; apply GlobalTheory.CompanionTheory.BZShellOpen.open_part <;> assumption)
