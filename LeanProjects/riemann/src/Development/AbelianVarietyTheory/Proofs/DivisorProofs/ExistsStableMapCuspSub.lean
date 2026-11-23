import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCuspImageOfSplitInvariant

open NumberField

theorem GlobalTheory.CuspQuot.exists_stable_map_cuspSub : GlobalTheory.Published.CuspidalSpectrumGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (d : ℕ) (f : GlobalTheory.CuspRep.Sm E d),
    GlobalTheory.CuspRep.IsCuspForm f → f ≠ 0 →
    ∃ (W : Submodule ℂ (GlobalTheory.CuspRep.Sm E d)) (τ : GlobalTheory.CuspRep.CuspSub E d) (p : GlobalTheory.CuspRep.Sm E d →ₗ[ℂ] τ.V),
      f ∈ W ∧ GlobalTheory.CuspRep.IsStable W ∧ p f ≠ 0 ∧
      ∀ (o : GlobalTheory.CuspRep.Op E d), ∀ g ∈ W, p (GlobalTheory.CuspRep.act o g) = τ.op o (p g) :=
  GlobalTheory.CuspQuot.exists_cuspSub_map
