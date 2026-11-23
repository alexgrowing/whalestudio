import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem tensBasis : ∀ {K : Type} [Field K] {J : Type} [DecidableEq J] (V W : J → Type 1) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)] (B : J → Type 1) [DecidableEq (Σ t, B t)] (b : ∀ t, Module.Basis (B t) K (V t)), ∃ e : (⨁ t, V t ⊗[K] W t) ≃ₗ[K] ⨁ u : (Σ t, B t), W u.1, ∀ (t : J) (β : B t) (x : W t), e (DirectSum.lof K J (fun t => V t ⊗[K] W t) t (b t β ⊗ₜ x)) = DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x := by
  classical
  intro K _ J _ V W _ _ _ _ B _ b
  let et : ∀ t, (V t ⊗[K] W t) ≃ₗ[K] (Π₀ _ : B t, W t) := fun t =>
    (TensorProduct.congr (b t).repr (LinearEquiv.refl K (W t))) ≪≫ₗ
      (TensorProduct.finsuppScalarLeft K (W t) (B t)) ≪≫ₗ (finsuppLequivDFinsupp K)
  have het : ∀ t (β : B t) (x : W t), et t (b t β ⊗ₜ x) = DFinsupp.single β x := by
    intro t β x
    simp [et, TensorProduct.finsuppScalarLeft_apply_tmul, Module.Basis.repr_self]
  let C : (⨁ u : (Σ t, B t), W u.1) ≃ₗ[K] (Π₀ t, Π₀ _ : B t, W t) :=
    DFinsupp.sigmaCurryLEquiv (R := K) (M := fun t (_ : B t) => W t)
  refine ⟨(DFinsupp.mapRange.linearEquiv et) ≪≫ₗ C.symm, ?_⟩
  intro t β x
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  have h1 : C (DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x)
      = DFinsupp.single t (DFinsupp.single β x) := by
    have : DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x
        = DFinsupp.single (⟨t, β⟩ : Σ t, B t) x := rfl
    rw [this]
    change DFinsupp.sigmaCurry (δ := fun t (_ : B t) => W t) (DFinsupp.single (⟨t, β⟩ : Σ t, B t) x) = _
    convert DFinsupp.sigmaCurry_single (δ := fun t (_ : B t) => W t) (⟨t, β⟩ : Σ t, B t) x
  rw [h1, ← het]
  exact DFinsupp.mapRange_single (hf := fun i => map_zero (et i))

end GlobalTheory.CompanionTheory.KunGlue
