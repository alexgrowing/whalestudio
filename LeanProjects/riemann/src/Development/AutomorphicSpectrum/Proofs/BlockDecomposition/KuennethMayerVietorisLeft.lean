import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosievePairingFamilyCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictSelfPullCEqStatement

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem glue_r : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₁ : ObjectProperty E.C₁) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₂) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → U₁ (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun U₁ (capU V S) (capU W S) (h₁ S) (h₂ S)) → E.Kun U₁ (capU V ∅) (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  intro hM hC K _ E U₁ ι _ _ V W hV hW h₁ h₂ hK
  refine GlobalTheory.T.cosieve_pairing_family_compat hM hC E.F₂ E.F₃ (fun a => CH.cx (U₁.ι ⋙ E.F₁ a))
    (fun U U' => (∀ T, U' T → U₁ (E.L₁.obj T)) ∧ (∀ T, U' T → U (E.L₂.obj T)))
    (fun U U' r {a a' c} ha => E.pr U₁ U U' r.1 r.2 ha) ?_ V W hV hW (fun S => ⟨h₁ S, h₂ S⟩)
    (fun S hS => hK S hS)
  intro A B A' B' r₁ r₂ k k' a a' c ha i j n hn x y
  have h := GlobalTheory.T.pairing_restrict_compat E r₁.1 r₁.2 r₂.1 r₂.2 (le_refl U₁) k k' ha hn x y
  rw [GlobalTheory.T.restrict_self_pullC_eq] at h
  exact h

end GlobalTheory.CompanionTheory.KunGlue
