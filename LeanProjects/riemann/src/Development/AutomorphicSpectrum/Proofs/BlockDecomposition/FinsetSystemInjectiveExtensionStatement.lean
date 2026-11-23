import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsetSystemInjectiveExtension
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finset_system_injective_extension : ∀ {K : Type} [CommRing K] {ι : Type} [DecidableEq ι] [Fintype ι] {W : Type} [AddCommGroup W] [Module K W] {Λ : Type} (b : Module.Basis Λ K W) (good' : Λ → Prop) (T : Λ → Finset ι), (∀ l, good' l → T l ≠ Finset.univ) → ∀ (M : Finset ι → Type) [∀ S, AddCommGroup (M S)] (r : ∀ {S S' : Finset ι}, S ⊆ S' → M S → M S') (j : ∀ S, M S →+ W), (∀ S, Function.Injective (j S)) → (∀ {S S' : Finset ι} (h : S ⊆ S') x, j S' (r h x) = j S x) → (∀ S w, (∃ x, j S x = w) ↔ w ∈ Submodule.span K (b '' {l | good' l ∧ T l ⊆ S})) → ExP M r := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc.exP_of_basis | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc.exP_of_basis | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc.exP_of_basis <;> assumption)
