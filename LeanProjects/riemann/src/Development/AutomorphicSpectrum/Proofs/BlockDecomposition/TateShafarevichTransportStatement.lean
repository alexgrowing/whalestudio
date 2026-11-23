import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateShafarevichTransport
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_shafarevich_transport : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] {I I' : Type} [Fintype I] [Fintype I'] {D : I → Type} {D' : I' → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)] [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)] (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i)) (φ' : ∀ i, D' i →* Γ') (hφ' : ∀ i, Continuous (φ' i)) (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ) {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (ρ' : Representation R Γ' M) (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i)), (∀ i d, φ' (eI i) (eD i d) = eG (φ i d)) → (∀ g, χ' (eG g) = χ g) → (∀ g m, ρ' (eG g) m = ρ g m) → ShaG φ' hφ' χ' ρ' → ShaG φ hφ χ ρ := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.ShaTransfer.shaG_transfer | exact GlobalTheory.CompanionTheory.PTIso.ShaTransfer.shaG_transfer | (intros; apply GlobalTheory.CompanionTheory.PTIso.ShaTransfer.shaG_transfer <;> assumption)
