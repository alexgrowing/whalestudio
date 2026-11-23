import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SelmerGroupDualExact
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selmer_group_dual_exact : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), μ.comp (toGS Ω _) = cycMod F Ω l r → ContAction (twDual μ ρ) := by
  first | exact @GlobalTheory.CompanionTheory.GalDual.contAction_twDual | exact GlobalTheory.CompanionTheory.GalDual.contAction_twDual | (intros; apply GlobalTheory.CompanionTheory.GalDual.contAction_twDual <;> assumption)
