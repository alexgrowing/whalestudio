import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneRankOneLocalParam
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.TripleGal GlobalTheory.CuspRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_rank_one_local_param : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ), Continuous μ → IsLAdicOf art ι χ n μ → ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal), GlobalTheory.WeilDeligne.wdOf h hl ι (rk1 μ) = ParLaws.locPar hL (CG.ofChar χ) h := by
  first | exact @GlobalTheory.AwayLGC.weil_deligne_rank_one_eq_local | exact GlobalTheory.AwayLGC.weil_deligne_rank_one_eq_local | (intros; apply GlobalTheory.AwayLGC.weil_deligne_rank_one_eq_local <;> assumption)
