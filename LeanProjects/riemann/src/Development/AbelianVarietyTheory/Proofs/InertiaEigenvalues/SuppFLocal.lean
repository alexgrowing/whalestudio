import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SuppLocal

theorem suppF_local : ∀ (D : D7) (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : AE D) (k : GA D V),
    IsPrimeIdem P e f → SuppF V f k → k ∈ GfC V ∧ ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ≠ P.under (𝓞 D.host.F) →
      GlobalTheory.FinZeta.projV V v k = 1 := by
  intro D V P e f k h hk
  obtain ⟨x, rfl⟩ := (GlobalTheory.AdelicU.Supp.suppF_iff_of_isPrimeIdem V h rfl k).1 hk
  exact ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC V _ x, fun v hv => GlobalTheory.AdelicU.proj_emb_ne _ _ hv x⟩

end GlobalTheory.SuppLocal
