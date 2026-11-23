import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightInfinitesimalCharacterParamOfLevelCompatib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightInfinitesimalCharacterParam_of_levelCompatible : ∀ (D : D7) (M : Formalism.L2.MtFam D) (tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E), Formalism.L2.LevelTied D M tup → (∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)}) → (∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ), (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam) → WeightParam D := by
  first | exact @GlobalTheory.WeightParamTie.weightParam_of_levelTied | exact GlobalTheory.WeightParamTie.weightParam_of_levelTied | (intros; apply GlobalTheory.WeightParamTie.weightParam_of_levelTied <;> assumption)
