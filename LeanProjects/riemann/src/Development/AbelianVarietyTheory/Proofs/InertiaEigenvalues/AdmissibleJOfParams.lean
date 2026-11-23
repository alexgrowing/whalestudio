import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2PairOfAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionaryOfParamsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpsReadingRowAdmStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescent
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

namespace GlobalTheory.AdmJointAssembly

theorem main : ∀ (D : D7) (L : SizeData₂ D), SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → WeightParam D →
    BlockCharParam D → AdmissibleParameterJ.AdmPar L → AdmissibleParameterJ.AdmJ L := by
  intro D L h0 h1 h2 h5 hW hB hP
  have hG := GlobalTheory.T.admG2_pair_of_admissible D h0 h1 h2 h5
  exact ⟨hG.1, GlobalTheory.CrysWD.crysIffWD D, hG.2, GlobalTheory.T.admissible_dictionary_of_params GlobalTheory.Published.cheb_holds D h2 hW hB, GlobalTheory.T.hodgeTateJumpsReading_rowAdm D, hP⟩

end GlobalTheory.AdmJointAssembly
