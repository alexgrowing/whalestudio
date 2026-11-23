import Formalism.LocalToGlobal.Columns.CardPathsEqSubmodulePairs
import Formalism.LocalToGlobal.Columns.MemOfSmulMemOfAddEqOne
import Formalism.LocalToGlobal.Columns.NeighbourConjOfTopNeighbour

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem pathCount_symmetric_holds : DecorationPathSymmetry E n ST SG := by
  intro P Q hP hQ hSTP hSGP hSTQ hSGQ i j d f
  by_cases hQP : Q = P
  · subst hQP
    exact pathCount_symm_same_prime Q hP hSTP hSGP i j d f
  by_cases hQP' : Q = conjPrime₂ P
  · subst hQP'
    exact pathCount_conj_symm (P := P) hP hSTP hSGP (fun i j d f => pathCount_symm_same_prime P hP hSTP hSGP i j d f) i j d f
  exact pathCount_symm_distinct P Q hP hQ hQP hQP' hSTP hSGP hSTQ hSGQ i j d f

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

theorem heckeOperators_commute (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : HeckeComm c S0 :=
  heckeComm_of_paths c S0 pathCount_symmetric_holds

end Formalism.L2.Col
