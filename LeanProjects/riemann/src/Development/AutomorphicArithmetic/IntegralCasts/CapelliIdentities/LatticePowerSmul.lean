import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPowSmulMemAlt

theorem UpperTheory.Reformulated.B.LatticePowerSmul.exists_pow_smul_mem_lattice_alt :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (LL : Formalism.BasicNotions.Loc.FinExt l) (T : GlobalTheory.BKGal.QLat LL) (v : T.V),
      ∃ (n : ℕ), (↑l : ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l))) ^ n • v ∈ T.L.T := by
  intro l inst LL T v
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact UpperTheory.exists_pow_smul_mem_alt T.L.T (fun c hc => ⟨⟨c, hc⟩, rfl⟩) T.L.span v
