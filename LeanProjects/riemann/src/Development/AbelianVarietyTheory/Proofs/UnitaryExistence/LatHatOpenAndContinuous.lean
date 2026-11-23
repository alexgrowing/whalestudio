import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem continuous_finPart (D : D7) : Continuous (finPart D) := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
  rw [this]
  exact continuous_snd.comp hc

theorem continuous_infPart (D : D7) : Continuous (infPart D) := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (infPart D : AE D → _) = fun z => (e z).1 := funext fun z => (he z).1.symm
  rw [this]
  exact continuous_fst.comp hc

theorem continuous_finHom_val (D : D7) (V : HSp D) : Continuous (fun k : GA D V => (finHom V k).1) := by
  have h : Continuous (fun k : GA D V => (matHom V k).1) :=
    Units.continuous_val.comp continuous_subtype_val
  exact h.matrix_map (continuous_finPart D)

theorem latHat_open_and_continuous : ∀ (D : D7) (V : HSp D), (∀ N : ℕ, 0 < N → IsOpen {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E | ∃ y ∈ latHat V, z = N • y}) ∧ Continuous (fun k : GA D V => (finHom V k).1) ∧ Continuous (finPart D) ∧ Continuous (infPart D) := by
  intro D V
  refine ⟨?_, continuous_finHom_val D V, continuous_finPart D, continuous_infPart D⟩
  obtain ⟨h1, -, -, h4, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  rw [h1]
  exact (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat D.host.F D.host.E V.rank (latC V) h4).1

end GlobalTheory.Member
