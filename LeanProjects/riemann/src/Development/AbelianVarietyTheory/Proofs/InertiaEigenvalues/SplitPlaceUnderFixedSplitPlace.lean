import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitOfGPl
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceUnderFixed

theorem exists_splitPlace_under_plGw : ∀ (D : D7) (s : SplitPlace D.host.E), s.v ∈ gPl D → ∃ (k : Fin 2) (v : D.nd.PlG k) (s₀ : SplitPlace D.host.E), s₀.w = D.naut.plGw k v ∧ s₀.v = s.v := by
  intro D s hs
  obtain ⟨k, u, s₀, hv, hw⟩ := GlobalTheory.FormInner.exists_split_of_gPl D s.v hs
  exact ⟨k, u, s₀, hw, hv⟩

end GlobalTheory.PlaceUnderFixed
