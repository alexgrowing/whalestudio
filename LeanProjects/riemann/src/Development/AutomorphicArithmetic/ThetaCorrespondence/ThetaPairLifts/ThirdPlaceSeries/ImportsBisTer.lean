import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PartOrthPin
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i)) → GlobalTheory.ThetaExh.PartOrth D.nd i := by
  intro hL D P i ⟨X⟩ σ σ' hne
  rw [Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  have hni : ¬ (P.rep σ).Iso (P.rep σ') := fun h => hne (P.rep_inj σ σ' h)
  rw [X.φ_inner]
  exact GlobalTheory.IsotOrth.isotIn_orthogonal D D.R.r X.A X.ρ X.C X.B X.lin X.herm X.pos X.stab X.inv X.adm
    (P.rep σ) (P.rep σ') hni _ ((X.isot σ u).1 hu) _ ((X.isot σ' v).1 hv)
end GlobalTheory.PartOrthPin
end
