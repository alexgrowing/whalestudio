import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsStrongMultiplicityOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNonsplitPlaceWithInertDatumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterAtInertPlaceOfSphericalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySatakeEqOfSameUnramifiedBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceOfSplitPlaceRealSubfieldHostStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RepOfLocal

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ S : Reading P.T, IsTrue P S → Laws S → ∀ i, RepOfLoc D.nd D.naut i := by
  intro hL D P S hT hLaws i P₁ P₂ hsplit hns
  apply P.H.av.inj i P₁ P₂
  refine GlobalTheory.T.algebraic_modular_forms_strong_multiplicity_one D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i P₁) (P.H.av.S i P₂) (P.H.av.irr i P₁) (P.H.av.irr i P₂) ?_ ?_
  · intro s
    have hw := GlobalTheory.T.isSplitPlace_of_splitPlace_realSubfield_host D s
    refine ⟨((S i s.w hw).rep P₁).toIrrRep, ((S i s.w hw).rep P₂).toIrrRep, hT.rep i s hw P₁, hT.rep i s hw P₂, ?_⟩
    have e1 := (S i s.w hw).locV P₁
    have e2 := (S i s.w hw).locV P₂
    rw [hsplit s.w hw, e2] at e1
    exact ((hLaws i s.w hw).iso _ _ _).1 e1.symm
  · intro v hv
    obtain ⟨w, hO, hns', ⟨Dv⟩⟩ := GlobalTheory.T.exists_nonsplit_place_with_inertDatum D D.R.nV v hv
    have hsph : ∀ Q : D.naut.AV i, (P.H.av.rep i Q).SphAt v := fun Q => by
      have h := D.nbc.embAV_sph i Q w hns'
      rw [P.H.emb i Q] at h
      exact (P.H.au.sph _ _ _ _ w v hns' hO).1 h
    obtain ⟨α₁, hα₁, e₁⟩ :=
      P.H.au.sat _ _ _ (P.H.av.rep i P₁) v w hO Dv (GlobalTheory.T.exists_satakeParameter_at_inertPlace_of_spherical _ _ _ v w hO (hsph P₁) Dv)
    obtain ⟨α₂, hα₂, e₂⟩ :=
      P.H.au.sat _ _ _ (P.H.av.rep i P₂) v w hO Dv (GlobalTheory.T.exists_satakeParameter_at_inertPlace_of_spherical _ _ _ v w hO (hsph P₂) Dv)
    have hu := hns w hns'
    rw [D.nbc.embAV_sat, D.nbc.embAV_sat, P.H.emb, P.H.emb, e₁, e₂] at hu
    refine ⟨w, Dv, α₁, hO, hα₁, ?_⟩
    obtain ⟨f, hf, hf0, U, hU, hUv, hh⟩ := hα₂
    refine ⟨f, hf, hf0, U, hU, hUv, fun h hh' => ?_⟩
    rw [GlobalTheory.T.unitarySatake_eq_of_same_unramifiedBaseChange _ Dv.ϖ Dv.σw _ D.R.nV Dv.unram α₁ α₂ hu h hh']
    exact hh h hh'

end GlobalTheory.RepOfLocal
