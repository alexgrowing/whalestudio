import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaActs
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionExtensionFieldTotalStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LatticePartCongrOfPhiRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsShiftGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartEqOfThetaOperatorEqStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPairEqOfThetaOperatorRelStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionMapInj

theorem qkToAk_injective : Laws → Laws2 → QkToAkInjSt := by
  intro hL hL₂ R _ _ I hR D A G _ _ hG U F _ _ _ n hn p p' x hp hp'
  obtain ⟨w₀, hw₀⟩ := U.ext
  obtain ⟨hx, H⟩ := hp w₀ hw₀
  obtain ⟨-, H'⟩ := hp' w₀ hw₀
  obtain ⟨θ, hθ, hact⟩ := GlobalTheory.TorsionTheta.exists_theta_acts hL.kerPow _ A F (jFK (R := R) F) n hn x hx
  obtain ⟨w, hw, Hw⟩ := H θ hθ
  obtain ⟨w', hw', Hw'⟩ := H' θ hθ
  obtain ⟨E₁, E₂⟩ := GlobalTheory.T.expansion_extensionField_total hL hL₂ R I hR D A G hG U F n hn w₀ hw₀
  have key : ∀ s : Fam D.toPre F n, ∃ s' : Fam D.toPre F n,
      PhiRel D.toPre F n p w s s' ∧ PhiRel D.toPre F n p' w' s s' := fun s => by
    obtain ⟨t, ht⟩ := E₁ s
    obtain ⟨t', ht'⟩ := hact t
    obtain ⟨s', hs'⟩ := E₂ t'
    exact ⟨s', Hw t t' s s' ht hs' ht', Hw' t t' s s' ht hs' ht'⟩
  have hB := D.tau_bimult
  obtain ⟨z, hz⟩ := GlobalTheory.lattice_part_congr_of_phiRel hL.globalFns hL₂.secTwist R D.toPre hB F n hn p p' w w' hw hw' key
  obtain ⟨w₂, hw₂, Hs⟩ := GlobalTheory.QkShift.qk_shift hL.globalFns R D.toPre hB F n hn p (GlobalTheory.TorusExt.qkShift hB p z) z
    (GlobalTheory.TorusExt.iota hB F z) rfl (GlobalTheory.TorusExt.isIota_iota hB z) ((GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl) w hw
  have key₂ : ∀ s : Fam D.toPre F n, ∃ s' : Fam D.toPre F n,
      PhiRel D.toPre F n (GlobalTheory.TorusExt.qkShift hB p z) w₂ s s' ∧ PhiRel D.toPre F n p' w' s s' := fun s => by
    obtain ⟨s', h, h'⟩ := key s
    exact ⟨s', Hs s s' h, h'⟩
  have hb := GlobalTheory.T.abelianPart_eq_of_thetaOperator_eq hL.globalFns hL₂.secTwist R D.toPre hB F n hn _ p' w₂ w' hw₂ hw' key₂ hz
  have hg := GlobalTheory.T.torsionPair_eq_of_thetaOperator_rel hL.globalFns hL₂.secTwist R D.toPre hB F n hn _ p' w₂ w' hw₂ hw' key₂ hz hb
  exact (GlobalTheory.TorusExt.equiv_iff hB p p').2 ⟨z, hz, hg.symm⟩

end GlobalTheory.TorsionMapInj
