import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealLatticeToAddSubgroupEqIdealSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAnalyticIsoOfIsAnalyticUniformization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAnalyticUniformizationOfIsAnalyticIso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvSmulEqFinitePartInvSmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulQuotientInvMkEqMkIffMulEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbelianizationEqOfForallAbRestrictEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinMapAbelianUniqueStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjEqOnAlgebraicClosure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPointEqPointMapRing

open NumberField
open scoped nonZeroDivisors GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem ellipticMainTheoremCM : GlobalTheory.Published.EllipticMainTheoremCM := by
  classical
  intro K _ _ _ _ h2 Art hArt σ s hs X _ 𝔞 h𝔞 ξ hξ
  obtain ⟨Art₀, hArt₀, hlink⟩ := GlobalTheory.CompanionTheory.EllipticCM.exists_globalArtinMap_tied K h2
  have hEq : Art = Art₀ := MonoidHom.ext fun c =>
    GlobalTheory.CompanionTheory.GaloisAb.abelianization_eq_of_forall_abRestrict_eq K _ _ fun L h =>
      GlobalTheory.T.artin_map_abelian_unique K Art Art₀ hArt hArt₀ L h c
  subst hEq
  have hfound := hlink σ s hs
  let 𝔞u : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 𝔞 h𝔞
  have hf := GlobalTheory.CompanionTheory.EllipticCM.isAnalyticUniformization_of_isAnalyticIso h2 X 𝔞 h𝔞 ξ hξ
  obtain ⟨f', ⟨hf', hrel⟩, -⟩ :=
    GroundTheory.Global.Elliptic.main_theorem_complexMultiplication h2 σ s hfound 𝔞u hf
  have hid : ((s⁻¹ • 𝔞u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ • 𝔞 :=
    GlobalTheory.CompanionTheory.EllipticCM.inv_smul_eq_finitePart_inv_smul s 𝔞u
  rw [hid] at hf'
  have hex := GlobalTheory.CompanionTheory.EllipticUniformization.exists_analyticIso_of_isAnalyticUniformization _ _ f' hf'
  rw [GlobalTheory.CompanionTheory.EllipticDict.idealLattice_toAddSubgroup_eq_idealSub] at hex
  obtain ⟨ξ', hξ', hξf⟩ := hex
  refine GlobalTheory.EllipticCM.transports_of_exists h𝔞 rfl hξ' fun x => ?_
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (GlobalTheory.Idele.mulEquiv (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ h𝔞 rfl (Submodule.Quotient.mk t))
  rw [← hy]
  have hq := (GlobalTheory.CompanionTheory.IdeleQuot.smulQuotient_inv_mk_eq_mk_iff_mulEquiv s 𝔞u t y).2 hy.symm
  have h3 := hrel t y hq
  rw [GlobalTheory.CompanionTheory.ConjPointDict.mapPoint_eq_pointMapRing, GlobalTheory.EllipticCM.torsionIncl_mk,
    GlobalTheory.EllipticCM.torsionIncl_mk, hξf, h3]
  rfl

end GlobalTheory.CompanionTheory.Hypotheses₂
