import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.CoefZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeProjectionEigenform
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftFourierCoefficients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetRepresentativesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainDescriptionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainInvarianceOfDescriptionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCentralInvarianceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterIntegralPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftExistenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftConductorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalTypeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftHeckeEigenvaluesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftWhittakerExpansionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftRapidDecayStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt)
open scoped NumberField.AdeleRing ValuativeRel ComplexConjugate
open Ad3 Ad3.R

namespace UpperTheory.V.Z.Sym.Unl

theorem selfAdj : SelfAdj := by
  intro k N _ hk χ hχ g p hp hpN
  have hB := GlobalTheory.T.global_rankin_selberg_basic_facts
  have hE := Ad3P.sEig k N hk χ g
  obtain ⟨hF, hEig⟩ := hE
  obtain ⟨ω, hω⟩ := GlobalTheory.T.newform_lift_existence hB N χ
  obtain ⟨hsign, φ, hL⟩ := GlobalTheory.T.newform_lift_level hB k N χ g.f g.a hF hEig.2.1 ω hω
  have hOmL := GlobalTheory.T.newform_lift_conductor hB k N χ hχ hsign ω hω
  have hHk := GlobalTheory.T.newform_lift_hecke_eigenvalues hB GlobalTheory.T.hecke_coset_representatives GlobalTheory.T.congruence_subgroup_coset_decomposition (GlobalTheory.T.newform_lift_conductor hB) (GlobalTheory.T.newform_lift_level hB)
    (GlobalTheory.T.newform_lift_level_character hB) (GlobalTheory.T.newform_lift_local_type hB) k N hk χ hχ g.f g.a hF hEig ω φ hω hL
  have hW := GlobalTheory.T.newform_lift_whittaker_expansion k N hk χ hχ g.f g.a hF hEig ω φ hω hL
  have hb := GlobalTheory.T.newform_lift_rapid_decay hB k N hk χ hχ g.f g.a hF hEig ω φ hω hL
  obtain ⟨μ, 𝓕, mK, 𝓓, hS⟩ := GlobalTheory.T.fundamental_domain_invariance_of_description GlobalTheory.T.fundamental_domain_description
  have hG1 := GlobalTheory.T.central_character_integral_properties GlobalTheory.T.fundamental_domain_integral_central_invariance
  obtain ⟨v, hv⟩ := hB.2.2.1 p hp
  have hnd : ¬pOf v ∣ N := by rwa [hv]
  obtain ⟨C, hC⟩ := hb.1
  have hφ0 : φ ≠ 0 := by
    intro h0
    have h1 := hW.2.2.2 (-1)
    rw [h0, GlobalTheory.CompanionTheory.RSEigen.wh_zero] at h1
    exact GlobalTheory.CompanionTheory.RSEigen.wr_ne k h1.symm
  have hpr := GlobalTheory.CompanionTheory.RSEigen.pr_self_ne hS hG1 (ω := ω) hL.cont hb.1 hL.left hL.cen hφ0
  have hone : ∀ x : G2, cdet 1 x = 1 := by
    intro x
    simp [Ad3.R.cdet, GroundTheory.Global.HeckeCharacter.toIdele_apply]
  have hPr : GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.Pr μ 𝓕 φ 1 1 1 ≠ 0 := by
    simpa [GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.Pr, GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.Fn, hone, GlobalTheory.CompanionTheory.RSEigen.pr] using hpr
  have hloc1 : ∀ u, localChar (1 : HeckeCharacter ℚ) v u = 1 := by
    intro u
    ext
    simp [GroundTheory.Automorphic.GodementSection.coe_localChar,
      GroundTheory.Global.HeckeCharacter.localComponent_apply, GroundTheory.Global.HeckeCharacter.toIdele_apply]
  have hunr1 : IsUnramifiedChar (localChar (1 : HeckeCharacter ℚ) v) :=
    isUnramifiedChar_iff.2 (fun u _ => hloc1 u)
  have hstd := (hB.1 v).1
  obtain ⟨ϖ, B, hR⟩ := (GlobalTheory.T.congruence_subgroup_coset_decomposition (Qv v) (localAdelicChar ℚ v) hstd).1
  have key := GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.eig_relation (φ := φ) (ω := ω) (c := 1) (μ := μ) (𝓕 := 𝓕) (C := C)
    hL.cont hC hL.left hL.cen (by simp)
    (fun F hF hFb hFL hFC h => (hG1 μ 𝓕 mK 𝓓 hS F hF hFb hFL).1 hFC h) hS.vol
    (v := v) (hB.1 v).2.2.2.2.2.1 hB.2.2.2.1 (hB.2.2.2.2.2.2.2 v) hunr1
    (lam := lamOf k g.a v) (fun g W hW' => hHk.good v hnd g W hW') hR (h := 1)
    (GroundTheory.Automorphic.Reduction.finAt_one v) hPr
  have hω1 : ((localChar ω v ϖ : ℂˣ) : ℂ) = χ p := by
    rw [quasiChar_apply_eq_of_isUnramified (hOmL.good v hnd).1 hR.1, (hOmL.good v hnd).2, hv]
  rw [hloc1, hω1] at key
  simp only [lamOf, hv, Units.val_one, one_mul, map_mul, Complex.conj_ofReal] at key
  have hr : (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _).ne'
  have h : g.a p * (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)
      = (χ p * (starRingEnd ℂ) (g.a p)) * (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) :=
    key.trans (by ring)
  have h2 := mul_right_cancel₀ hr h
  linear_combination -h2

end UpperTheory.V.Z.Sym.Unl
