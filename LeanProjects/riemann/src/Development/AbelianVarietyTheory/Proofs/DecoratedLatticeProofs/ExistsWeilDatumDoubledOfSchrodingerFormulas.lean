import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HypsSatisfiable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondOnCommonRangeOfSecond
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta

noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.SchDatum

theorem exists_datum : ∀ (D : D7) (A V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (WO A V)) (𝓨 : Set (WO A V)), IsCovolOne (ratL V A) ν 𝓨 → ∀ ω : G D A.rank →* Module.End ℂ (schwartzA θ V.rank A.rank), IsWeilSch ψ χ θ V ν ω → ∃ (ψ₀ : AddChar (AF D.host.F) ℂ) (μ : D.host.E) (lam : D.host.F) (κ : GA D (dblSp A) ≃* G D A.rank) (omh : GA D (dblSp A) × GA D V →* Module.End ℂ (WO (dblSp A) V → ℂ)), IsStdChar D ψ₀ (-1) ∧ IsSkew μ ∧ algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ ∧ ψ = shift ψ₀ lam ∧ IsChart A μ κ ∧ IsWeilDatumO ψ₀ (dblSp A) V 1 χ⁻¹ omh ∧ IsTransport ψ₀ θ A V ν 𝓨 omh κ ω := by
  intro D A V ψ hψ χ hχ hr θ hθ ν 𝓨 hν ω hω
  obtain ⟨ψ₀, h₀, lam, hlam, hψeq⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hsh : ψ = shift ψ₀ lam := by
    ext x
    rw [hψeq]
    rfl
  have hlamE : algebraMap D.host.F D.host.E lam ≠ 0 := (map_ne_zero _).2 hlam
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  set μ' : D.host.E := -D.host.xi0 / algebraMap D.host.F D.host.E lam with hμ'
  have hsk : IsSkew μ' := by
    refine ⟨div_ne_zero (neg_ne_zero.2 hxi) hlamE, ?_⟩
    rw [hμ', star_div₀, star_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, Formalism.IndefR.Eqv.star_algebraMapF]
    ring
  have hl : algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ' := by
    rw [hμ']; field_simp
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ' hsk
  obtain ⟨hχi, hri⟩ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χ V.rank hχ hr
  have hr1 : ResEta D 1 (dblSp A).rank := by
    have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D A.rank
    convert this using 2
    simp [GlobalTheory.Doubling.dblSp]
    omega
  obtain ⟨omh, homh⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ₀ (dblSp A) V 1 χ⁻¹ h₀
    ⟨continuous_const, fun _ => rfl⟩ hχi hr1 hri
  obtain ⟨omS, hS⟩ := GlobalTheory.StdUnn.exists_transport_std D ψ₀ A V χ⁻¹ omh homh ν 𝓨 hν θ hθ κ
  have hWS : IsWeilSch (shift ψ₀ lam) χ θ V ν omS := by
    refine ⟨?_, ?_, ?_⟩
    · intro g a hg Φ x
      have := GlobalTheory.StdUnn.transport_levi D ψ₀ A V χ⁻¹ omh homh ν 𝓨 hν θ hθ μ' hsk κ hκ omS hS lam hl g a hg Φ x
      rw [inv_inv] at this
      exact this
    · intro g b hg Φ x
      exact GlobalTheory.StdUnn.Unip.transport_unip D ψ₀ A V χ⁻¹ omh homh ν 𝓨 hν θ hθ μ' hsk κ hκ omS hS lam hl g b hg Φ x
    · intro g hg Φ x
      exact GlobalTheory.StdUnn.WeylStd.main D ψ₀ A V χ⁻¹ omh homh ν 𝓨 hν θ hθ μ' hsk κ hκ omS hS lam hl g hg Φ x
  subst hsh
  obtain rfl := GlobalTheory.SiegelWeilLitCompare.isWeilSch_unique hω hWS
  exact ⟨ψ₀, μ', lam, κ, omh, h₀, hsk, hl, rfl, hκ, homh, hS⟩

end GlobalTheory.StdUnn.SchDatum

end
