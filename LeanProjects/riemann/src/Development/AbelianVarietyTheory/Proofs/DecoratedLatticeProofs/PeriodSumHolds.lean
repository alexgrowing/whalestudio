import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupSemidirectProductRational
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicIteratedIntegrability
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.PerSumProof

variable {D : D7}

theorem conv {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {ρ : ℕ} (B : BesLev D ρ) {f : GA D B.V → ℂ}
    (hf : IsContAut B.V f) {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) :
    (∀ h, IntegrableOn (besFun ψ 1 B.d B.o B.ζ φ f h) B.vN.𝓝 B.vN.ν) ∧
      IntegrableOn (fun h => ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν) B.vA.𝓕 B.vA.μ := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
  haveI := B.vA.haar
  obtain ⟨K, hK, hcov⟩ := B.cpt
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V ρ B.d.e (isIsoSub_e B.d)).1
  obtain ⟨hemb, -, hnorm, -, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  have hch := GlobalTheory.MixPer.charLaws D ψ hψ.1 B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  have hfin : B.vA.μ B.vA.𝓕 < ⊤ := by
    refine GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ B.A) hK (fun g => ?_) B.vA.μ B.vA.fund
    obtain ⟨γ, hγ, hk⟩ := hcov g
    exact ⟨γ⁻¹, inv_mem hγ, γ * g, hk, by group⟩
  have hc : Continuous fun q : GA D B.A × flagN B.d => besFun ψ 1 B.d B.o B.ζ φ f q.1 q.2 :=
    ((hφ.2.comp continuous_fst).mul (hf.2.comp ((continuous_subtype_val.comp continuous_snd).mul
      (hemb.comp continuous_fst)))).mul ((hch.1 _).comp (continuous_subtype_val.comp continuous_snd)).star
  obtain ⟨M, hM⟩ := (hK.prod hK').exists_bound_of_continuousOn hc.continuousOn
  refine GlobalTheory.Per.FJConv.iterated_integrableOn hfin.ne (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top) hc (M := M)
    fun g n => ?_
  obtain ⟨γ, hγ, hk⟩ := hcov g
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹, hnorm n.1 n.2 γ⟩
  have e' : embA B.d B.o γ * n.1 * (embA B.d B.o γ)⁻¹ = γ'.1 * k'.1 := congrArg Subtype.val e
  have hδ : embA B.d B.o γ ∈ GQ B.V := by simpa using (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
  have hγ'Q : γ'.1 ∈ GQ B.V := hγ'
  have en : n.1 = (embA B.d B.o γ)⁻¹ * (γ'.1 * k'.1) * embA B.d B.o γ := by
    rw [← e']; group
  have e1 : besFun ψ 1 B.d B.o B.ζ φ f g n = besFun ψ 1 B.d B.o B.ζ φ f (γ * g) k' := by
    simp only [besFun]
    have f1 : f (n.1 * embA B.d B.o g) = f (k'.1 * embA B.d B.o (γ * g)) := by
      rw [← hf.1 ((embA B.d B.o γ)⁻¹ * γ'.1) (mul_mem (inv_mem hδ) hγ'Q) (k'.1 * embA B.d B.o (γ * g)), en, map_mul]
      congr 1; group
    have p1 : psiBes ψ B.d 1 (vecB B.o B.ζ) n.1 = psiBes ψ B.d 1 (vecB B.o B.ζ) k'.1 := by
      have := hch.2.2.1 (γ'.1 * k'.1) γ⁻¹
      rw [map_inv, inv_inv, ← en] at this
      rw [this, psiBes_mul B.d ψ 1 _ γ'.2 k'.2, hch.2.1 _ _ hγ'Q, one_mul]
    rw [f1, p1, hφ.1 γ hγ g]
  rw [e1]
  exact hM (γ * g, k') ⟨hk, hk'⟩

end GlobalTheory.SeeSaw.PerSumProof

namespace GlobalTheory.SeeSaw

theorem perSum_all : ∀ D : D7, PerSum D := by
  intro D ψ hψ ρ B f hf I s a φ hφ
  have hconv := fun i (hi : i ∈ s) => PerSumProof.conv hψ B hf (hφ i hi)
  simp only [BesLev.per, besPer]
  have e1 : ∀ h n, besFun ψ 1 B.d B.o B.ζ (∑ i ∈ s, a i • φ i) f h n =
      ∑ i ∈ s, a i * besFun ψ 1 B.d B.o B.ζ (φ i) f h n := by
    intro h n
    simp only [besFun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e1]
  have e2 : (fun h => ∫ n in B.vN.𝓝, ∑ i ∈ s, a i * besFun ψ 1 B.d B.o B.ζ (φ i) f h n ∂B.vN.ν) =
      fun h => ∑ i ∈ s, a i * ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ (φ i) f h n ∂B.vN.ν := by
    funext h
    rw [integral_finset_sum s fun i hi => ((hconv i hi).1 h).const_mul (a i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [e2, integral_finset_sum s fun i hi => (hconv i hi).2.const_mul (a i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

end GlobalTheory.SeeSaw

end
