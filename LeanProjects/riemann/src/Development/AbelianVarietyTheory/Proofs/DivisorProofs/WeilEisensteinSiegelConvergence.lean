import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilEisensteinSiegelConvergence
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilSchrodingerStandardUnnEvalZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec)

namespace GlobalTheory.WeilEisConv

theorem weilEisensteinSiegelConvergence : GlobalTheory.Published.WeilEisensteinSiegelConvergence := by
  intro D n V hn hV ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, _, _, hκ, hW, hT⟩ :=
    GlobalTheory.StdUnn.SchDatum.exists_datum D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have key : ∀ g : G D n, (ω g Φ).1 0 = swSec A V omh μ 𝓕 f (κ.symm g) := by
    intro g
    have h := hT (κ.symm g) f hf Φ hfΦ.symm
    have e : κ (κ.symm g) = g := κ.apply_symm_apply g
    rw [e] at h
    exact (congrFun h 0).trans (mixS_dblDec_zero A V ψ₀ μ 𝓕 _ 0)
  obtain ⟨a, ha⟩ := exists_isMaj A
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  obtain ⟨C, hC, h₁⟩ := GlobalTheory.SWAbsGrowth.norm_swSec_le hW hμ hf a ha
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hs : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hc.2.2.2, hc.2.2.2, star_star])
  have hP := GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ' hsk κ hκ
  have hG := GlobalTheory.StdUnn.chart_mem_GF_iff D A μ' hsk κ hκ
  have hb : (A.rank : ℝ) < (V.rank : ℝ) / 2 := by
    have : (2 * n : ℝ) < V.rank := by exact_mod_cast hV
    change (n : ℝ) < _
    linarith
  have hsum : Summable fun q : GlobalTheory.Eis.Cosets (P D n) (GF D n) =>
      (hgt A a (κ.symm (Subtype.val (q.out : GF D n))) : ℝ) ^ ((V.rank : ℝ) / 2) := by
    refine GlobalTheory.Eis.Conv.summable_hgt hc hs (GlobalTheory.Doubling.gram_hdbl A) (GlobalTheory.Doubling.isHermND_gram A)
      (GlobalTheory.Doubling.isCompact_Khat A a) hI (γ := fun q : GlobalTheory.Eis.Cosets (P D n) (GF D n) => κ.symm (Subtype.val (q.out : GF D n)))
      (fun q => (hG _).2 (by rw [MulEquiv.apply_symm_apply]; exact q.out.2)) (fun q q' h => ?_) hb
    have h' := (hP _).1 h
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
    rw [← q.out_eq, ← q'.out_eq]
    exact GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨q'.out * q.out⁻¹, h'⟩, inv_mul_cancel_right _ _⟩
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) (hsum.mul_left C)
  simp only [GlobalTheory.Eis.term, mul_one]
  rw [key]
  exact h₁ _

end GlobalTheory.WeilEisConv
