import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)

noncomputable section

namespace GlobalTheory.UnrPlDict

open GlobalTheory.IdemSupport

variable {D : D7}

theorem exists_glue_kill {χ : (AE D)ˣ →* Circle} {w : HeightOneSpectrum (𝓞 D.host.E)} (hu : UnrAt χ w)
    {e : AE D} (hd : GlobalTheory.IdemSupport.IsDelta (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) w e)
    (x : (AE D)ˣ) (h1 : finPart D (x : AE D) ∈ intAE D) (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) :
    ∃ y : (AE D)ˣ, (y : AE D) = e * (x : AE D) + (1 - e) ∧ χ y = 1 := by
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  have hm : GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E (x : AE D) w *
      GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E ((x⁻¹ : (AE D)ˣ) : AE D) w = 1 := by
    rw [← ev_mul, Units.mul_inv, map_one]
    try rfl
  let u : (w.adicCompletion D.host.E)ˣ :=
    ⟨_, _, hm, by rw [mul_comm]; exact hm⟩
  have hU : Formalism.L2.Host.IsUnitAt w u := by
    rw [GlobalTheory.LFun.EulerTie.isUnitAt_iff]
    exact ⟨(hΦ.int _).1 h1 w, (hΦ.int _).1 h2 w⟩
  refine ⟨GlobalTheory.LFun.locIdele D.host.F w u, (GlobalTheory.LFun.EulerTie.glue_eq_locIdele hd rfl).symm, ?_⟩
  have := congrArg (fun z : ℂˣ => (z : ℂ)) (hu u hU)
  exact Circle.ext this

theorem unrPl_of_unrAt : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)),
    w.under (𝓞 D.host.F) = v → ∀ χ : (AE D)ˣ →* Circle,
    (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χ w') → UnrPl w χ := by
  intro D v w hw χ hχ e f hp x hx h1 h2
  have hΦ : Comp D (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) := by
    obtain ⟨a, b, c, d, e⟩ := (GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E))
    exact ⟨a, b, c, d, e⟩
  have hd := (of_isPrimeIdem hΦ hp).1
  rcases hp with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
  · have hd' := delta_conj hΦ hd
    obtain ⟨y, hy, hy1⟩ := exists_glue_kill (hχ w hw) hd x h1 h2
    obtain ⟨z, hz, hz1⟩ := exists_glue_kill (hχ (cP w) ((under_cP w).trans hw)) hd' x h1 h2
    have ho : e * cA D e = 0 := hi.1.2.1
    have e1 : x = y * z := Units.ext (by
      rw [Units.val_mul, hy, hz]
      linear_combination (-1 : AE D) * hx - ((x : AE D) - 1) ^ 2 * ho)
    rw [e1, map_mul, hy1, hz1, one_mul]
  · obtain ⟨y, hy, hy1⟩ := exists_glue_kill (hχ w hw) hd x h1 h2
    have e1 : x = y := Units.ext (by rw [hy]; linear_combination (-1 : AE D) * hx)
    rw [e1, hy1]

end GlobalTheory.UnrPlDict

end
