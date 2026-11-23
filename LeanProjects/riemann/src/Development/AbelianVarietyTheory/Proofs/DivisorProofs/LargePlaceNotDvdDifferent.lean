import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NotDvdDiff

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop

namespace GlobalTheory.DiffSOne

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem not_dvd_diff_of_split (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {p : ℕ} (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L)).ncard = Module.finrank ℚ L)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 K) := by
  have h' : ({w : HeightOneSpectrum (𝓞 L) | ((p : ℕ) : 𝓞 L) ∈ w.asIdeal}).ncard = Module.finrank ℚ L := by
    rw [← h, Formalism.L2.SG.Pf.TypedLoc.primesOver_eq L hp]
    exact (Set.ncard_image_of_injective _ fun v w hvw => HeightOneSpectrum.ext hvw).symm
  obtain ⟨he, -⟩ := Formalism.L2.SG.Pf.TypedLoc.tower_ef K L hp h' v hv
  have hvq : v.asIdeal ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
    rw [Formalism.L2.SG.Pf.TypedLoc.primesOver_eq K hp]; exact ⟨v, hv, rfl⟩
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := hvq.2
  have : v.asIdeal.IsPrime := v.isPrime
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp)] at he
  rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain]
  exact he

theorem not_dvd_differentIdeal : ∀ {D : D7} (large₂ : SizeData₂ D), Rec large₂ → ∀ v : HeightOneSpectrum (𝓞 D.host.F), v ∈ S1 D →
    ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro D large₂ hR v hv
  obtain ⟨⟨Pm, -, -⟩, -⟩ := hR.size
  rcases (S1_mem_OmF D).1 hv with h | h | h | h
  · exact Formalism.L2.SG.Pf.FibD.not_dvd_diff v 0 h
  · exact Formalism.L2.SG.Pf.FibD.not_dvd_diff v 1 h
  · exact not_dvd_diff_of_split D.host.F D.host.E D.host.pde_prime Pm.pde_split.1 v h
  · exact not_dvd_diff_of_split D.host.F D.host.E D.host.pde'_prime Pm.pde_split.2 v h

end GlobalTheory.DiffSOne
