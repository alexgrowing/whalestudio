import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiQEqZeroOfNotMem
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

noncomputable section

namespace GlobalTheory.NrmVol

theorem phiQ_mul_conj_eq_indicator : ∀ (D : D7) (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ∀ (a b r : ℕ) (ξ : (kP PP)ˣ →* ℂˣ) (mu : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP mu ξ → ∀ x : Matrix (Fin b) (Fin a) (Fv D.host.F v), phiQ v r mu x * (starRingEnd ℂ) (phiQ v r mu x) = (GlobalTheory.NrmVol.suppQ v r).indicator (fun _ => (1 : ℂ)) x := by
  intro D PP v φ hP a b r ξ mu hL x
  by_cases hx : x ∈ GlobalTheory.NrmVol.suppQ v r
  · rw [Set.indicator_of_mem hx]
    have h : IsUnit (topL r x).det ∧ Valued.v (topL r x).det = 1 ∧
        (∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F) ∧
        ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1 := hx
    unfold phiQ
    rw [dif_pos h]
    obtain ⟨⟨red, -, -, hrel, -⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v φ PP hP
    set u := h.1.unit with hu
    have hv : Valued.v (u : Fv D.host.F v) = 1 := by rw [hu, IsUnit.unit_spec]; exact h.2.1
    have hvi : Valued.v ((u⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v) = 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
    have hint : (u : Fv D.host.F v) ∈ v.adicCompletionIntegers D.host.F :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hv.le
    have hint' : ((u⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v) ∈ v.adicCompletionIntegers D.host.F :=
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hvi.le
    have hunit : IsUnit (⟨(u : Fv D.host.F v), hint⟩ : v.adicCompletionIntegers D.host.F) :=
      ⟨⟨⟨_, hint⟩, ⟨_, hint'⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩, rfl⟩
    haveI : Finite (kP PP) := PP.asIdeal.finiteQuotientOfFreeOfNeBot PP.ne_bot
    set k := (hunit.map red).unit with hk
    have hR : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (u : Fv D.host.F v) (k : kP PP) :=
      (hrel _ _).2 ⟨hint, (IsUnit.unit_spec (hunit.map red)).symm⟩
    have hmu : mu u = ξ k := hL u k hR
    haveI : Finite (kP PP)ˣ := Finite.of_injective _ Units.val_injective
    obtain ⟨n, hn0, hn⟩ := (ξ.isOfFinOrder (isOfFinOrder_of_finite k)).exists_pow_eq_one
    have hpow : ((mu u : ℂˣ) : ℂ) ^ n = 1 := by
      rw [hmu, ← Units.val_pow_eq_pow_val, hn, Units.val_one]
    have hnorm : ‖((mu u : ℂˣ) : ℂ)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow hn0.ne'
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_inv, hnorm]
    norm_num
  · rw [Set.indicator_of_notMem hx, phiQ_eq_zero_of_not_mem v r mu x hx, zero_mul]

end GlobalTheory.NrmVol
