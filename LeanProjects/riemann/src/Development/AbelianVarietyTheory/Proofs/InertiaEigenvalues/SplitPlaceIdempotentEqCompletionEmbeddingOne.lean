import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemUniq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSelfDualLatticeIffIntegralFrameMatricesHalf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelAdaptedCharAbs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsIotaAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsComplMapEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdemSumMulOfSubset
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceModelIndicatorEqMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.IdemIota

set_option maxHeartbeats 800000 in

theorem toCompl_map_mem {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = q) (z : Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ intAE D) :
    GlobalTheory.LFun.toCompl h (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E) z)
      ∈ w.adicCompletionIntegers D.host.E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, rfl⟩ := hz
    have e2 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)
        (b ⊗ₜ[D.host.F] (x : D.host.E)) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q b ⊗ₜ[D.host.F] (x : D.host.E) :=
      Algebra.TensorProduct.map_tmul _ _ _ _
    rw [e2]
    exact GlobalTheory.LFun.InertChart.toCompl_mem h (GlobalTheory.AdelicU.tmul_mem_intLoc (hb q) x)
  | zero =>
    rw [map_zero (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)),
      map_zero (GlobalTheory.LFun.toCompl h)]
    exact (w.adicCompletionIntegers D.host.E).zero_mem
  | add y y' _ _ h1 h2 =>
    rw [map_add (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)),
      map_add (GlobalTheory.LFun.toCompl h)]
    exact (w.adicCompletionIntegers D.host.E).add_mem _ _ h1 h2
  | neg y _ h1 =>
    rw [map_neg (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E)),
      map_neg (GlobalTheory.LFun.toCompl h)]
    exact (w.adicCompletionIntegers D.host.E).neg_mem _ h1

theorem cw_mem_integers {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = q) {a : AE D} (ha : finPart D a ∈ intAE D) :
    GlobalTheory.Core.Rk.SWQ.cw h a ∈ w.adicCompletionIntegers D.host.E := by
  have e : GlobalTheory.Core.Rk.SWQ.cw h a = GlobalTheory.LFun.toCompl h
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F q) (AlgHom.id D.host.F D.host.E) (finPart D a)) := by
    show GlobalTheory.LFun.toCompl h (GlobalTheory.AdelicU.compFin D.host.F D.host.E q a) = _
    congr 1
    clear ha
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [e]
  exact toCompl_map_mem h _ ha

theorem idemAt_eq_iota_one : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P →
    ∀ ι : P.adicCompletion D.host.E →+ AE D,
      GlobalTheory.DivPtLocal.IsIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) ι → e = ι 1 := by
  intro D P e he ι hι
  obtain ⟨-, -, -, -, -, h6, -, -⟩ := hι
  have hq : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := rfl
  have hee : e * e = e := he.1.1
  have hec : e * cA D e = 0 := he.1.2.1
  have hne : e ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    have := (he.2 x hx0).1 hx
    rw [h0, zero_mul, map_zero] at this
    exact this (zero_mem _)
  have idem01 : ∀ a : AE D, a * a = a → GlobalTheory.Core.Rk.SWQ.cw hq a = 0 ∨ GlobalTheory.Core.Rk.SWQ.cw hq a = 1 := fun a ha =>
    IsIdempotentElem.iff_eq_zero_or_one.mp
      (by show GlobalTheory.Core.Rk.SWQ.cw hq a * GlobalTheory.Core.Rk.SWQ.cw hq a = GlobalTheory.Core.Rk.SWQ.cw hq a; rw [← map_mul, ha])
  have he' := GlobalTheory.ExportSeries.LatHalf.isIdemAt_conjPl he
  have hPP : Formalism.L2.DIV.conjPl P ≠ P := by
    intro hP
    rw [hP] at he'
    have h1 := GlobalTheory.Tow.idemAt_unique he' he
    apply hne
    rw [← hee]
    nth_rewrite 2 [← h1]
    exact hec
  obtain ⟨x, hxP, hxP'⟩ : ∃ x ∈ P.asIdeal, x ∉ (Formalism.L2.DIV.conjPl P).asIdeal := by
    by_contra hc
    push Not at hc
    exact hPP (HeightOneSpectrum.ext (P.isMaximal.eq_of_le (Formalism.L2.DIV.conjPl P).isPrime.ne_top hc)).symm
  have hx0 : x ≠ 0 := by rintro rfl; exact hxP' (Formalism.L2.DIV.conjPl P).asIdeal.zero_mem
  have hint : finPart D (cA D e * incA D ((x : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hc
    exact hxP' ((he'.2 x hx0).2 hc)
  have hc0 : GlobalTheory.Core.Rk.SWQ.cw hq (cA D e) = 0 := by
    have hm := cw_mem_integers hq hint
    rw [map_mul, GlobalTheory.Core.Rk.SecPar.cw_incA] at hm
    rcases idem01 (cA D e) (by rw [← map_mul, hee]) with h | h
    · exact h
    · exfalso
      have hv : Valued.v ((algebraMap D.host.E (HeightOneSpectrum.adicCompletion D.host.E P)) ((x : D.host.E))⁻¹)
          = HeightOneSpectrum.valuation D.host.E P ((x : D.host.E))⁻¹ :=
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
      rw [h, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers, hv] at hm
      have hv0 : HeightOneSpectrum.valuation D.host.E P (x : D.host.E) ≠ 0 := by simpa using hx0
      rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hv0), ← not_lt,
        HeightOneSpectrum.valuation_lt_one_iff_mem] at hm
      exact hm hxP
  have he0 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin (P.under (𝓞 D.host.F)) 1)) =
      e + cA D e := by
    rw [Formalism.IndefR.Fin.below_of_idemAt he]
    show _ = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (Formalism.IndefR.Fin.sglV _ 1))
    have hb : Formalism.IndefR.Fin.belowPl P = P.under (𝓞 D.host.F) := HeightOneSpectrum.ext rfl
    rw [hb]
    congr 2
  have h6e := h6 e
  rw [he0, add_mul, hee, mul_comm (cA D e) e, hec, add_zero, hc0, map_zero, map_zero, add_zero] at h6e
  rcases idem01 e hee with h | h
  · rw [h, map_zero] at h6e
    exact absurd h6e hne
  · rw [h] at h6e
    exact h6e

end GlobalTheory.IdemIota

end
