import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompFinIdemSum

variable {D : D7}

theorem compFin_tensAt_ne {u v : HeightOneSpectrum (𝓞 D.host.F)} (h : u ≠ v)
    (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    compFin D.host.F D.host.E u (GlobalTheory.EmbChart.tensAt D.host.E v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    rw [GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]
    have h0 : evFin D.host.F u (pairA D.host.F 0 (singleFin v a)) = 0 := evalV_singleFin_ne h a
    have h1 : compFin D.host.F D.host.E u (pairA D.host.F 0 (singleFin v a) ⊗ₜ[D.host.F] x) =
        evFin D.host.F u (pairA D.host.F 0 (singleFin v a)) ⊗ₜ[D.host.F] x :=
      Algebra.TensorProduct.map_tmul ..
    rw [h1, h0, TensorProduct.zero_tmul]
  | add y z hy hz => simp only [map_add, hy, hz, add_zero]

set_option maxHeartbeats 1000000 in
open Classical in

theorem compFin_add_cA_eq_one : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ PP ∈ Z,
    compFin D.host.F D.host.E (PP.under (𝓞 D.host.F)) (e + cA D e) = 1 := by
  intro D Z e he PP hPP
  classical
  obtain ⟨⟨es, hes, rfl⟩, hcc⟩ := he
  obtain ⟨v0, τ0, -, hPP0⟩ := GlobalTheory.SplitIdemDict.exists_emb (hes PP hPP)
  have hu : PP.under (𝓞 D.host.F) = v0 := by rw [hPP0]; exact splitPrime_under τ0
  rw [hu]
  have key : ∀ Q ∈ Z, compFin D.host.F D.host.E v0 (es Q) =
      (if Q = PP then splitIdem (isCMExt_host D) τ0 else 0) +
        (if Q = splitPrime (τ0.comp D.sp.cm.sig) then 1 - splitIdem (isCMExt_host D) τ0 else 0) := by
    intro Q hQ
    obtain ⟨v, τ, hI, hQτ⟩ := GlobalTheory.SplitIdemDict.exists_emb (hes Q hQ)
    have hQv : Q.under (𝓞 D.host.F) = v := by rw [hQτ]; exact splitPrime_under τ
    rw [GlobalTheory.SplitIdemDict.eq_idem hI, GlobalTheory.EmbChart.idem]
    by_cases hv : v = v0
    · subst hv
      rcases eq_or_eq_comp_conj (isCMExt_host D) τ0 τ with h | h <;> rw [h] at hQτ ⊢
      · rw [if_pos (hQτ.trans hPP0.symm), if_neg (by rw [hQτ]; exact (splitPrime_comp_ne (isCMExt_host D) τ0).symm),
          add_zero]
        exact GlobalTheory.EmbChart.compFin_tensAt _ _
      · rw [if_neg (by rw [hQτ, hPP0]; exact splitPrime_comp_ne (isCMExt_host D) τ0), if_pos hQτ, zero_add,
          GlobalTheory.EmbChart.compFin_tensAt, splitIdem_comp]
    · have h1 : Q ≠ PP := fun h => hv (by rw [← hQv, h, hu])
      have h2 : Q ≠ splitPrime (τ0.comp D.sp.cm.sig) := fun h => hv (by rw [← hQv, h]; exact splitPrime_under _)
      rw [if_neg h1, if_neg h2, add_zero]
      exact compFin_tensAt_ne (Ne.symm hv) _
  have hsum : compFin D.host.F D.host.E v0 (∑ Q ∈ Z, es Q) = splitIdem (isCMExt_host D) τ0 +
      (if splitPrime (τ0.comp D.sp.cm.sig) ∈ Z then 1 - splitIdem (isCMExt_host D) τ0 else 0) := by
    rw [map_sum, Finset.sum_congr rfl key]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos hPP]
  have hc : compFin D.host.F D.host.E v0 (cA D (∑ Q ∈ Z, es Q)) =
      sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v0 (∑ Q ∈ Z, es Q)) :=
    (GlobalTheory.SplitIdemDict.compFin_cA _).symm
  have h1 : ∀ a : Fv D.host.F v0 ⊗[D.host.F] D.host.E, a + (1 - a) = 1 := fun a => by abel
  rw [map_add, hc, hsum]
  by_cases hP' : splitPrime (τ0.comp D.sp.cm.sig) ∈ Z
  · exfalso
    have hz := congrArg (compFin D.host.F D.host.E v0) hcc
    rw [map_mul, hc, hsum, if_pos hP', h1, map_one, mul_one, map_zero] at hz
    have h3 := congrArg (fun y => splitProj τ0 y) hz
    simp only [map_one, map_zero] at h3
    exact one_ne_zero h3
  · rw [if_neg hP', add_zero, sigR_splitIdem, h1]

end GlobalTheory.CompFinIdemSum

end
