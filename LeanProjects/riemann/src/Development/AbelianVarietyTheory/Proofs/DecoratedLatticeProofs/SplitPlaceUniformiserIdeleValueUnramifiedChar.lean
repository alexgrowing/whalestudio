import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
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

namespace GlobalTheory.SplitUnifIdele

theorem value_eq_val : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsSplit (E := D.host.E) v → ∀ χ : (AE D)ˣ →* Circle, UnrAt χ w → ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ), Formalism.L2.NTheta.IsIdemAt e w ∧ ϖ ∈ w.asIdeal ∧ ϖ ∉ w.asIdeal ^ 2 ∧ (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) ∧ ∀ χ' : (AE D)ˣ →* Circle, UnrAt χ' w → ((χ' x : Circle) : ℂ) = ((val (F := D.host.F) χ' w : ℂˣ) : ℂ) := by
  intro D v w hw hs χ _
  obtain ⟨e, he⟩ := GlobalTheory.WeilAtPlace.exists_isIdemAt_of_split hs hw
  have hP : IsPrimeIdem w e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have hee : e * e = e := he.1.1
  have hlt : w.asIdeal ^ 2 < w.asIdeal ^ 1 :=
    Ideal.pow_right_strictAnti w.asIdeal w.ne_bot w.isPrime.ne_top (by norm_num : 1 < 2)
  rw [pow_one] at hlt
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt hlt
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0
    exact h2 (by rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h0]; exact zero_mem _)
  have hab : incA D (ϖ : D.host.E) * incA D ((ϖ : D.host.E)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hϖ0, map_one]
  have hba : incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) = 1 := by
    rw [mul_comm]; exact hab
  let x : (AE D)ˣ := ⟨e * incA D (ϖ : D.host.E) + (1 - e), e * incA D ((ϖ : D.host.E)⁻¹) + (1 - e),
    by linear_combination (incA D (ϖ : D.host.E) * incA D ((ϖ : D.host.E)⁻¹) - incA D (ϖ : D.host.E)
      - incA D ((ϖ : D.host.E)⁻¹) + 1) * hee + e * hab,
    by linear_combination (incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) - incA D (ϖ : D.host.E)
      - incA D ((ϖ : D.host.E)⁻¹) + 1) * hee + e * hba⟩
  refine ⟨e, ϖ, x, he, h1, h2, rfl, fun χ' hχ' => ?_⟩
  obtain ⟨y, hy, hxy⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hP)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem hP) x (by
      change e * (e * incA D (ϖ : D.host.E) + (1 - e) - 1) = e * incA D (ϖ : D.host.E) + (1 - e) - 1
      linear_combination (incA D (ϖ : D.host.E) - 1) * hee)
  have hy' : (y : w.adicCompletion D.host.E) = algebraMap D.host.E _ (ϖ : D.host.E) := by
    rw [hy, show (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) from rfl,
      GlobalTheory.WeilAtPlace.compAt_cut (GlobalTheory.LFun.finPart_of_isPrimeIdem hP), GlobalTheory.LFun.compAt_incA]
  have hu : Formalism.L2.Host.IsUnifAt w y := by
    unfold Formalism.L2.Host.IsUnifAt
    rw [hy']
    exact (Formalism.UG.P.levelaf_valued_algebraMap _ _).trans
      (GlobalTheory.LFun.EulerTie.valuation_of_mem_notMem_sq w h1 h2)
  have := hχ'.locChar_eq_val hu
  rw [← this, hxy]
  rfl

end GlobalTheory.SplitUnifIdele

end
