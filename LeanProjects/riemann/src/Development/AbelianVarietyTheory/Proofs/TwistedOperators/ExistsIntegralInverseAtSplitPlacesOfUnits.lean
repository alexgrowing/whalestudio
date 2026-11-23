import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentPrimeProjectionCorrespondence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LocalInvIdem

theorem toEAf_surj {D : D7} (a : EAf D) : ∃ α : AE D, toEAf D α = a := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, by rw [RingHom.map_add, hp, hq]⟩
  | tmul x y => exact ⟨pairA D.host.F 0 y ⊗ₜ[D.host.F] x, rfl⟩

theorem inv_of_chart {D : D7} {ePP α : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (hC : GlobalTheory.SplitHecke.Chart ePP v π) {c : Fv D.host.F v} (hc : π α = c) (hv1 : Valued.v c = 1) :
    ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = ePP := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hv1; exact zero_ne_one hv1
  obtain ⟨t, ht⟩ := hC.1 c⁻¹
  refine ⟨ePP * t, ?_, ?_⟩
  · refine (hC.2.2.2 t).2 (GlobalTheory.SplitHecke.isInt_Ov.2 ?_)
    rw [ht, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
  · have h1 : π (α * t - 1) = 0 := by
      rw [map_sub, map_mul, ht, hc, mul_inv_cancel₀ hc0, map_one, sub_self]
    have h2 := (hC.2.1 _).1 h1
    linear_combination h2

theorem exists_local_inv {D : D7} {PP : Pl D.host.E} {ePP : AE D} (hPP : Formalism.L2.NTheta.IsIdemAt ePP PP)
    (α : AE D) (ha : toEAf D α ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hu : IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D α, ha⟩)) :
    ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = ePP := by
  obtain ⟨v, τ, hIdem, hP⟩ := GlobalTheory.SplitIdemDict.exists_emb hPP
  have hProj := (GlobalTheory.SplitIdemDict.isProjAt_iff τ PP).2 hP
  obtain ⟨⟨r, -, hr0, -, hrS⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v (splitProj τ) PP hProj
  obtain ⟨hC, hE, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v (splitProj τ) ePP hIdem
  obtain ⟨hmem, hrr⟩ := hrS (toEAf D α) ha
  obtain ⟨c, hc⟩ : ∃ c, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA (splitProj τ) α = c := ⟨_, rfl⟩
  have hcE := (hE α).trans hc
  have : Nontrivial (Formalism.L2.DIV.kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  have hv1 : Valued.v c = 1 := by
    have hle : Valued.v c ≤ 1 := by
      rw [← hcE]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hmem
    refine le_antisymm hle (not_lt.1 fun hlt => hu.ne_zero ?_)
    rw [← hrr]
    refine (hr0 _).2 ?_
    exact (congrArg Valued.v hcE).trans_lt hlt
  exact inv_of_chart hC hc hv1

theorem exists_inv : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (a : EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ Z, IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨a, ha⟩)) → ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, a * w * toEAf D e = toEAf D e := by
  intro D Z e he a ha hZ
  obtain ⟨α, rfl⟩ := toEAf_surj a
  obtain ⟨es, hes, hsum⟩ := he.1
  have key : ∀ PP ∈ Z, ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = es PP :=
    fun PP hPP => exists_local_inv (hes PP hPP) α ha (hZ PP hPP)
  choose! γ hγ1 hγ2 using key
  refine ⟨toEAf D (∑ PP ∈ Z, γ PP), GlobalTheory.IdemIntegral.toEAf_mem_of_finPart ?_, ?_⟩
  · rw [map_sum (finPart D)]; exact sum_mem fun PP hPP => hγ1 PP hPP
  · have hαw : α * ∑ PP ∈ Z, γ PP = e := by
      rw [Finset.mul_sum, hsum]; exact Finset.sum_congr rfl fun PP hPP => hγ2 PP hPP
    have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
    rw [← map_mul, ← map_mul, hαw, hee]

end GlobalTheory.LocalInvIdem
