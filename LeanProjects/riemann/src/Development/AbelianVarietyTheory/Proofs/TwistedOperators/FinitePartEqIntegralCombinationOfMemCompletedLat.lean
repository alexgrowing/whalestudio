import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SrcLat
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryPairMapsCompletedHomLatticeOntoTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open Matrix

noncomputable section
namespace GlobalTheory.LatExpand

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

variable {D : D7}

theorem finPart_liftFin (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    finPart D (GlobalTheory.LatticeStable.liftFin D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a m => rfl

theorem toEAf_apply (w : Formalism.L2.Theta.AE D) :
    Formalism.IndefR.Datum.toEAf D w = Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D w) := rfl

theorem toEAf_liftFin (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    Formalism.IndefR.Datum.toEAf D (GlobalTheory.LatticeStable.liftFin D y) =
      Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E y := by
  rw [toEAf_apply, finPart_liftFin]

theorem toEAf_incA' (e : D.host.E) :
    Formalism.IndefR.Datum.toEAf D (incA D e) = Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F) e := rfl

theorem exists_integralCombination_of_mem_completedLattice {n : ℕ} (B : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (z : Fin n → Formalism.IndefR.Datum.EAf D) (hz : z ∈ Formalism.L2.Herm.hatL (F := D.host.F) B) :
    ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin n → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ B) ∧
      ∀ i, z i = Formalism.IndefR.Datum.toEAf D (∑ p, β p * incA D (b p i)) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine ⟨1, fun _ => 1, fun _ => c, fun _ => ?_, fun _ => hc, fun i => ?_⟩
    · exact (GlobalTheory.SplitDec.int_iff 1).2 (by rw [map_one]; exact one_mem _)
    · rw [Fin.sum_univ_one, one_mul, toEAf_incA']
  | zero =>
    refine ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, fun p => p.elim0, fun i => ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, map_zero]; rfl
  | add x y _ _ hx hy =>
    obtain ⟨m, β, b, hβ, hb, he⟩ := hx
    obtain ⟨m', β', b', hβ', hb', he'⟩ := hy
    refine ⟨m + m', Fin.append β β', Fin.append b b', fun p => ?_, fun p => ?_, fun i => ?_⟩
    · refine Fin.addCases (fun q => ?_) (fun q => ?_) p
      · rw [Fin.append_left]; exact hβ q
      · rw [Fin.append_right]; exact hβ' q
    · refine Fin.addCases (fun q => ?_) (fun q => ?_) p
      · rw [Fin.append_left]; exact hb q
      · rw [Fin.append_right]; exact hb' q
    · rw [Fin.sum_univ_add, map_add, Pi.add_apply, he i, he' i]
      simp only [Fin.append_left, Fin.append_right]
  | smul r x _ hx =>
    obtain ⟨m, β, b, hβ, hb, he⟩ := hx
    set y := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm (r : Formalism.IndefR.Datum.EAf D)
    have hy : Formalism.IndefR.Datum.toEAf D (GlobalTheory.LatticeStable.liftFin D y) = r := by
      rw [toEAf_liftFin, AlgEquiv.apply_symm_apply]
    have hyi : finPart D (GlobalTheory.LatticeStable.liftFin D y) ∈ intAE D :=
      (GlobalTheory.SplitDec.int_iff _).2 (by rw [hy]; exact r.2)
    refine ⟨m, fun p => GlobalTheory.LatticeStable.liftFin D y * β p, b, fun p => ?_, hb, fun i => ?_⟩
    · rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE hyi (hβ p)
    · simp only [mul_assoc, ← Finset.mul_sum, map_mul, hy]
      rw [Pi.smul_apply, he i, Subring.smul_def, smul_eq_mul]

theorem expand {n : ℕ} (B : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Y : Fin n → Formalism.L2.Theta.AE D)
    (hY : (fun i => Formalism.IndefR.Datum.toEAf D (Y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B) :
    ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin n → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ B) ∧
      ∀ i, finPart D (Y i) = finPart D (∑ p, β p * incA D (b p i)) := by
  obtain ⟨m, β, b, hβ, hb, he⟩ := exists_integralCombination_of_mem_completedLattice B _ hY
  refine ⟨m, β, b, hβ, hb, fun i => ?_⟩
  have h := he i
  rw [toEAf_apply, toEAf_apply] at h
  exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h

theorem finPart_eq_int_comb_of_mem_hatL : ∀ {D : D7} {n : ℕ} (B : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Y : Fin n → Formalism.L2.Theta.AE D),
    (fun i => Formalism.IndefR.Datum.toEAf D (Y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B →
    ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin n → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ B) ∧
      ∀ i, finPart D (Y i) = finPart D (∑ p, β p * incA D (b p i)) := fun B Y hY => expand B Y hY

end GlobalTheory.LatExpand
