import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGoodIndexNormalizationNegativeInert
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Hilbert90FiniteIdelesCongruence
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NatCastMemOfPrimeDvdAbsNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinZeta.SplitNorm

theorem natCast_mem_of_dvd_absNorm {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ}
    (hq : q.Prime) (hd : q ∣ Ideal.absNorm w.asIdeal) : (q : 𝓞 K) ∈ w.asIdeal := by
  first
  | exact @_root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm
  | exact _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm
  | (apply _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastMemOfPrimeDvdNorm.natCast_mem_of_prime_dvd_absNorm ..)

theorem conj_smul_ne_of_isSplit (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w.under (𝓞 D.host.F) = v) (hv : IsSplit (E := D.host.E) v) : D.host.conj • w.asIdeal ≠ w.asIdeal := by
  intro hfix
  set c := GlobalTheory.Member.cF D
  have hcc : ∀ x : D.host.E, c x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hself : GlobalTheory.Mem.Chr.ConjPl c.toRingEquiv w w := by
    rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
    rw [hy]
    conv_rhs => rw [← hfix]
    exact Ideal.smul_mem_pointwise_smul_iff.symm
  have key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v → u = w := fun u hu =>
    ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl c D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D) w u).1 (hu.trans hw.symm)).elim id
      fun h => (GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h hself
  obtain ⟨w₁, w₂, hne, h₁, h₂⟩ := GlobalTheory.LFun.isSplit_iff.1 hv
  exact hne ((key w₁ h₁).trans (key w₂ h₂).symm)

theorem lam_qV_pow (D : D7) (lam : ℕ →* ℂ)
    (hlam : ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w.under (𝓞 D.host.F) = v)
    (hv : IsSplit (E := D.host.E) v) (m : ℕ) :
    lam (qV D.host.E w ^ m) = (Real.sqrt ((qV D.host.E w ^ m : ℕ) : ℝ) : ℂ) := by
  apply hlam
  · exact pow_ne_zero _ fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · intro q hq hi hd
    have hmem := natCast_mem_of_dvd_absNorm w hq (hq.dvd_of_dvd_pow hd)
    refine conj_smul_ne_of_isSplit D v w hw hv (hi w.asIdeal w.isPrime w.ne_bot hmem)

end GlobalTheory.FinZeta.SplitNorm
