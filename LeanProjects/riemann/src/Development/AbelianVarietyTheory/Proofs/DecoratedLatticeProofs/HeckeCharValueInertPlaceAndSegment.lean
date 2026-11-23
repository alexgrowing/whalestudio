import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
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

noncomputable section

namespace GlobalTheory.ChainOnto.InertValue

theorem npow_eq_zpow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (N : ℕ)
    (hN : Ideal.absNorm w.asIdeal = N ^ 2) (k : ℤ) (z : ℂ) (hz : 2 * z = k) :
    GlobalTheory.LFun.npow w z = (N : ℂ) ^ k := by
  have hlog : (Complex.log (N : ℂ) * ((2 : ℕ) : ℂ)).im = 0 := by
    rw [Complex.mul_im, Complex.log_im, Complex.log_re, ← Complex.ofReal_natCast N,
      Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)]
    simp
  rw [GlobalTheory.LFun.npow, hN, Nat.cast_pow, ← Complex.cpow_natCast (N : ℂ) 2,
    ← Complex.cpow_mul (x := (N : ℂ)) (y := ((2 : ℕ) : ℂ)) (z := z) (by rw [hlog]; linarith [Real.pi_pos]) (by rw [hlog]; linarith [Real.pi_pos])]
  rw [show ((2 : ℕ) : ℂ) * z = (k : ℂ) by rw [← hz]; norm_num, Complex.cpow_intCast]

theorem range_reflect (t : ℕ) : (Multiset.range t).map (fun i => t - 1 - i) = Multiset.range t := by
  refine (Multiset.Nodup.ext ?_ (Multiset.nodup_range t)).2 fun a => ?_
  · refine (Multiset.nodup_range t).map_on fun x hx y hy h => ?_
    rw [Multiset.mem_range] at hx hy
    omega
  · simp only [Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩; omega
    · intro ha; exact ⟨t - 1 - a, by omega, by omega⟩

end GlobalTheory.ChainOnto.InertValue

open GlobalTheory.ChainOnto.InertValue in

theorem GlobalTheory.ChainOnto.val_seg_of_isInertAt : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → Formalism.L2.Theta.ResEta D χ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → UnrAt χ w → val (F := D.host.F) χ w = (-1) ^ n ∧ ∀ (qu z : ℂˣ) (t : ℕ), (qu : ℂ) = qV D.host.F v → seg w z t = (GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str qu t).map (z * ·) := by
  intro D χ n _ hres v w hwv hw hu
  refine ⟨GlobalTheory.LFun.ResEta.val_of_isInertAt D.sp.cm.deg2 hres hw hu, ?_⟩
  intro qu z t hqu
  have hN : Ideal.absNorm w.asIdeal = qV D.host.F v ^ 2 := GlobalTheory.LFun.InertChart.absNorm_eq D.sp.cm.deg2 hw
  rw [GlobalTheory.LFun.seg, GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str, Int.toNat_natCast, Multiset.map_map, Finset.range_val]
  conv_lhs => rw [← range_reflect t, Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  simp only [Function.comp_apply]
  congr 1
  refine Units.ext ?_
  rw [GlobalTheory.LFun.coe_npowU, Units.val_zpow_eq_zpow_val, hqu]
  refine npow_eq_zpow w _ hN _ _ ?_
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring
