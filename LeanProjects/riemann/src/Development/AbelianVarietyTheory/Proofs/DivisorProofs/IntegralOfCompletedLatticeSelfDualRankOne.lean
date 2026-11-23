import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IpEqZeroOfHeisEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterFiniteIdeleValueEq

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.CosetOrth

variable {D : D7}

theorem hO_single_of_gram_one {S T : HSp D} (hS : S.gram = 1) (hT : T.gram = 1) (p : Fin T.rank) (q : Fin S.rank)
    (x : AE D) (y : WO S T) : hO S T (Matrix.single p q x) y = cA D (y p q) * x := by
  unfold hO
  rw [hS, hT, inv_one, Finset.sum_eq_single q, Finset.sum_eq_single q, Finset.sum_eq_single p, Finset.sum_eq_single p]
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.single_apply_same, map_one, one_mul, mul_one]
  · intro b _ hb; simp [Matrix.one_apply_ne hb.symm]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun d _ => ?_
    by_cases h : d = p
    · subst h; simp [Matrix.one_apply_ne hb]
    · simp [Matrix.single_apply_of_row_ne (Ne.symm h)]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [Matrix.one_apply_ne hb.symm]
  · exact fun h => absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [Matrix.single_apply_of_col_ne _ _ (Ne.symm hb)]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem fe_incA_mul (a : D.host.E) (z : AE D) : fe D (incA D a * z) = algebraMap D.host.E (FA D) a * fe D z := by
  rw [map_mul, fe_apply (incA D a), GlobalTheory.LatVac.finPart_incA, GlobalTheory.FinIdlRead.finAdEquiv_one_tmul]

theorem inHat_one_fe_iff (z : AE D) : InHat 1 (fe D z) ↔ finPart D z ∈ intAE D := by
  rw [inHat_one_iff, GlobalTheory.FinIdlRead.mem_intAE_iff_finAdEquiv]
  rfl

theorem inHat_of_char_dual : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : D.host.E) (LB : Lat T) (n : ℕ), IsStdChar D ψ (-1) →
  S.gram = 1 → T.gram = 1 → IsSelfDualC S (stdLat S) → IsSelfDualC T LB → r ≠ 0 →
  (∀ u ∈ (latO S T (stdLat S) LB fun _ => True), HatPt ((n : D.host.E) * r) 1 u) →
  ∀ (p : Fin T.rank) (q : Fin S.rank) (c : AE D), infPart D c = 0 →
  (∀ t : AE D, infPart D t = 0 → InHat 1 (fe D t) →
    ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D (star r⁻¹) * (t * c)))) = 1) →
  InHat 1 (algebraMap D.host.E (FA D) ((n : D.host.E) * n * r) * fe D c) := by
  intro D ψ S T r LB n hψ hS hT hΛS hΛT hr hL p q c hc h
  have hmem : (Matrix.single p q (incA D (n : D.host.E) * c) : WO S T) ∈
      latO S T (stdLat S) LB fun _ => True := by
    refine GlobalTheory.LatVac.mem_of_char hψ hΛS hΛT ?_ fun u' hu' => ?_
    · rw [Matrix.map_single, map_mul, hc, mul_zero, Matrix.single_zero]
    · obtain ⟨h0, h1⟩ := hL u' hu'
      have h0' : infPart D (u' p q) = 0 := congrFun (congrFun h0 p) q
      have ht := h (cA D (incA D ((n : D.host.E) * r) * u' p q))
        (by rw [(GlobalTheory.IdemSupport.parts_cA _).1, map_mul, h0', mul_zero, map_zero])
        (by
          rw [inHat_one_fe_iff]
          refine GlobalTheory.IdemSupport.finPart_cA_mem ?_
          rw [← inHat_one_fe_iff, fe_incA_mul]
          exact h1 p q)
      have e : incA D (star r⁻¹) * (cA D (incA D ((n : D.host.E) * r) * u' p q) * c) =
          cA D (u' p q) * (incA D (n : D.host.E) * c) := by
        have e1 : incA D (star r⁻¹) * incA D (star ((n : D.host.E) * r)) = incA D (n : D.host.E) := by
          rw [← map_mul, ← star_mul, mul_assoc, mul_inv_cancel₀ hr, mul_one, star_natCast]
        rw [map_mul, GlobalTheory.IdemSupport.cA_incA, ← e1]
        ring
      rw [e] at ht
      unfold symplO
      rw [hO_single_of_gram_one hS hT]
      exact ht
  have h2 := (hL _ hmem).2 p q
  rw [Matrix.single_apply_same, fe_incA_mul, ← mul_assoc, ← map_mul] at h2
  rw [mul_right_comm]
  exact h2

end GlobalTheory.CosetOrth
