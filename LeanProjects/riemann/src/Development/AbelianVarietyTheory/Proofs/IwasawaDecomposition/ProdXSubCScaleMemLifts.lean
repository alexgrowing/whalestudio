import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlocksUnique
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistLift

open Polynomial

theorem prod_X_sub_C_scale_mem_lifts {K : Type} [Field K] (f : K →+* ℂ) (M : Multiset ℂ) (y : K)
    (hy : f y ≠ 0) (h : (M.map (fun α => X - C α)).prod ∈ Polynomial.lifts f) :
    ((M.map (fun x => x * f y)).map (fun α => X - C α)).prod ∈ Polynomial.lifts f := by
  set q : ℂ[X] := C (f y)⁻¹ * X with hq
  have key : ((M.map (fun x => x * f y)).map (fun α => X - C α)).prod =
      C (f y) ^ Multiset.card M * ((M.map (fun α => X - C α)).prod).comp q := by
    clear h
    induction M using Multiset.induction_on with
    | empty => simp
    | cons a M ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, ih, mul_comp]
      have e1 : (X - C a).comp q = C (f y)⁻¹ * X - C a := by simp [hq]
      have e2 : X - C (a * f y) = C (f y) * (C (f y)⁻¹ * X - C a) := by
        rw [mul_sub, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hy, C_1, one_mul, ← C_mul, mul_comm (f y) a]
      rw [e1, e2]; ring
  rw [key]
  refine mul_mem (pow_mem (Polynomial.C_mem_lifts f y) _) ?_
  rw [Polynomial.lifts_iff_set_range] at h ⊢
  obtain ⟨p, hp⟩ := h
  refine ⟨p.comp (C y⁻¹ * X), ?_⟩
  rw [Polynomial.map_comp, hp, hq]
  simp [map_inv₀]

end GlobalTheory.TwistLift

namespace GlobalTheory.TwistLift

open Polynomial

theorem galPol_lifts_tw_etaTinv : ∀ (D : D7) (cf : CharFrame D), GlobalTheory.HeightCounting.CharSide D cf → ValLL0 D cf → ∀ π : D.naut.CG D.R.r, (∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D)) → ∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) ((1 - (D.R.nV : ℝ)) / 2)) ∈ Polynomial.lifts (embLL0 D) := by
  intro D cf hC hV π hπ
  obtain ⟨k, hk⟩ := D.R.t_odd
  filter_upwards [hπ, D.naut.locG_unr_ae π] with w hw hu
  have hUe : cf.eta.UnrAt w := by
    have h1 := (hC.unr_iff D.naut.etaT w).1 (D.naut.etaT_unr w)
    rwa [hC.etaT] at h1
  have hFe : D.naut.frobEig (D.naut.locG D.naut.etaT w) = {((cf.eta.val w : ℂ))⁻¹} := by
    have h1 := hC.frob D.naut.etaT w (by rw [hC.etaT]; exact hUe)
    rw [h1, hC.etaT]; simp
  have hFi : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {(cf.eta.val w : ℂ)} := by
    rw [(D.naut.etaTinv_def w).2, hFe]; simp
  have hUi : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hD1 : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ w
  obtain ⟨y, hy⟩ := hV.eta w hUe
  have hNv : Formalism.ConjugateSelfDual.normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hN : ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ≠ 0 := by
    rw [hNv, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  set N : ℂ := ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) with hNdef
  set lam : D.LL0 := y * (((Formalism.ConjugateSelfDual.normV w : ℕ) : D.LL0) ^ k)⁻¹ with hlamdef
  have hlam : embLL0 D lam = (cf.eta.val w : ℂ) * N ^ (-(1 / 2 : ℂ)) * (N ^ k)⁻¹ := by
    rw [hlamdef, map_mul, map_inv₀, map_pow, map_natCast, hy, Formalism.L2.Host.HChar.valTw, hNdef, hNv]
    push_cast; ring
  have hlam0 : embLL0 D lam ≠ 0 := by
    rw [hlam]
    refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) ?_) (inv_ne_zero (pow_ne_zero _ hN))
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hmul : D.naut.frobEig (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) ((1 - (D.R.nV : ℝ)) / 2)) =
      (D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map (fun x => x * embLL0 D lam) := by
    rw [D.naut.locG_tw, D.naut.frobEig_tw _ _ (D.naut.unr_char _ _ hD1 hu hUi),
      D.naut.frobEig_char _ _ _ hu hUi hD1 hFi, D.naut.frobEig_tw _ _ hu, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun x _ => ?_)
    simp only [Function.comp_apply]
    have hs : (((1 - (D.R.nV : ℝ)) / 2 : ℝ) : ℂ) = (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) + (-(1 / 2 : ℂ)) + (-(k : ℂ)) := by
      have e : D.R.nV = D.R.r + D.R.t := rfl
      rw [e, hk]; push_cast; ring
    rw [hlam, ← hNdef, hs, Complex.cpow_add _ _ hN, Complex.cpow_add _ _ hN, Complex.cpow_neg (x := N) (y := (k : ℂ)),
      Complex.cpow_natCast]
    ring
  have hw' := hw
  simp only [galPol] at hw' ⊢
  rw [hmul]
  exact prod_X_sub_C_scale_mem_lifts (embLL0 D) _ lam hlam0 hw'

end GlobalTheory.TwistLift
