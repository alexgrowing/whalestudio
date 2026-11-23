import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TrivFlag

theorem isRatSec_lbPow_frob {Z : Scheme.{0}} [IsIntegral Z] {L : LB Z} {r : L.ι → Z.functionFieldˣ}
    (hr : IsRatSec L r) (τ : ℕ) : IsRatSec (lbPow L τ) fun c => r (c PUnit.unit) ^ τ :=
  fun c c' h => by
  have l : (lbPow L τ).U c ⊓ (lbPow L τ).U c' ≤ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have e : (lbPow L τ).g c c' = res l (L.g (c PUnit.unit) (c' PUnit.unit)) ^ τ := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rfl
  rw [e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    ← mul_pow, hr _ _ (l h)]
  exact congrArg (fun a => (a * _) ^ τ) (fnOf_resG l h _).symm

theorem regAt_pow_frob {Z : Scheme.{0}} [IsIntegral Z] {z : Z} {f : Z.functionField} (h : RegAt z f)
    (n : ℕ) : RegAt z (f ^ n) :=
  have ⟨a, ha⟩ := h; ⟨a ^ n, by rw [map_pow, ha]⟩

theorem unitAt_pow_frob {Z : Scheme.{0}} [IsIntegral Z] {z : Z} {f : Z.functionField} (h : UnitAt z f)
    (n : ℕ) : UnitAt z (f ^ n) :=
  have ⟨a, ha, e⟩ := h; ⟨a ^ n, ha.pow n, by rw [map_pow, e]⟩

theorem flagOfTriv_frob : ∀ (p : ℕ), p.Prime → ∀ (Z : Scheme.{0}) [IsIntegral Z], (p : Γ(Z, ⊤)) = 0 →
    ∀ (N : ℕ) (g : Fin N → Pic Z), FlagOfTriv g → FlagOfTriv fun i => p • g i := by
  intro p hp Z _ hpZ N g hg
  obtain ⟨G, hG, r, A, hcls, hr, hB⟩ := hg
  haveI := Fact.mk hp
  have hpK : (p : Z.functionField) = 0 := by
    rw [← map_natCast (algebraMap Γ(Z, ⊤) Z.functionField), hpZ, map_zero]
  haveI : CharP Z.functionField p := (CharP.charP_iff_prime_eq_zero hp).2 hpK
  let φ := frobenius Z.functionField p
  have hφ : ∀ x, φ x = x ^ p := fun x => frobenius_def _ _
  refine ⟨fun i => lbPow (G i) p, fun i => LB.isLB_linComb (hG i) _ _,
    fun i c => r i (c PUnit.unit) ^ p, A.map φ, fun i => ?_, fun i => isRatSec_lbPow_frob (hr i) p,
    fun z => ?_⟩
  · rw [cls_lbPow (hG i), hcls i]
  · obtain ⟨B, hBt, hreg, hdet, hu⟩ := hB z
    refine ⟨B.map φ, hBt.map φ, fun a b => ?_, ?_, fun i c hc => ?_⟩
    · rw [← Matrix.map_mul, Matrix.map_apply, hφ]
      exact regAt_pow_frob (hreg a b) p
    · rw [← Matrix.map_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hφ]
      exact unitAt_pow_frob hdet p
    · have hc' : z ∈ (G i).U (c PUnit.unit) := Set.mem_iInter.1 hc PUnit.unit
      rw [Matrix.map_apply, hφ, Units.val_pow_eq_pow_val, ← mul_pow]
      exact unitAt_pow_frob (hu i (c PUnit.unit) hc') p

end GlobalTheory.TrivFlag

end
