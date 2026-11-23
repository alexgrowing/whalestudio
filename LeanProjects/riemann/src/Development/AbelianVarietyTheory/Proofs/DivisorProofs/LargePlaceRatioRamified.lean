import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAbovePlaceOfTrivialUnits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamifiedOnLargePlaces

theorem chrEq_mul' {D : D7} {c c' : (AE D)ˣ →* Circle} {χ χ' : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ)
    (h' : ChrEq c' χ') : ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx]
    rfl

theorem not_unramAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ →
    ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∈ S1 D →
    ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  intro D T Lc sc G μ₀ hIs t v e he hv i j hU
  have hi1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have hi2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  set k := D.R.m - (i : ℕ) with hk
  have hμ : ChrEq (Lc.mu t ((j : ℕ) + 1)) (Lc.C.mu0 j * Lc.xiH t) := chrEq_mul' (hIs.mu0 j) (hIs.xi t)
  have hν : ChrEq (Lc.mu t ((j : ℕ) + 1) / G.ch.chi k) (Lc.C.mu0 j * Lc.xiH t * (G.ch.chiH k)⁻¹) := by
    rw [div_eq_mul_inv]; exact GlobalTheory.ChartQuot.chrEq_div hμ (G.ch.chi_eq k hi1 hi2)
  set P := G.pl.w v
  have hP : P.under (𝓞 D.host.F) = v := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inr hv))
  have hUnr := (GlobalTheory.LFun.unrAt_iff_of_chrEq hν P).1
    (GlobalTheory.UnrOverPlace.unrAt_of_unramAt D _ v e he hU P hP)
  apply (G.ch.lev1 k hi1 hi2 P (by rw [hP]; exact hv)).2
  intro x hx hxv
  have h1 := hUnr x hx
  have h2 := (Lc.C.isMu0 j).tame P x hx hxv
  have h3 := hIs.xi_tame t P x hx hxv
  have e1 : (Lc.C.mu0 j * Lc.xiH t * (G.ch.chiH k)⁻¹).loc P x =
      (Lc.C.mu0 j).loc P x * (Lc.xiH t).loc P x * ((G.ch.chiH k).loc P x)⁻¹ := rfl
  rw [e1, h2, h3, one_mul, one_mul, inv_eq_one] at h1
  exact h1

end GlobalTheory.RamifiedOnLargePlaces
