import Mathlib
import Development.AutomorphicArithmetic.OrbitLabellings.ColDefs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalRingCardinality.DataForced
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstUnitaryLogarithmicCoordinatesStatement
import Development.AutomorphicArithmetic.OrbitLabellings.ExistsUnitQuotientOfNormOneUnramifiedUltrametric
import Development.AutomorphicArithmetic.OrbitLabellings.IntegralMvExpSumLogSOfOddPeriod
import Development.AutomorphicArithmetic.OrbitLabellings.StdSeriesOrbitCoordinateChangeOfOddInert

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd UpperTheory.G2 Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace UpperTheory.LinearSubstitutionRepresentatives

private lemma exists_reps {Lt : Type} [Fintype Lt] {i : ℕ} [NeZero i] {pos : Lt → ℕ → Lt} (hp : IsPos i pos) :
    ∃ R : Finset Lt, ∀ z, ∃! r, r ∈ R ∧ ∃ e : ℕ, pos r e = z := by
  have hmul : ∀ z k, pos z (i * k) = z := fun z k => by
    induction k with
    | zero => rw [mul_zero, hp.zero]
    | succ k ih => rw [mul_add, mul_one, ← hp.add, ih, hp.period]
  let S : Setoid Lt :=
    { r := fun a b => ∃ e : ℕ, pos a e = b
      iseqv :=
        { refl := fun a => ⟨0, hp.zero a⟩
          symm := by
            rintro a _ ⟨e, rfl⟩
            obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne i)
            refine ⟨j * e, ?_⟩
            rw [hp.add, show e + j * e = i * e by rw [hj, Nat.succ_mul, add_comm], hmul]
          trans := by
            rintro a _ _ ⟨e, rfl⟩ ⟨f, rfl⟩
            exact ⟨e + f, (hp.add a e f).symm⟩ } }
  refine ⟨Finset.univ.image fun z => (Quotient.mk S z).out, fun z => ⟨(Quotient.mk S z).out,
    ⟨Finset.mem_image.2 ⟨z, Finset.mem_univ _, rfl⟩, Quotient.mk_out (s := S) z⟩, ?_⟩⟩
  rintro r ⟨hr, hz⟩
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hr
  have h : Quotient.mk S (Quotient.mk S w).out = Quotient.mk S z := Quotient.sound hz
  rw [Quotient.out_eq] at h
  rw [h]

private lemma subst_lin_comp {K n m τ : Type} [Field K] [Fintype n] [Fintype m] (γ : n → m → K)
    (a : m → MvPowerSeries τ K) (ha : ∀ e, MvPowerSeries.constantCoeff (a e) = 0) (Θ : MvPowerSeries n K) :
    (MvPowerSeries.subst (fun k => (∑ e, MvPowerSeries.C (γ k e) * a e : MvPowerSeries τ K)) Θ : MvPowerSeries τ K) =
      MvPowerSeries.subst a (MvPowerSeries.subst
        (fun k => (∑ e, MvPowerSeries.C (γ k e) * MvPowerSeries.X e : MvPowerSeries m K)) Θ : MvPowerSeries m K) := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp) hs]
  congr 1
  funext k
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hs, MvPowerSeries.subst_C]

private lemma cc_linS {K K0 Lt β : Type} [Field K] [Field K0] (j : K0 →+* K) (σ : K0 →+* K0) (i : ℕ) [NeZero i]
    (pos : Lt → ℕ → Lt) (c : K0) (r : Lt) (b : β) : MvPowerSeries.constantCoeff (linS j σ i pos c r b) = 0 := by
  unfold linS
  rw [map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  split_ifs <;> simp

end UpperTheory.LinearSubstitutionRepresentatives

open UpperTheory.LinearSubstitutionRepresentatives in
theorem UpperTheory.lattice_pairs_odd_degree_isometric :
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime]
    (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → 5 ≤ p → IsResidueClassZero D p → ∀ [NeZero (nP D p)], Odd (nP D p) →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
    admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' →
    ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → HasThetaProductForm p (nP D p) (posPl D p) (stdSer D lam (fun _ => 1) P P' G) := by
  intro D cc δ B χ p _ lam hHost h5 hC _ hi N N' L L' P P' hAdm hS hS' G hG
  obtain ⟨c, g2, g3, s2, ε, σ, F, hc, hcd, hfam⟩ := hHost
  obtain ⟨r, b, hLB, hON, hInt⟩ := hfam N N' L L' hAdm
  have hσ : UnrOK (MaximalUnramifiedExtension p) p σ := hcd.2.2.2.2.2.1
  have hp : IsPos (nP D p) (posPl D p) := ⟨posPl_zero D p, posPl_add D p, posPl_period D p⟩
  obtain ⟨om, hOw, hTr⟩ := UpperTheory.exists_unit_quotient_of_normOne_unramified_ultrametric p h5 σ hσ (nP D p) hi
  obtain ⟨R, hR⟩ := exists_reps hp
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := UpperTheory.stdSeries_orbit_coordinate_change_of_odd_inert D p lam σ hσ h5 hC hi om hOw hTr R hR N N' L L' P P' hAdm hS hS' r b hLB hON
  have hU := GlobalTheory.T.subst_unitary_logarithmic_coordinates p g2 g3 s2 ε σ F hcd (Fin r) (({z // z ∈ R} × Fin (nP D p)) × Fin N × Fin N') γ hγ1
    (by convert hγ2) _ (hInt G hG)
  refine UpperTheory.integral_mvExp_sum_logS_of_odd_period p g2 g3 s2 ε σ F hcd (nP D p) hi om hOw hTr _ _ (posPl D p) hp R _ hU c _ hc ?_
  exact (hγ3 c G).trans (subst_lin_comp (fun k e => (γ k e : ℂ_[p])) _ (fun e => cc_linS _ _ _ _ _ _ _) _)
