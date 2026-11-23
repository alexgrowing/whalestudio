import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatPowDvdPerPowMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisLimitLatticeTowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LimitBreuilKisinBasisInvariantEtaleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapBreuilKisinMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MittagLefflerImageBreuilKisinModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentCoefficientsAinfModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisOfEtaleInvariantBoundedPolesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescendRightInverseStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

set_option maxHeartbeats 1000000 in

theorem mittagLeffler_approx : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), IsUnit T0 → (∀ n i j, R n i j ∈ bk.OE) → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∀ n, ∃ c : ℕ, ∀ m, n ≤ m → ∀ s : Fin (tw.d' n) → bk.S, ∃ s' : Fin (tw.d' m) → bk.S, ∀ i, (l : WCb l) ^ n ∣ ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) - R m *ᵥ fun j => bk.evW (s' j)) i := by
  intro l _ K bk τ hτ d N ρ tw F T0 R hT0 hR hRF n
  set I : Ideal (WCb l) := Ideal.span {(l : WCb l) ^ n} with hI
  let q : WCb l →+* WCb l ⧸ I := Ideal.Quotient.mk I
  have hq : ∀ w, (l : WCb l) ^ n ∣ w ↔ q w = 0 := fun w => by
    rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  have hmat : ∀ {a b : ℕ} (A B : Matrix (Fin a) (Fin b) (WCb l)), (∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) →
      A.map q = B.map q := by
    intro a b A B h
    ext i j
    simp only [Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub]
    exact (hq _).1 (h i j)
  have hvec : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) (WCb l)) (v : Fin b → WCb l),
      (fun i => q ((M *ᵥ v) i)) = M.map q *ᵥ fun j => q (v j) := fun M v => funext fun i => RingHom.map_mulVec q M v i
  obtain ⟨c, y, hcy⟩ := GlobalTheory.BKLim.flatPow_dvd_perPow_mod l K bk τ hτ (2 * N) n
  refine ⟨c, fun m hnm s => ?_⟩

  obtain ⟨Yn, Y'n, hYn, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N (tw.d' n) _ (F n)
  obtain ⟨Ym, Y'm, hYm, hYYm⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N (tw.d' m) _ (F m)
  obtain ⟨Sm, hSm⟩ := (tw.onto m).surj
  have hu : IsUnit (inclW l τ ^ N) := (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).1.pow N

  have hTY : (F m).T * Y'm.map (inclW l) = inclW l τ ^ N • (1 : Matrix _ _ (WCb l)) := by
    have h1 : (Ym * Y'm).map (inclW l) = (τ ^ (2 * N) • (1 : Matrix _ _ (Ainf l))).map (inclW l) := by rw [hYYm]
    rw [Matrix.map_mul, hYm] at h1
    have h2 : (τ ^ (2 * N) • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (Ainf l))).map (inclW l) =
        inclW l τ ^ N • (inclW l τ ^ N • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (WCb l))) := by
      rw [smul_smul, ← pow_add, ← two_mul, ← map_pow]
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [← hu.smul_left_cancel, ← Matrix.smul_mul, h1, h2]
  let qi : Ainf l →+* WCb l ⧸ I := q.comp (inclW l)
  have hv : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) (Ainf l)) (v : Fin b → Ainf l),
      (fun i => qi ((M *ᵥ v) i)) = M.map qi *ᵥ fun j => qi (v j) := fun M v => funext fun i => RingHom.map_mulVec qi M v i
  have hzq : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℤ_[l]),
      (M.map (algebraMap ℤ_[l] (Ainf l))).map qi = (zW M).map q := fun M => by
    ext i j
    show q (inclW l (algebraMap ℤ_[l] (Ainf l) (M i j))) = q (algebraMap ℤ_[l] (WCb l) (M i j))
    congr 1
    exact (inclWA l).commutes _

  have F1 : T0.map q * (R n).map q = (zW (tw.Pi n)).map q * (F n).T.map q := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact (hmat _ _ fun i j => by rw [Matrix.sub_apply, dvd_sub_comm, ← Matrix.sub_apply]; exact hRF n i j)
  have F2 : T0.map q * (R m).map q = (zW (tw.Pi m)).map q * (F m).T.map q := by
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact (hmat _ _ fun i j => by
      rw [Matrix.sub_apply, dvd_sub_comm, ← Matrix.sub_apply]; exact dvd_trans (pow_dvd_pow _ hnm) (hRF m i j))
  have F3 : (zW (tw.Pi m)).map q * (zW Sm).map q = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_one q (map_zero q) (map_one q)]
    refine hmat _ _ fun i j => dvd_trans (pow_dvd_pow _ hnm) ?_
    have h := map_dvd (algebraMap ℤ_[l] (WCb l)) (hSm i j)
    rw [map_pow, map_natCast] at h
    convert h using 1
    rw [← Matrix.map_mul, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have F4 : Yn.map qi = qi τ ^ N • (F n).T.map q := by
    have : Yn.map qi = (Yn.map (inclW l)).map q := by ext i j; rfl
    rw [this, hYn]; ext i j; simp [qi]
  have F5 : (F m).T.map q * Y'm.map qi = qi τ ^ N • (1 : Matrix _ _ (WCb l ⧸ I)) := by
    have : Y'm.map qi = (Y'm.map (inclW l)).map q := by ext i j; rfl
    rw [this, ← Matrix.map_mul, hTY]
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp [qi]
  have hXc : q (inclW l (bk.ev X ^ c)) = qi τ ^ (2 * N) * qi y := by
    have h0 : (l : WCb l) ^ n ∣ inclW l (bk.ev X ^ c - τ ^ (2 * N) * y) := by
      have := map_dvd (inclW l) hcy
      rwa [map_pow, map_natCast] at this
    have h := (hq _).1 h0
    rw [map_sub, map_sub, sub_eq_zero] at h
    rw [h]
    simp [qi]
  have F6 : (fun j => q (bk.evW (X ^ c * s j))) = (qi τ ^ (2 * N) * qi y) • fun j => qi (bk.ev (s j)) := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul, ← hXc]
    show q (inclW l (bk.ev (X ^ c * s j))) = q (inclW l (bk.ev X ^ c)) * q (inclW l (bk.ev (s j)))
    rw [map_mul, map_pow, map_mul, map_mul]

  set e : Fin (tw.d' n) → WCb l ⧸ I := fun j => qi (bk.ev (s j)) with he
  set zA := algebraMap ℤ_[l] (Ainf l) with hzA
  set w1 : Fin (tw.d' m) → Ainf l := (Sm.map zA) *ᵥ ((tw.Pi n).map zA *ᵥ (Yn *ᵥ fun j => bk.ev (s j))) with hw1
  set a : Fin (tw.d' m) → Ainf l := y • (Y'm *ᵥ w1) with ha
  have hqa : (fun j => q (inclW l (a j))) =
      qi y • (Y'm.map qi *ᵥ ((zW Sm).map q *ᵥ ((zW (tw.Pi n)).map q *ᵥ (Yn.map qi *ᵥ e)))) := by
    have h0 : (fun j => q (inclW l (a j))) = qi y • fun j => qi ((Y'm *ᵥ w1) j) := by
      funext j
      simp only [ha, Pi.smul_apply, smul_eq_mul, map_mul]
      rfl
    rw [h0, hv, hw1, hv, hv, hv, hzq, hzq]
  obtain ⟨T0i, hT0i⟩ := (hT0.map (RingHom.mapMatrix q)).exists_left_inv
  have hT0i' : T0i * T0.map q = 1 := hT0i
  have G : (R n).map q *ᵥ ((qi τ ^ (2 * N) * qi y) • e) =
      (R m).map q *ᵥ (qi y • (Y'm.map qi *ᵥ ((zW Sm).map q *ᵥ ((zW (tw.Pi n)).map q *ᵥ (Yn.map qi *ᵥ e))))) := by
    have canc : ∀ u v : Fin d → WCb l ⧸ I, T0.map q *ᵥ u = T0.map q *ᵥ v → u = v := fun u v h => by
      have := congrArg (fun x => T0i *ᵥ x) h
      simpa only [Matrix.mulVec_mulVec, hT0i', Matrix.one_mulVec] using this
    apply canc
    have L : T0.map q *ᵥ ((R n).map q *ᵥ ((qi τ ^ (2 * N) * qi y) • e)) =
        (qi τ ^ (2 * N) * qi y) • (((zW (tw.Pi n)).map q * (F n).T.map q) *ᵥ e) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, F1]
    have Rr : T0.map q *ᵥ ((R m).map q *ᵥ (qi y • (Y'm.map qi *ᵥ ((zW Sm).map q *ᵥ ((zW (tw.Pi n)).map q *ᵥ (Yn.map qi *ᵥ e)))))) =
        (qi y * qi τ ^ N * qi τ ^ N) • (((zW (tw.Pi n)).map q * (F n).T.map q) *ᵥ e) := by
      simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
      rw [F2, Matrix.mul_assoc ((zW (tw.Pi m)).map q), F5, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        Matrix.smul_mul, F3, Matrix.one_mul, F4]
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mulVec, smul_smul]
      first | rfl | (congr 1; ring)
    rw [L, Rr]
    congr 1
    ring
  have hev : ∀ t : bk.S, bk.evW t ∈ bk.OE := fun t => by
    intro k
    exact ⟨0, t, 0, by simp⟩
  have hxOE : ∀ i, (R n *ᵥ fun j => bk.evW (X ^ c * s j)) i ∈ bk.OE := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hR n i j) (hev _)
  obtain ⟨s', hs'⟩ := GlobalTheory.T.breuilKisin_descent_coefficients_ainf_mod_pow l K bk d (tw.d' m) n (R m) (R n *ᵥ fun j => bk.evW (X ^ c * s j)) a (hR m) hxOE
    (fun i => by
      rw [hq, Pi.sub_apply, map_sub, sub_eq_zero]
      have h1 : q ((R n *ᵥ fun j => bk.evW (X ^ c * s j)) i) =
          ((R n).map q *ᵥ fun j => q (bk.evW (X ^ c * s j))) i := congrFun (hvec (R n) fun j => bk.evW (X ^ c * s j)) i
      have h2 : q ((R m *ᵥ fun j => inclW l (a j)) i) = ((R m).map q *ᵥ fun j => q (inclW l (a j))) i :=
        congrFun (hvec (R m) fun j => inclW l (a j)) i
      rw [h1, h2, F6, hqa, G])
  exact ⟨s', hs'⟩

end GlobalTheory.BKLim
