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

set_option maxHeartbeats 4000000 in
theorem GlobalTheory.LimVec.invertible_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (d' : ℕ → ℕ) (R : ∀ n, Matrix (Fin d) (Fin (d' n)) (WCb l)), (∀ n, ∃ R' : Matrix (Fin (d' n)) (Fin d) (WCb l), (∀ i j, R' i j ∈ bk.OE) ∧ ∀ i j, (l : WCb l) ^ n ∣ (R n * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ n i j, R n i j ∈ bk.OE) → ∃ V V' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, V i j ∈ bk.OE) ∧ (∀ i j, V' i j ∈ bk.OE) ∧ V * V' = 1 ∧ ∀ j k, ∃ s' : Fin (d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ ((fun i => V i j) - R k *ᵥ fun a => bk.evW (s' a)) i := by
  intro l _ K bk d d' R h1 h2 h3
  have lnu : ¬ IsUnit ((l : ℕ) : WCb l) := by
    intro h
    obtain ⟨u, hu⟩ := h
    have h1 := congrArg (fun x : WCb l => x.coeff 0) u.mul_inv
    simp only [WittVector.mul_coeff_zero, WittVector.one_coeff_zero] at h1
    rw [hu, WittVector.coeff_p_zero, zero_mul] at h1
    exact zero_ne_one h1
  have evW_mem : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  obtain ⟨hOEsat, ⟨wX, -, hwX⟩, -, hOEdec, -⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  obtain ⟨-, hOEcl, -⟩ := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  have cU : IsUnit (bk.evW X) := ⟨⟨_, wX, hwX, by rw [mul_comm]; exact hwX⟩, rfl⟩
  set π := Ideal.Quotient.mk (Ideal.span {((l : ℕ) : WCb l)}) with hπ
  have hdvd : ∀ x : WCb l, ((l : ℕ) : WCb l) ∣ x ↔ π x = 0 := fun x => by
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have πl : π ((l : ℕ) : WCb l) = 0 := (hdvd _).1 dvd_rfl
  have hdvd' : ∀ x y : WCb l, ((l : ℕ) : WCb l) ∣ x - y → π x = π y := fun x y h => by
    rw [← sub_eq_zero, ← map_sub]; exact (hdvd _).1 h
  obtain ⟨m, hm1, hm⟩ := h2 1
  obtain ⟨R', hR'OE, hRR'⟩ := h1 m
  choose k s y hk using fun a j => hR'OE a j 1
  set N := Finset.univ.sup (fun p : Fin (d' m) × Fin d => k p.1 p.2) with hN
  have hkN : ∀ a j, k a j ≤ N := fun a j =>
    Finset.le_sup (f := fun p : Fin (d' m) × Fin d => k p.1 p.2) (Finset.mem_univ (a, j))
  let σ : Fin (d' m) → Fin d → bk.S := fun a j => X ^ (N - k a j) * s a j
  have hσ : ∀ a j, π (bk.evW (σ a j)) = π (bk.evW X ^ N * R' a j) := by
    intro a j
    have e : bk.evW X ^ N * R' a j = bk.evW (σ a j) + (l : WCb l) * (bk.evW X ^ (N - k a j) * y a j) := by
      have hk' := hk a j
      rw [pow_one] at hk'
      have hp : bk.evW X ^ N = bk.evW X ^ (N - k a j) * bk.evW X ^ k a j := by
        rw [← pow_add, Nat.sub_add_cancel (hkN a j)]
      simp only [σ, map_mul, map_pow]
      rw [hp, mul_assoc, hk']
      ring
    rw [e, map_add, (hdvd _).1 (dvd_mul_right _ _), add_zero]
  choose v hv1 hvlim using fun j => hm (fun a => σ a j)
  let V : Matrix (Fin d) (Fin d) (WCb l) := Matrix.of fun i j => v j i
  have hVmem : ∀ i j, V i j ∈ bk.OE := by
    intro i j
    apply hOEcl
    intro n
    obtain ⟨s', hs'⟩ := hvlim j n
    refine ⟨(R n *ᵥ fun a => bk.evW (s' a)) i, ?_, hs' i⟩
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun a _ => Subring.mul_mem _ (h3 n i a) (evW_mem _)
  have hπV : π.mapMatrix V = π (bk.evW X ^ N) • (1 : Matrix (Fin d) (Fin d) (WCb l ⧸ Ideal.span {((l : ℕ) : WCb l)})) := by
    ext i j
    have e1 := hdvd' _ _ (by simpa [pow_one] using hv1 j i)
    have e2 : π ((R m * R') i j) = π ((1 : Matrix (Fin d) (Fin d) (WCb l)) i j) :=
      hdvd' _ _ (dvd_trans (dvd_pow_self ((l : ℕ) : WCb l) (show m ≠ 0 by omega)) (by simpa [Matrix.sub_apply] using hRR' i j))
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, V, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [e1]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hσ]
    rw [Matrix.mul_apply] at e2
    rw [map_sum] at e2
    simp only [map_mul] at e2
    calc ∑ x, π (R m i x) * (π (bk.evW X ^ N) * π (R' x j)) = π (bk.evW X ^ N) * ∑ x, π (R m i x) * π (R' x j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      _ = _ := by
          rw [e2]
          by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hdet : π V.det = π ((bk.evW X ^ N) ^ d) := by
    rw [RingHom.map_det, hπV, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    simp only [map_pow]
  have ndvd : ¬ ((l : ℕ) : WCb l) ∣ V.det := by
    intro h
    rw [hdvd, hdet, ← hdvd] at h
    obtain ⟨a, ha⟩ := h
    exact lnu (isUnit_of_mul_isUnit_left (ha ▸ (cU.pow N).pow d))
  let V0 : Matrix (Fin d) (Fin d) ↥bk.OE := Matrix.of fun i j => ⟨V i j, hVmem i j⟩
  have hV0 : bk.OE.subtype.mapMatrix V0 = V := by ext i j; rfl
  have hdetmem : V.det ∈ bk.OE := by
    rw [← hV0, ← RingHom.map_det]; exact (V0.det).2
  have hadj : ∀ i j, V.adjugate i j ∈ bk.OE := by
    intro i j
    rw [← hV0, ← RingHom.map_adjugate]; exact (V0.adjugate i j).2
  have hne : V.det ≠ 0 := fun h => ndvd (h ▸ dvd_zero _)
  obtain ⟨e, u, u', hu, hu', huu', hdec⟩ := hOEdec _ hdetmem hne
  have he : e = 0 := by
    by_contra he
    apply ndvd
    rw [hdec]
    obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
    exact Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero _)) _
  rw [he, pow_zero, one_mul] at hdec
  refine ⟨V, u' • V.adjugate, hVmem, fun i j => ?_, ?_, fun j k' => hvlim j k'⟩
  · simp only [Matrix.smul_apply, smul_eq_mul]; exact Subring.mul_mem _ hu' (hadj i j)
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, hdec, smul_smul, mul_comm, huu', one_smul]
