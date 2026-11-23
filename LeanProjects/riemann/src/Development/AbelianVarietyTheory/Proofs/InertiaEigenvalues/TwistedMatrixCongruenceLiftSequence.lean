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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubIffMapMkEq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.LimLink

theorem dvd_iff_map_eq {R : Type*} [CommRing R] {p q : Type*} (a : R) (A B : Matrix p q R) :
    (∀ i j, a ∣ (A - B) i j) ↔
      A.map (Ideal.Quotient.mk (Ideal.span {a})) = B.map (Ideal.Quotient.mk (Ideal.span {a})) := by
  first
  | exact @_root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq
  | exact _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq
  | (apply _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq ..)

theorem map_smul_ringHom {R S : Type*} [CommRing R] [CommRing S] {p q : Type*} (f : R →+* S) (r : R)
    (A : Matrix p q R) : (r • A).map f = f r • A.map f := by
  ext i j; simp

end GlobalTheory.BKLim.LimLink

open GlobalTheory.BKLim.LimLink in
theorem GlobalTheory.BKLim.limit_basis_link_mod : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (tw.d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v)) → ∀ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (T : Matrix (Fin d) (Fin d) (WCb l)), Y.map (inclW l) = inclW l τ ^ N • T → (∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∀ n, ∃ m, n ≤ m ∧ ∃ (Rn : Matrix (Fin d) (Fin (tw.d' m)) bk.S) (Q : Matrix (Fin (tw.d' m)) (Fin d) (Ainf l)), (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi m) * (F m).T - T * Rn.map bk.evW) i j) ∧ ∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * (Rn.map bk.ev * Q).map (inclW l) - inclW l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j := by
  intro l _ K bk τ hτ d N ρ tw F T0 R H1 H2 H3 Y T hY H5 n
  obtain ⟨hu, -, -, -⟩ := GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ
  have huN : IsUnit (inclW l τ ^ N) := hu.pow N
  obtain ⟨π, key, key'⟩ : ∃ π : WCb l →+* (WCb l ⧸ Ideal.span {(l : WCb l) ^ n}),
      (∀ {p q : ℕ} (A B : Matrix (Fin p) (Fin q) (WCb l)),
        (∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) → A.map π = B.map π) ∧
      (∀ {p q : ℕ} (A B : Matrix (Fin p) (Fin q) (WCb l)),
        A.map π = B.map π → ∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) :=
    ⟨_, fun A B => (dvd_iff_map_eq _ A B).1, fun A B => (dvd_iff_map_eq _ A B).2⟩
  obtain ⟨m, hnm, hm⟩ := H2 n
  have hcol : ∀ j : Fin (tw.d' m), ∃ (v : Fin d → WCb l) (c : Fin d → bk.S),
      (∀ i, (l : WCb l) ^ n ∣ v i - R m i j) ∧ T0 *ᵥ v = T *ᵥ fun a => bk.evW (c a) := by
    intro j
    obtain ⟨v, hv1, hv2⟩ := hm (Pi.single j 1)
    obtain ⟨hOE, y, hy⟩ := H3 v hv2
    obtain ⟨c, hc⟩ := H5 y ⟨v, hOE, hy⟩
    refine ⟨v, c, ?_, ?_⟩
    · intro i
      have hs : (fun a => bk.evW ((Pi.single j (1 : bk.S) : Fin (tw.d' m) → bk.S) a))
          = Pi.single j 1 := by
        funext a; by_cases h : a = j
        · subst h; simp
        · simp [Pi.single_apply, h]
      have := hv1 i
      rw [hs] at this
      simpa [Matrix.mulVec_single_one] using this
    · have h1 : (fun i => inclW l (y i)) = inclW l τ ^ N • (T *ᵥ fun a => bk.evW (c a)) := by
        rw [hc]; funext i
        rw [RingHom.map_mulVec, hY, Matrix.smul_mulVec]
        rfl
      rw [hy] at h1
      exact huN.smul_left_cancel.1 h1
  choose V C hV hVC using hcol
  let Rn : Matrix (Fin d) (Fin (tw.d' m)) bk.S := Matrix.of fun i j => C j i
  have hTR : T * Rn.map bk.evW = T0 * Matrix.of (fun i j => V j i) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hVC j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Rn]
    exact this.symm
  have hfirst : (zW (tw.Pi m) * (F m).T).map π = (T * Rn.map bk.evW).map π := by
    have e1 : (zW (tw.Pi m) * (F m).T).map π = (T0 * R m).map π :=
      key _ _ (fun i j => (pow_dvd_pow _ hnm).trans (H1 m i j))
    have e2 : (R m).map π = (Matrix.of fun i j => V j i).map π :=
      key _ _ (fun i j => by
        have := hV j i
        rw [← dvd_neg]; simpa [neg_sub] using this)
    rw [e1, hTR, Matrix.map_mul, Matrix.map_mul, e2]
  obtain ⟨Ym, Y'm, hYm, hYY⟩ :=
    GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N (tw.d' m) (fun g => (tw.ρ' m g).val) (F m)
  obtain ⟨Sm, hSm⟩ := (tw.onto m).surj
  refine ⟨m, hnm, Rn, Y'm * Sm.map (algebraMap ℤ_[l] (Ainf l)), key' _ _ hfirst, ?_⟩
  have hinc : ∀ x : ℤ_[l], inclW l (algebraMap ℤ_[l] (Ainf l) x) = algebraMap ℤ_[l] (WCb l) x :=
    fun x => (inclWA l).commutes x
  have hFY : (F m).T * Y'm.map (inclW l) = inclW l τ ^ N • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (WCb l)) := by
    apply huN.smul_left_cancel.1
    rw [← Matrix.smul_mul, ← hYm, ← Matrix.map_mul, hYY, map_smul_ringHom,
      Matrix.map_one _ (map_zero _) (map_one _), smul_smul, map_pow, ← pow_add, two_mul]
  have hQ : ((Rn.map bk.ev) * (Y'm * Sm.map (algebraMap ℤ_[l] (Ainf l)))).map (inclW l)
      = Rn.map bk.evW * (Y'm.map (inclW l) * zW Sm) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map]
    congr 2
    ext i j
    simp [hinc]
  have hS1 : (zW (tw.Pi m * Sm)).map π = (1 : Matrix (Fin d) (Fin d) (WCb l)).map π := by
    apply key
    intro i j
    have e : (zW (tw.Pi m * Sm) - 1) i j = algebraMap ℤ_[l] (WCb l) ((tw.Pi m * Sm - 1 : Matrix (Fin d) (Fin d) ℤ_[l]) i j) := by
      simp only [zW, Matrix.sub_apply, Matrix.map_apply, map_sub]
      congr 1
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [e]
    refine (pow_dvd_pow _ hnm).trans ?_
    have := map_dvd (algebraMap ℤ_[l] (WCb l)) (hSm i j)
    simpa using this
  have hE : inclW l τ ^ N • (zW (tw.Pi m) * (F m).T * (Y'm.map (inclW l) * zW Sm))
      = inclW l τ ^ (2 * N) • zW (tw.Pi m * Sm) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (F m).T, hFY, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_smul,
      ← pow_add, ← two_mul]
    simp only [zW, Matrix.map_mul]
  apply key'
  calc (Y.map (inclW l) * (Rn.map bk.ev * (Y'm * Sm.map (algebraMap ℤ_[l] (Ainf l)))).map (inclW l)).map π
      = (inclW l τ ^ N • ((T * Rn.map bk.evW) * (Y'm.map (inclW l) * zW Sm))).map π := by
        rw [hQ, hY, Matrix.smul_mul, ← Matrix.mul_assoc]
    _ = (inclW l τ ^ N • ((zW (tw.Pi m) * (F m).T) * (Y'm.map (inclW l) * zW Sm))).map π := by
        rw [map_smul_ringHom, map_smul_ringHom, Matrix.map_mul, Matrix.map_mul (L := zW (tw.Pi m) * (F m).T), hfirst]
    _ = (inclW l τ ^ (2 * N) • zW (tw.Pi m * Sm)).map π := by rw [hE]
    _ = (inclW l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l))).map π := by
        rw [map_smul_ringHom, map_smul_ringHom, hS1]
