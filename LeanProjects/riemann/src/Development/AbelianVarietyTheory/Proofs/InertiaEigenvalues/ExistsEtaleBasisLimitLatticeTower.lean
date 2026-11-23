import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisModPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantMapBreuilKisinMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LadicDescentStepToOE
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.EtaleLimit

variable {l : ℕ} [Fact l.Prime]

theorem cong_iff {m k : Type} (n : ℕ) (A B : Matrix m k (WCb l)) :
    (∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) ↔
      A.map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ n})) =
        B.map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ n})) := by
  constructor
  · intro h; ext i j
    simp only [Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]; exact h i j
  · intro h i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.map_apply] at this
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at this
    exact this

theorem cong_mono {m k : Type} {n n' : ℕ} (h : n ≤ n') {A B : Matrix m k (WCb l)}
    (hAB : ∀ i j, (l : WCb l) ^ n' ∣ (A - B) i j) : ∀ i j, (l : WCb l) ^ n ∣ (A - B) i j :=
  fun i j => (pow_dvd_pow _ h).trans (hAB i j)

theorem not_isUnit_l : ¬ IsUnit (l : WCb l) := by
  intro h
  have h2 := h.map (WittVector.constantCoeff (p := l) (R := Cb l))
  rw [map_natCast, CharP.cast_eq_zero] at h2
  exact not_isUnit_zero h2

theorem complete : IsAdicComplete (Ideal.span {(l : WCb l)}) (WCb l) := by
  haveI := GlobalTheory.BSP.DescentStep.perfectRing_Cb (l := l)
  exact WittVector.isAdicCompleteIdealSpanP

theorem isUnit_of_cong {d : ℕ} {A B : Matrix (Fin d) (Fin d) (WCb l)} (hB : IsUnit B)
    (h : ∀ i j, (l : WCb l) ^ 1 ∣ (A - B) i j) : IsUnit A := by
  have hq := (cong_iff 1 A B).1 h
  set q := Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ 1})
  have hd : q A.det = q B.det := by
    rw [RingHom.map_det, RingHom.map_det]
    exact congrArg Matrix.det hq
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, pow_one] at hd
  rw [Matrix.isUnit_iff_isUnit_det] at hB ⊢
  obtain ⟨b, hb⟩ := hB
  haveI := complete (l := l)
  have hj : (A.det - B.det) * ((b⁻¹ : (WCb l)ˣ) : WCb l) ∈ Ideal.jacobson ⊥ :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {(l : WCb l)})
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.2 hd))
  have h1 := (Ideal.mem_jacobson_bot.1 hj) 1
  have e : (A.det - B.det) * ((b⁻¹ : (WCb l)ˣ) : WCb l) * 1 + 1 = A.det * ((b⁻¹ : (WCb l)ˣ) : WCb l) := by
    rw [← hb]; simp only [mul_one, sub_mul, Units.mul_inv]; ring
  rw [e] at h1
  exact isUnit_of_mul_isUnit_left h1

end GlobalTheory.BKLim.EtaleLimit

namespace GlobalTheory.BKLim.EtaleLimit

variable {l : ℕ} [Fact l.Prime]

theorem mul_mem {S : Subring (WCb l)} {m k o : Type} [Fintype k] {A : Matrix m k (WCb l)} {B : Matrix k o (WCb l)}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) : ∀ i j, (A * B) i j ∈ S := fun i j => by
  rw [Matrix.mul_apply]
  exact S.sum_mem fun x _ => S.mul_mem (hA i x) (hB x j)

theorem exists_lim {d : ℕ} (S : ℕ → Matrix (Fin d) (Fin d) (WCb l))
    (h : ∀ k i j, (l : WCb l) ^ (k + 1) ∣ (S (k + 1) - S k) i j) :
    ∃ L : Matrix (Fin d) (Fin d) (WCb l), ∀ k i j, (l : WCb l) ^ (k + 1) ∣ (L - S k) i j := by
  haveI := complete (l := l)
  have hc : ∀ i j m n, m ≤ n → (l : WCb l) ^ m ∣ S n i j - S m i j := by
    intro i j m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have e : S (n + 1) i j - S m i j = (S (n + 1) - S n) i j + (S n i j - S m i j) := by
        simp only [Matrix.sub_apply]; ring
      rw [e]
      exact dvd_add ((pow_dvd_pow _ (by omega)).trans (h n i j)) ih
  have key : ∀ i j, ∃ L : WCb l, ∀ n, (l : WCb l) ^ n ∣ L - S n i j := by
    intro i j
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := Ideal.span {(l : WCb l)}) (M := WCb l))
      (f := fun m => S m i j) (fun {m n} hmn => by
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
          ← dvd_neg, neg_sub]
        exact hc i j m n hmn)
    refine ⟨L, fun n => ?_⟩
    have := hL n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
    rw [← dvd_neg, neg_sub]; exact this
  choose L hL using key
  refine ⟨Matrix.of L, fun k i j => ?_⟩
  have e : (Matrix.of L - S k) i j = (L i j - S (k + 1) i j) + (S (k + 1) - S k) i j := by
    simp only [Matrix.sub_apply, Matrix.of_apply]; ring
  rw [e]
  exact dvd_add (hL i j (k + 1)) (h k i j)

end GlobalTheory.BKLim.EtaleLimit

namespace GlobalTheory.BKLim.EtaleLimit

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem inv_mem (bk : BK K) {x : WCb l} (hx : x ∈ bk.OE) (hu : IsUnit x) : ∃ v ∈ bk.OE, x * v = 1 := by
  obtain ⟨-, -, -, hval, -⟩ := GlobalTheory.T.integral_elements_unit_factorization l K bk
  obtain ⟨k, v, v', hv, hv', hvv, rfl⟩ := hval x hx hu.ne_zero
  cases k with
  | zero => exact ⟨v', hv', by rw [pow_zero, one_mul, hvv]⟩
  | succ k =>
    exfalso
    apply not_isUnit_l (l := l)
    rw [pow_succ', mul_assoc] at hu
    exact isUnit_of_mul_isUnit_left hu

theorem exists_inv (bk : BK K) {d : ℕ} {M : Matrix (Fin d) (Fin d) (WCb l)} (hM : ∀ i j, M i j ∈ bk.OE)
    (hu : IsUnit M) : ∃ M' : Matrix (Fin d) (Fin d) (WCb l), (∀ i j, M' i j ∈ bk.OE) ∧ M * M' = 1 := by
  let Mo : Matrix (Fin d) (Fin d) bk.OE := Matrix.of fun i j => ⟨M i j, hM i j⟩
  have hMo : Mo.map bk.OE.subtype = M := by ext i j; rfl
  have hdet : bk.OE.subtype Mo.det = M.det := by rw [RingHom.map_det]; exact congrArg Matrix.det hMo
  rw [Matrix.isUnit_iff_isUnit_det, ← hdet] at hu
  obtain ⟨v, hv, hxv⟩ := inv_mem bk (Mo.det).2 hu
  have hdu : IsUnit Mo.det := isUnit_iff_exists_inv.2 ⟨⟨v, hv⟩, Subtype.ext hxv⟩
  refine ⟨(Mo⁻¹).map bk.OE.subtype, fun i j => (Mo⁻¹ i j).2, ?_⟩
  rw [← hMo, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdu]
  simp

end GlobalTheory.BKLim.EtaleLimit

namespace GlobalTheory.BKLim.EtaleLimit

theorem evW_mem {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (s : bk.S) : bk.evW s ∈ bk.OE :=
  fun _ => ⟨0, s, 0, by simp⟩

theorem cong_symm {l : ℕ} [Fact l.Prime] {m k : Type} {n : ℕ} {A B : Matrix m k (WCb l)}
    (h : ∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) : ∀ i j, (l : WCb l) ^ n ∣ (B - A) i j := fun i j => by
  rw [← neg_sub, Matrix.neg_apply, dvd_neg]; exact h i j

theorem one_mem' {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) {d : ℕ} :
    ∀ i j, (1 : Matrix (Fin d) (Fin d) (WCb l)) i j ∈ bk.OE := fun i j => by
  rw [Matrix.one_apply]; split_ifs
  · exact bk.OE.one_mem
  · exact bk.OE.zero_mem

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val), ∃ T0 : Matrix (Fin d) (Fin d) (WCb l), IsUnit T0 ∧ ∀ n, ∃ (R : Matrix (Fin d) (Fin (tw.d' n)) (WCb l)) (R' : Matrix (Fin (tw.d' n)) (Fin d) (WCb l)), (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (R * R' - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) := by
  intro l _ K bk τ hτ d N ρ tw F
  choose T R R' hTu hR hR' ha hb using fun k : ℕ =>
    GlobalTheory.T.exists_etaleBasis_modPow l K bk τ hτ N d (tw.d' (k + 1)) (k + 1) ρ (tw.ρ' (k + 1)) (F (k + 1)) (tw.Pi (k + 1)) (by omega)
      (tw.onto (k + 1))
  choose Y hY using fun k : ℕ =>
    GlobalTheory.T.exists_equivariantMap_breuilKisinMatrix l K bk τ hτ N N (tw.d' (k + 1 + 1)) (tw.d' (k + 1)) (fun g => (tw.ρ' (k + 1 + 1) g).val)
      (fun g => (tw.ρ' (k + 1) g).val) (F (k + 1 + 1)) (F (k + 1)) (tw.f (k + 1)) (fun g => tw.f_equi (k + 1) g)
  obtain ⟨U, hU⟩ : ∃ U : ℕ → Matrix (Fin d) (Fin d) (WCb l), ∀ k, U k = R k * (Y k).map bk.evW * R' (k + 1) :=
    ⟨_, fun _ => rfl⟩
  have hUm : ∀ k i j, U k i j ∈ bk.OE := fun k => by
    rw [hU k]
    exact mul_mem (mul_mem (hR k) (fun i j => evW_mem bk _)) (hR' (k + 1))
  have hUT : ∀ k i j, (l : WCb l) ^ (k + 1) ∣ (T (k + 1) - T k * U k) i j := by
    intro k
    rw [cong_iff]
    have h1 : (zW (tw.Pi (k + 1 + 1)) * (F (k + 1 + 1)).T * R' (k + 1)).map
        (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) =
        (T (k + 1)).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) :=
      (cong_iff _ _ _).1 (cong_mono (by omega) (hb (k + 1)))
    have h2 : (zW (tw.Pi (k + 1) * tw.f (k + 1))).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) =
        (zW (tw.Pi (k + 1 + 1))).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := by
      apply (cong_iff _ _ _).1
      intro i j
      have := map_dvd (algebraMap ℤ_[l] (WCb l)) (tw.f_Pi (k + 1) i j)
      rw [map_pow, map_natCast, Matrix.sub_apply, map_sub] at this
      exact this
    have h4 : (zW (tw.Pi (k + 1)) * (F (k + 1)).T).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) =
        (T k * R k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := (cong_iff _ _ _).1 (ha k)
    have h3 := hY k
    rw [← h1, hU k]
    have e2 : zW (tw.Pi (k + 1) * tw.f (k + 1)) = zW (tw.Pi (k + 1)) * zW (tw.f (k + 1)) := Matrix.map_mul
    rw [e2] at h2
    calc (zW (tw.Pi (k + 1 + 1)) * (F (k + 1 + 1)).T * R' (k + 1)).map
          (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)}))
        = (zW (tw.Pi (k + 1 + 1))).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) *
          ((F (k + 1 + 1)).T * R' (k + 1)).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := by
          simp only [Matrix.map_mul, Matrix.mul_assoc]
      _ = (zW (tw.Pi (k + 1)) * (zW (tw.f (k + 1)) * (F (k + 1 + 1)).T) * R' (k + 1)).map
          (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := by
          rw [← h2]; simp only [Matrix.map_mul, Matrix.mul_assoc]
      _ = (zW (tw.Pi (k + 1)) * (F (k + 1)).T).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) *
          ((Y k).map bk.evW * R' (k + 1)).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := by
          rw [← h3]; simp only [Matrix.map_mul, Matrix.mul_assoc]
      _ = (T k * (R k * (Y k).map bk.evW * R' (k + 1))).map
          (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := by
          rw [h4]; simp only [Matrix.map_mul, Matrix.mul_assoc]
  have hUu : ∀ k, IsUnit (U k) := fun k => by
    have h := isUnit_of_cong (A := T k * U k) (hTu (k + 1)) (cong_symm (cong_mono (by omega) (hUT k)))
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at h
    exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right h)
  choose V hVm hUV using fun k => exists_inv bk (hUm k) (hUu k)
  obtain ⟨C, hC0, hCs⟩ : ∃ C : ℕ → Matrix (Fin d) (Fin d) (WCb l), C 0 = 1 ∧ ∀ k, C (k + 1) = V k * C k :=
    ⟨fun k => Nat.rec 1 (fun k Ck => V k * Ck) k, rfl, fun _ => rfl⟩
  obtain ⟨D, hD0, hDs⟩ : ∃ D : ℕ → Matrix (Fin d) (Fin d) (WCb l), D 0 = 1 ∧ ∀ k, D (k + 1) = D k * U k :=
    ⟨fun k => Nat.rec 1 (fun k Dk => Dk * U k) k, rfl, fun _ => rfl⟩
  have hCm : ∀ k i j, C k i j ∈ bk.OE := by
    intro k; induction k with
    | zero => rw [hC0]; exact one_mem' bk
    | succ k ih => rw [hCs]; exact mul_mem (hVm k) ih
  have hDm : ∀ k i j, D k i j ∈ bk.OE := by
    intro k; induction k with
    | zero => rw [hD0]; exact one_mem' bk
    | succ k ih => rw [hDs]; exact mul_mem ih (hUm k)
  have hDC : ∀ k, D k * C k = 1 := by
    intro k; induction k with
    | zero => rw [hD0, hC0, Matrix.mul_one]
    | succ k ih =>
      rw [hDs, hCs, Matrix.mul_assoc, ← Matrix.mul_assoc (U k), hUV k, Matrix.one_mul, ih]
  have hCD : ∀ k, C k * D k = 1 := fun k => mul_eq_one_comm.1 (hDC k)
  have hS : ∀ k i j, (l : WCb l) ^ (k + 1) ∣ (T (k + 1) * C (k + 1) - T k * C k) i j := by
    intro k
    rw [cong_iff, hCs]
    have h := (cong_iff _ _ _).1 (hUT k)
    calc (T (k + 1) * (V k * C k)).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)}))
        = (T (k + 1)).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) *
          (V k * C k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := Matrix.map_mul
      _ = (T k * (U k * V k) * C k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := by
          rw [h]; simp only [Matrix.map_mul, Matrix.mul_assoc]
      _ = _ := by rw [hUV k, Matrix.mul_one]
  obtain ⟨T0, hT0⟩ := exists_lim (fun k => T k * C k) hS
  refine ⟨T0, isUnit_of_cong (B := T 0 * C 0) ?_ (hT0 0), ?_⟩
  · rw [hC0, Matrix.mul_one]; exact hTu 0
  intro n
  cases n with
  | zero =>
    exact ⟨0, 0, fun _ _ => bk.OE.zero_mem, fun _ _ => bk.OE.zero_mem, fun _ _ => by rw [pow_zero]; exact one_dvd _,
      fun _ _ => by rw [pow_zero]; exact one_dvd _⟩
  | succ k =>
    refine ⟨D k * R k, R' k * C k, mul_mem (hDm k) (hR k), mul_mem (hR' k) (hCm k), ?_, ?_⟩
    · rw [cong_iff]
      have h4 := (cong_iff _ _ _).1 (ha k)
      have h5 : T0.map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) =
          (T k * C k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := (cong_iff _ _ _).1 (hT0 k)
      rw [h4]
      calc (T k * R k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)}))
          = (T k * (C k * D k) * R k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := by
            rw [hCD k, Matrix.mul_one]
        _ = (T k * C k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) *
            (D k * R k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := by
            simp only [Matrix.map_mul, Matrix.mul_assoc]
        _ = (T0 * (D k * R k)).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := by
            rw [← h5, ← Matrix.map_mul]
    · rw [cong_iff]
      have h4 := (cong_iff _ _ _).1 (ha k)
      have h6 := (cong_iff _ _ _).1 (hb k)
      have hTq : IsUnit ((T k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)}))) :=
        (hTu k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})).mapMatrix
      have hRR : (R k * R' k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) = 1 := by
        apply hTq.mul_left_cancel
        calc (T k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) *
              (R k * R' k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)}))
            = (T k * R k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) *
              (R' k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := by
              simp only [Matrix.map_mul, Matrix.mul_assoc]
          _ = (zW (tw.Pi (k + 1)) * (F (k + 1)).T * R' k).map
              (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := by rw [← h4, ← Matrix.map_mul]
          _ = (T k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) * 1 := by rw [h6, Matrix.mul_one]
      calc (D k * R k * (R' k * C k)).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)}))
          = (D k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) *
            (R k * R' k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) *
            (C k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := by
            simp only [Matrix.map_mul, Matrix.mul_assoc]
        _ = (D k * C k).map (Ideal.Quotient.mk (Ideal.span {(l : WCb l) ^ (k + 1)})) := by
            rw [hRR, Matrix.mul_one, Matrix.map_mul]
        _ = _ := by rw [hDC k]

end GlobalTheory.BKLim.EtaleLimit
