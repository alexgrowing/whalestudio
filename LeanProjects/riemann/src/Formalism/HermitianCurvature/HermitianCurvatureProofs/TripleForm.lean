import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.A5x1

theorem lamN_last {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (j : ℕ) (hj : j + 1 = n) : lamN R Z j = lamLin R Z := by
  unfold lamN lamTil lamLin rowN lastCoord
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  have : (a.val = j ↔ a.val + 1 = n) := by omega
  simp [this]

theorem card_isoSet {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (φ0 : coker R Z ≃ₗ[R] C) (hφ0 : φ0 ∈ isoSet R Z C e lam) :
    Nat.card (isoSet R Z C e lam) = Nat.card (autSet R C e lam) := by
  refine Nat.card_congr ⟨fun φ => ⟨φ0.symm.trans φ.1, ?_⟩, fun σ => ⟨φ0.trans σ.1, ?_⟩, ?_, ?_⟩
  · refine ⟨?_, fun c => ?_⟩
    · have : φ0.symm e = eZ R Z := by rw [← hφ0.1]; simp
      simp [this, φ.2.1]
    · obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (φ0.symm c)
      have h3 : φ0 (Submodule.Quotient.mk v) = c := by rw [hv]; simp
      simp only [LinearEquiv.trans_apply]
      rw [← hv, φ.2.2 v, ← hφ0.2 v, h3]
  · refine ⟨?_, fun v => ?_⟩
    · simp [hφ0.1, σ.2.1]
    · simp only [LinearEquiv.trans_apply]
      rw [σ.2.2, hφ0.2]
  · intro φ; ext x; simp
  · intro σ; ext x; simp

theorem card_isoZZ {K : Type} [CommRing K] (R : Subring K) {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (φ0 : coker R Z ≃ₗ[R] C) (hφ0 : φ0 ∈ isoSet R Z C e lam) :
    Nat.card (isoSet R Z' C e lam) = Nat.card (isoZZ R Z Z') := by
  refine Nat.card_congr ⟨fun ρ => ⟨φ0.trans ρ.1.symm, ?_⟩, fun φ => ⟨φ.1.symm.trans φ0, ?_⟩, ?_, ?_⟩
  · refine ⟨?_, fun v v' hv => ?_⟩
    · simp only [LinearEquiv.trans_apply, hφ0.1]
      exact (LinearEquiv.symm_apply_eq _).2 ρ.2.1.symm
    · simp only [LinearEquiv.trans_apply] at hv
      have h4 : φ0 (Submodule.Quotient.mk v) = ρ.1 (Submodule.Quotient.mk v') := by
        rw [← hv]; simp
      rw [← ρ.2.2 v', ← h4, hφ0.2]
  · refine ⟨?_, fun v' => ?_⟩
    · have : φ.1.symm (eZ R Z') = eZ R Z := by rw [← φ.2.1]; simp
      simp [this, hφ0.1]
    · obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (φ.1.symm (Submodule.Quotient.mk v'))
      have h3 : φ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' := by rw [hv]; simp
      simp only [LinearEquiv.trans_apply]
      rw [← hv, hφ0.2 v, φ.2.2 v v' h3]
  · intro ρ; ext x; simp
  · intro φ; ext x; simp

end Formalism.FourierDecayAlt.P.A5x1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A5x1

theorem matchingIsoSetEq : Formalism.FourierDecayAlt.A5.IsoZZIsIso := by
  intro K _ R n n' Z Z' lam' h
  ext φ
  simp only [isoZZ, isoSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v => ?_⟩
    obtain ⟨v', hv'⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk v))
    rw [← hv', h]; exact h2 v v' hv'.symm
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v v' hv => ?_⟩
    rw [← h2 v, hv, h]

theorem invRowFunctionalLast : Formalism.FourierDecayAlt.A5.LamLast := by
  intro K _ R n Z
  exact lamN_last R Z n rfl

theorem matchingIsoCount : Formalism.FourierDecayAlt.A5.IsoCount := by
  intro K _ R n n' Z Z' ι _ C _ _ e lam hne hex
  obtain ⟨a0, φ0, hφ0⟩ := hex
  classical
  have hzero : ∀ b, b ≠ a0 → IsEmpty (isoSet R Z (C b) (e b) (lam b)) := by
    intro b hb
    refine ⟨fun ⟨φ1, h1⟩ => hne b a0 hb ⟨φ1.symm.trans φ0, ?_, ?_⟩⟩
    · have : φ1.symm (e b) = eZ R Z := by rw [← h1.1]; simp
      simp [this, hφ0.1]
    · intro c
      obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (φ1.symm c)
      have h3 : φ1 (Submodule.Quotient.mk v) = c := by rw [hv]; simp
      simp only [LinearEquiv.trans_apply]
      rw [← hv, hφ0.2 v, ← h1.2 v, h3]
  rw [Finset.sum_eq_single a0 (fun b _ hb => by have := hzero b hb; simp) (by simp)]
  rw [card_isoSet R Z _ _ _ φ0 hφ0, ← card_isoZZ R Z Z' _ _ _ φ0 hφ0]
  by_cases hN : Nat.card (autSet R (C a0) (e a0) (lam a0)) = 0
  · have hM : Nat.card (isoSet R Z' (C a0) (e a0) (lam a0)) = 0 := by
      by_cases hE : (isoSet R Z' (C a0) (e a0) (lam a0)).Nonempty
      · obtain ⟨ρ, hρ⟩ := hE
        rw [card_isoSet R Z' _ _ _ ρ hρ, hN]
      · rw [Set.not_nonempty_iff_eq_empty] at hE
        rw [hE]; simp
    simp [hN, hM]
  · have : (Nat.card (autSet R (C a0) (e a0) (lam a0)) : ℂ) ≠ 0 := by exact_mod_cast hN
    field_simp

theorem tripleForm : Formalism.FourierDecayAlt.A5.TripleForm := by
  intro K _ R ψ w w' k hw hw'
  unfold Kp intTT pairTerm
  apply finsum_congr
  intro q
  congr 2
  split_ifs with hI
  · congr 1
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight ?_
    intro φ
    constructor
    · intro hφ
      refine ⟨hφ, ?_⟩
      intro j hkj hjn
      have hj : j = k := by omega
      subst hj
      refine ⟨0, ?_⟩
      intro v v' hv
      have h2 := hφ.2 v v' hv
      rw [lamN_last R _ j hw'.symm, lamN_last R _ j hw.symm, h2]
      simp
    · exact fun h => h.1
  · rfl

end Formalism.FourierDecayAlt.P
