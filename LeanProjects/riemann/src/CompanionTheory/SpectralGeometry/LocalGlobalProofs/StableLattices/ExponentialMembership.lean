import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuExpMem

theorem lin_exp_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (h : ∀ m : ℕ, L (A ^ (m + 1)) = 0) : L (NormedSpace.exp A) = L 1 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hs : HasSum (fun m : ℕ => ((m.factorial : ℂ)⁻¹) • A ^ m) (NormedSpace.exp A) :=
    NormedSpace.exp_series_hasSum_exp' A
  have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have h1 := hs.map L hL
  have h2 : HasSum (fun m : ℕ => L (((m.factorial : ℂ)⁻¹) • A ^ m)) (L 1) := by
    have e : (fun m : ℕ => L (((m.factorial : ℂ)⁻¹) • A ^ m)) = fun m => if m = 0 then L 1 else 0 := by
      funext m
      cases m with
      | zero => simp
      | succ m => rw [map_smul, h m, smul_zero]; simp
    rw [e]
    exact hasSum_ite_eq 0 (L 1)
  exact h1.unique h2

theorem ex_mulVec {n : ℕ} (X : Mat n) (t : ℝ) (v : Fin n → ℂ) (hv : X *ᵥ v = 0) : ex X t *ᵥ v = v := by
  funext i
  have hsm : ∀ (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ), (c • M) *ᵥ v = c • (M *ᵥ v) := by
    intro c M
    funext l
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => (M *ᵥ v) i
      map_add' := fun M N => by simp [Matrix.add_mulVec]
      map_smul' := fun c M => by simp [hsm] }
  have hA : ∀ m : ℕ, L (((t : ℂ) • X) ^ (m + 1)) = 0 := by
    intro m
    show ((((t : ℂ) • X) ^ (m + 1)) *ᵥ v) i = 0
    rw [pow_succ, ← Matrix.mulVec_mulVec, hsm, hv, smul_zero, Matrix.mulVec_zero]
    rfl
  have e := lin_exp_eq ((t : ℂ) • X) L hA
  have e' : ((NormedSpace.exp ((t : ℂ) • X)) *ᵥ v) i = ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i := e
  show ((NormedSpace.exp ((t : ℂ) • X)) *ᵥ v) i = v i
  rw [e', Matrix.one_mulVec]

theorem ex_entry {n : ℕ} (X : Mat n) (t : ℝ) (a : ℕ) (j : Fin n)
    (h1 : ∀ i l : Fin n, a ≤ i.val → l.val < a → X i l = 0) (h2 : ∀ i : Fin n, a ≤ i.val → X i j = 0)
    (i : Fin n) (hi : a ≤ i.val) : ex X t i j = if i = j then 1 else 0 := by
  have hpow : ∀ m : ℕ, ∀ i' : Fin n, a ≤ i'.val → (X ^ (m + 1)) i' j = 0 := by
    intro m
    induction m with
    | zero => intro i' hi'; simpa using h2 i' hi'
    | succ m ih =>
      intro i' hi'
      rw [pow_succ', Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun l _ => ?_)
      by_cases hl : l.val < a
      · rw [h1 i' l hi' hl, zero_mul]
      · rw [ih l (not_lt.1 hl), mul_zero]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun M N => rfl
      map_smul' := fun c M => rfl }
  have hA : ∀ m : ℕ, L (((t : ℂ) • X) ^ (m + 1)) = 0 := by
    intro m
    show (((t : ℂ) • X) ^ (m + 1)) i j = 0
    rw [smul_pow, Matrix.smul_apply, hpow m i hi, smul_zero]
  have e := lin_exp_eq ((t : ℂ) • X) L hA
  have e' : (NormedSpace.exp ((t : ℂ) • X)) i j = (1 : Matrix (Fin n) (Fin n) ℂ) i j := e
  show (NormedSpace.exp ((t : ℂ) • X)) i j = _
  rw [e', Matrix.one_apply]

private theorem exp_mul_eq_mul_exp_of_semiconj {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    (B C H : 𝔸) (h : B * H = H * C) : NormedSpace.exp B * H = H * NormedSpace.exp C := by
  have hp : ∀ m : ℕ, B ^ m * H = H * C ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have e1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B).mul_right H
  have e2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) C).mul_left H
  have hf : (fun m : ℕ => ((m.factorial : ℂ)⁻¹ • B ^ m) * H) =
      fun m => H * (((m.factorial : ℂ)⁻¹) • C ^ m) := by
    funext m
    rw [smul_mul_assoc, hp m, mul_smul_comm]
  rw [hf] at e1
  exact e1.unique e2

theorem expMem : ExpMem := by
  intro k r z X t
  have hint : ∀ B C H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, B * H = H * C →
      NormedSpace.exp B * H = H * NormedSpace.exp C := by
    intro B C H h
    letI : NormedRing (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
      Matrix.linftyOpNormedAlgebra
    exact exp_mul_eq_mul_exp_of_semiconj B C H h
  have hU : Lie (Formalism.QuantumDeterminants.Hpk k r) X → ex X t ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
    intro hX
    have hX' : Xᴴ * Formalism.QuantumDeterminants.Hpk k r = -(Formalism.QuantumDeterminants.Hpk k r * X) := eq_neg_of_add_eq_zero_left hX
    have hAH : ((t : ℂ) • X)ᴴ * Formalism.QuantumDeterminants.Hpk k r = Formalism.QuantumDeterminants.Hpk k r * (-((t : ℂ) • X)) := by
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, hX', Matrix.mul_neg, Matrix.mul_smul, smul_neg]
      simp [Complex.star_def, Complex.conj_ofReal]
    show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Formalism.QuantumDeterminants.Hpk k r * NormedSpace.exp ((t : ℂ) • X) =
      Formalism.QuantumDeterminants.Hpk k r
    rw [← Matrix.exp_conjTranspose, hint _ _ _ hAH, mul_assoc,
      ← Matrix.exp_add_of_commute (-((t : ℂ) • X)) ((t : ℂ) • X) (Commute.neg_left (Commute.refl _)),
      neg_add_cancel, NormedSpace.exp_zero, mul_one]
  refine ⟨fun h => ⟨hU h.1, fun a => ⟨ex_mulVec X t _ (h.2.1 a).1, ex_mulVec X t _ (h.2.1 a).2⟩,
    ex_mulVec X t z h.2.2⟩, fun h => ⟨hU h.1, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩⟩
  · refine ex_entry X t (a : ℕ) (Formalism.QuantumDeterminants.eI k r a) (fun i' l hi' hl => ?_) (fun i' hi' => h.2.1 a i' hi') i hi
    have hlr : l.val < r := lt_trans hl a.isLt
    have := h.2.1 ⟨l.val, hlr⟩ i' (le_of_lt (lt_of_lt_of_le hl hi'))
    simpa [Formalism.QuantumDeterminants.eI] using this
  · refine ex_entry X t r j (fun i' l hi' hl => ?_) (fun i' hi' => h.2.2 i' j hj1 hj2 hi') i hi
    have := h.2.1 ⟨l.val, hl⟩ i' (le_of_lt (lt_of_lt_of_le hl hi'))
    simpa [Formalism.QuantumDeterminants.eI] using this

end GlobalTheory.CompanionTheory.BmuExpMem
