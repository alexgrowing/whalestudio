import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DvdPowZeroIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWittUnitaryModUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryGroupHenselStepFamiliesStatement

noncomputable section

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem pi_int {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) : ϖ ∈ Formalism.UG.intL L := by
  show Valued.v ϖ ≤ 1
  rw [hU.2.2.2.1]
  exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1)

theorem glint_entry {n : ℕ} {h : GL (Fin n) L} (hh : h ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)) (r s : Fin n) :
    (h : Matrix (Fin n) (Fin n) L) r s ∈ Formalism.UG.intL L := by
  obtain ⟨g0, hg0⟩ := hh
  rw [← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) r s).2

theorem mulVec_int {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, M r s ∈ Formalism.UG.intL L)
    {v : Fin n → L} (hv : ∀ r, v r ∈ Formalism.UG.intL L) (r : Fin n) : (M *ᵥ v) r ∈ Formalism.UG.intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun s _ => (Formalism.UG.intL L).mul_mem (hM r s) (hv s)

theorem dvdPow_mulVec {ϖ : L} {k : ℕ} {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, DvdPow ϖ k (M r s))
    {v : Fin n → L} (hv : ∀ r, v r ∈ Formalism.UG.intL L) (r : Fin n) : DvdPow ϖ k ((M *ᵥ v) r) := by
  simp only [Matrix.mulVec, dotProduct]
  refine dvdPow_sum _ _ fun s _ => ?_
  rw [mul_comm]; exact dvdPow_mul_int (hM r s) (hv s)

theorem hform_eq_dot (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (x y : Fin n → L) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_unitary (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (h : Formalism.UG.UJ σ J) (x y : Fin n → L) :
    Formalism.UG.hform σ J (((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ x)
      (((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ y) = Formalism.UG.hform σ J x y := by
  have hu : Formalism.UG.cT σ ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * J * ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = J := h.2
  rw [hform_eq_dot, hform_eq_dot]
  set H := ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  have e1 : (fun i => σ ((H *ᵥ x) i)) = (H.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i; exact RingHom.map_mulVec σ H x i
  rw [e1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  exact congrArg (· *ᵥ y) hu

end GlobalTheory.Hk3.IntWittMod

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem dvdPow_intMulVec {ϖ : L} {k : ℕ} {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, M r s ∈ Formalism.UG.intL L)
    {v : Fin n → L} (hv : ∀ r, DvdPow ϖ k (v r)) (r : Fin n) : DvdPow ϖ k ((M *ᵥ v) r) := by
  simp only [Matrix.mulVec, dotProduct]
  exact dvdPow_sum _ _ fun s _ => dvdPow_mul_int (hv s) (hM r s)

theorem indepMod_mulVec {ϖ : L} {ι : Type} [Fintype ι] {n : ℕ} {h : GL (Fin n) L}
    (hh : h ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)) {z : ι → Fin n → L} (hz : IndepMod ϖ z) :
    IndepMod ϖ (fun i => (h : Matrix (Fin n) (Fin n) L) *ᵥ z i) := by
  intro d hd hs i
  refine hz d hd (fun r => ?_) i
  set w : Fin n → L := ∑ j, d j • z j with hw
  have e1 : ∀ s, ((h : Matrix (Fin n) (Fin n) L) *ᵥ w) s = ∑ j, d j * ((h : Matrix (Fin n) (Fin n) L) *ᵥ z j) s := by
    intro s
    simp [hw, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply]
  have e2 : ∑ j, d j * z j r = (((h⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ ((h : Matrix (Fin n) (Fin n) L) *ᵥ w)) r := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    simp [hw, Finset.sum_apply]
  rw [e2]
  exact dvdPow_intMulVec (glint_entry ((Formalism.UG.GLint _ _).inv_mem hh)) (fun s => by rw [e1]; exact hs s) r

theorem indepMod_sub {ϖ : L} {ι : Type} [Fintype ι] {n : ℕ} {z : ι → Fin n → L} (hz : IndepMod ϖ z)
    (p : ι → Prop) [DecidablePred p] : IndepMod ϖ (fun i : {i // p i} => z i.1) := by
  intro d hd hs i
  let d' : ι → L := fun j => if hj : p j then d ⟨j, hj⟩ else 0
  have h1 : ∀ j, d' j ∈ Formalism.UG.intL L := by
    intro j; by_cases hj : p j
    · simp only [d', dif_pos hj]; exact hd _
    · simp only [d', dif_neg hj]; exact (Formalism.UG.intL L).zero_mem
  have h2 : ∀ r, ∑ j, d' j * z j r = ∑ j : {i // p i}, d j * z j.1 r := by
    intro r
    rw [← Fintype.sum_subtype_add_sum_subtype p (fun j => d' j * z j r)]
    have a1 : ∑ j : {i // ¬ p i}, d' j.1 * z j.1 r = 0 :=
      Finset.sum_eq_zero fun j _ => by simp [d', dif_neg j.2]
    rw [a1, add_zero]
    exact Finset.sum_congr rfl fun j _ => by simp [d', dif_pos j.2]
  have := hz d' h1 (fun r => by rw [h2]; exact hs r) i.1
  simpa [d', dif_pos i.2] using this

end GlobalTheory.Hk3.IntWittMod

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

theorem witt_mod_pow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (z z' : ι → Fin n' → L), (∀ i, 1 ≤ a i) →
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j)) (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a i) ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ _ ϖ σ q hU hq n' JT hJT hJh ι _ a z z' ha hz hz' hiz hiz' hG
  classical
  have hϖ := pi_int hU
  have key : ∀ k, 1 ≤ k → ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
      (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, DvdPow ϖ (min (a i) k) ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      obtain ⟨h, hh, hc⟩ := GlobalTheory.T.integral_witt_unitary_mod_uniformizer L ϖ σ q hU hq n' JT hJT hJh ι z z' hz hz' hiz hiz'
        (fun i j => dvdPow_mono hϖ (le_min (ha i) (ha j)) (hG i j))
      refine ⟨h, hh, fun i r => ?_⟩
      rw [min_eq_right (ha i)]; exact hc i r
    | succ k hk ih =>
      obtain ⟨h, hh, hc⟩ := ih
      have hHint := glint_entry hh
      obtain ⟨g, hg, hg1, hgc⟩ := GlobalTheory.T.unitaryGroup_hensel_step_families L ϖ σ q hU hq n' JT hJT hJh {i // k < a i}
        (fun i => ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i.1) (fun i => z' i.1) k hk
        (fun i r => mulVec_int hHint (hz i.1) r) (fun i r => hz' i.1 r)
        (indepMod_sub (indepMod_mulVec hh hiz) (fun i => k < a i))
        (fun i r => by
          have h0 := hc i.1 r
          rw [min_eq_right i.2.le] at h0
          have h1 := dvdPow_neg h0
          rwa [neg_sub] at h1)
        (fun i j => by
          simp only [hform_unitary]
          exact dvdPow_mono hϖ (le_min i.2 j.2) (hG i.1 j.1))
      refine ⟨g * h, (Formalism.UG.GLint _ _).mul_mem hg hh, fun i r => ?_⟩
      have e : (((g * h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)) : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i
          = ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) := by
        simp [Matrix.mulVec_mulVec]
      rw [e]
      by_cases hki : k < a i
      · rw [min_eq_right (Nat.succ_le_of_lt hki)]
        exact hgc ⟨i, hki⟩ r
      · push_neg at hki
        rw [min_eq_left (by omega)]
        have h2 := hc i r
        rw [min_eq_left hki] at h2
        have h1 : DvdPow ϖ (a i) (((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) - 1) *ᵥ
            (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r) :=
          dvdPow_mono hϖ hki (dvdPow_mulVec (fun r s => by simpa [Matrix.sub_apply] using hg1 r s)
            (mulVec_int hHint (hz i)) r)
        have e2 : (((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r - z' i r
            = (((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) - 1) *ᵥ
              (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r)
              + ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]; ring
        rw [e2]; exact dvdPow_add h1 h2
  obtain ⟨h, hh, hc⟩ := key (1 + ∑ i, a i) (by omega)
  refine ⟨h, hh, fun i r => ?_⟩
  have h0 := hc i r
  have hle : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
  rwa [min_eq_left (by omega)] at h0

end GlobalTheory.Hk3.IntWittMod

end
