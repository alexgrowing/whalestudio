import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MiTop.FirstVec

section Mat

variable {R : Type} [CommRing R] {ρ : ℕ}

def UniRow (U : Matrix (Fin ρ) (Fin ρ) R) (j : Fin ρ) : Prop := ∀ i, i ≤ j → U j i = if i = j then 1 else 0

def Keeps (U V : Matrix (Fin ρ) (Fin ρ) R) : Prop :=
  ∀ i j : Fin ρ, i < j → (∀ p q : Fin ρ, q ≤ p → U p i * V j q = 0) ∧
    ∑ p : Fin ρ, ∑ q : Fin ρ, (if q.1 = p.1 + 1 then U p i * V j q else 0) = if j.1 = i.1 + 1 then 1 else 0

theorem uniRow_step {U V : Matrix (Fin ρ) (Fin ρ) R} (h : Keeps U V) {j j' : Fin ρ} (hj : j.1 = j'.1 + 1) (hV : UniRow V j) :
    UniRow U j' := by
  intro i hi
  have hij : i < j := by rw [Fin.lt_def]; rw [Fin.le_def] at hi; omega
  obtain ⟨h1, h2⟩ := h i j hij
  have hjj : V j j = 1 := by simpa using hV j le_rfl
  have hU : ∀ p, j ≤ p → U p i = 0 := fun p hp => by simpa [hjj] using h1 p j hp
  rw [Finset.sum_eq_single j', Finset.sum_eq_single j, if_pos hj, hjj, mul_one] at h2
  · rw [h2]
    refine if_congr ?_ rfl rfl
    rw [Fin.ext_iff]; omega
  · intro q _ hq
    rw [if_neg fun e => hq (Fin.ext (by omega))]
  · simp
  · intro p _ hp
    refine Finset.sum_eq_zero fun q _ => ?_
    split_ifs with e
    · rcases lt_or_ge p j with hp' | hp'
      · have hq : q < j := by
          have : p.1 ≠ j'.1 := fun e' => hp (Fin.ext e')
          rw [Fin.lt_def] at hp' ⊢; omega
        rw [hV q hq.le, if_neg hq.ne, mul_zero]
      · rw [hU p hp', zero_mul]
    · rfl
  · simp

theorem uniRow_all {U V : Matrix (Fin ρ) (Fin ρ) R} (h : Keeps U V) (h' : Keeps V U)
    (hU : ∀ j : Fin ρ, j.1 + 1 = ρ → UniRow U j) (hV : ∀ j : Fin ρ, j.1 + 1 = ρ → UniRow V j) (j : Fin ρ) : UniRow U j := by
  have key : ∀ m : ℕ, ∀ j : Fin ρ, j.1 + 1 + m = ρ → UniRow U j ∧ UniRow V j := by
    intro m
    induction m with
    | zero => exact fun j hj => ⟨hU j hj, hV j hj⟩
    | succ m ih =>
      intro j hj
      obtain ⟨a, b⟩ := ih ⟨j.1 + 1, by omega⟩ (by simp only; omega)
      exact ⟨uniRow_step h rfl b, uniRow_step h' rfl a⟩
  exact (key (ρ - (j.1 + 1)) j (by omega)).1

theorem mul_single_mul (U V : Matrix (Fin ρ) (Fin ρ) R) (i j : Fin ρ) (s : R) :
    U * (Matrix.single i j s * V) = Matrix.of fun p q => s * (U p i * V j q) := by
  ext p q
  rw [← Matrix.mul_assoc]
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]
  ring

theorem sum_single (i j : Fin ρ) (s : R) :
    ∑ p : Fin ρ, ∑ q : Fin ρ, (if q.1 = p.1 + 1 then Matrix.single i j s p q else 0) = s * if j.1 = i.1 + 1 then 1 else 0 := by
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro q _ hq
    simp [hq.symm]
  · simp
  · intro p _ hp
    simp [hp.symm]
  · simp

theorem sum_scal (f : Fin ρ → Fin ρ → R) (s : R) :
    ∑ p : Fin ρ, ∑ q : Fin ρ, (if q.1 = p.1 + 1 then Matrix.of (fun p q => s * f p q) p q else 0) =
      s * ∑ p : Fin ρ, ∑ q : Fin ρ, (if q.1 = p.1 + 1 then f p q else 0) := by
  simp [Finset.mul_sum]

theorem last_dot (w : Fin ρ → R) (j : Fin ρ) (hj : j.1 + 1 = ρ) : (fun i : Fin ρ => if i.1 + 1 = ρ then (1 : R) else 0) ⬝ᵥ w = w j := by
  rw [dotProduct, Finset.sum_eq_single j]
  · simp [hj]
  · intro p _ hp
    rw [if_neg fun e => hp (Fin.ext (by omega)), zero_mul]
  · simp

theorem mulVec_single_at {n : ℕ} (P : Matrix (Fin ρ) (Fin n) R) (J : Matrix (Fin n) (Fin ρ) R) (i j : Fin ρ) (s : R) :
    (0 : R) + ((0 : Fin ρ → R) + P *ᵥ (J *ᵥ Pi.single i s)) j = s * (P * J) j i := by
  rw [Matrix.mulVec_mulVec]; simp [mul_comm]

theorem zero_tidy (a : R) (l : Fin ρ → R) : 0 + a + l ⬝ᵥ 0 = a := by simp

end Mat

variable {D : D7} {S S₀ S₁ : HSp D} {ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ}

theorem eq_of_psiE (hψ : ∃ s, psiE ψ s ≠ 1) {x y : AE D} (hx : x ∈ (incA D).range) (hy : y ∈ (incA D).range)
    (h : ∀ s, psiE ψ (s * x) = psiE ψ (s * y)) : x = y := by
  obtain ⟨t, ht⟩ := sub_mem hx hy
  by_contra hne
  have ht0 : t ≠ 0 := fun e => hne (by rw [← sub_eq_zero, ← ht, e, map_zero])
  obtain ⟨s, hs⟩ := hψ
  have hadd : ∀ a b, psiE ψ (a + b) = psiE ψ a * psiE ψ b := fun a b => by
    unfold psiE; rw [map_add, AddChar.map_add_eq_mul]
  have h0 : psiE ψ (0 : AE D) = 1 := by unfold psiE; rw [map_zero, AddChar.map_zero_eq_one]
  apply hs
  have e1 : s * incA D t⁻¹ * x = s + s * incA D t⁻¹ * y := by
    have : x = incA D t + y := by rw [ht]; ring
    rw [this, mul_add, mul_assoc s _ (incA D t), ← map_mul, inv_mul_cancel₀ ht0, map_one, mul_one]
  have e2 := h (s * incA D t⁻¹)
  rw [e1, hadd] at e2
  have e3 := hadd (s * incA D t⁻¹ * y) (-(s * incA D t⁻¹ * y))
  rw [add_neg_cancel, h0] at e3
  exact (mul_eq_right₀ (left_ne_zero_of_mul_eq_one e3.symm)).1 e2

theorem simpleSum_eq (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (n : GA D S) :
    simpleSum d z n = upSum (d.pX ⬝ (mt S n ⬝ d.jX)) + ell D ρ ⬝ᵥ (d.pX *ᵥ (mt S n *ᵥ (d.j0 *ᵥ ratV z))) := by
  unfold simpleSum blockX coefX
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem psiBes_one (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (n : GA D S) :
    psiBes ψ d 1 z n = psiE ψ (simpleSum d z n) :=
  congrArg (psiE ψ) ((congrArg (· * simpleSum d z n) (incA D).map_one).trans (one_mul _))

theorem pX_Z (d : HypDec S S₀ ρ) (y : Fin S₀.rank → AE D) : d.pX *ᵥ (d.j0 *ᵥ y) = 0 := by
  rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]

theorem flag_act (d : HypDec S S₀ ρ) (y : Fin S₀.rank → AE D) {n : GA D S} (hn : n ∈ flagN d) :
    (∀ p q : Fin ρ, q ≤ p → (d.pX ⬝ (mt S n ⬝ d.jX)) p q = (1 : Mx D ρ ρ) p q) ∧
      ∃ β, mt S n *ᵥ (d.j0 *ᵥ y) = d.j0 *ᵥ y + d.jX *ᵥ β := by
  obtain ⟨u, hu, b, c, rfl⟩ := Decomp.flag_decomp d hn
  refine ⟨fun p q hpq => ?_, (u.1 ⬝ b) *ᵥ y, ?_⟩
  · rw [Decomp.mt_flag_jX, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
    obtain ⟨h1, h2⟩ := (GlobalTheory.UniIndexPrime.mem_uniSub u).1 hu
    rcases hpq.eq_or_lt with e | e
    · subst e; rw [h2, Matrix.one_apply_eq]
    · rw [h1 p q e, Matrix.one_apply_ne e.ne']
  · rw [Matrix.mulVec_mulVec, Decomp.flag_unipotent_product_anisotropic_action, Matrix.add_mulVec, Matrix.mulVec_mulVec]

theorem exists_transl (d : HypDec S S₀ ρ) {z : Fin S₀.rank → D.host.E} (hz : z ≠ 0) (β : Fin ρ → AE D) :
    ∃ n ∈ flagN d, mt S n ⬝ d.jX = d.jX ∧ mt S n *ᵥ (d.j0 *ᵥ ratV z) = d.j0 *ᵥ ratV z + d.jX *ᵥ β := by
  obtain ⟨l, hl⟩ := Function.ne_iff.1 hz
  let b : Mx D ρ S₀.rank := Matrix.vecMulVec β (Pi.single l (incA D (z l)⁻¹))
  refine ⟨d.levi 1 * (d.nB b * d.nC 0), (Decomp.mem_flag_iff d).2 ⟨1, one_mem _, b, 0, rfl⟩, ?_, ?_⟩
  · rw [Decomp.mt_flag_jX]; exact Matrix.mul_one _
  · rw [Matrix.mulVec_mulVec, Decomp.flag_unipotent_product_anisotropic_action, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    congr 2
    rw [Units.val_one, Matrix.one_mul, Matrix.vecMulVec_mulVec, single_dotProduct]
    have : incA D (z l)⁻¹ * ratV z l = 1 := by
      change incA D _ * incA D (z l) = 1
      rw [← map_mul, inv_mul_cancel₀ hl, map_one]
    rw [this]; simp

theorem exists_elem (d : HypDec S S₀ ρ) (y : Fin S₀.rank → AE D) {i j : Fin ρ} (hij : i < j) (s : AE D) :
    ∃ n ∈ flagN d, mt S n ⬝ d.jX = d.jX ⬝ (1 + Matrix.single i j s) ∧ mt S n *ᵥ (d.j0 *ᵥ y) = d.j0 *ᵥ y := by
  obtain ⟨u, hu, hu1⟩ := Decomp.exists_unit (D := D) (T := Matrix.single i j s) (fun p q hpq => by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact absurd hij (not_lt.2 hpq))
  refine ⟨d.levi u * (d.nB 0 * d.nC 0), (Decomp.mem_flag_iff d).2 ⟨u, hu, 0, 0, rfl⟩, ?_, ?_⟩
  · rw [Decomp.mt_flag_jX, hu1]
  · rw [Matrix.mulVec_mulVec, Decomp.flag_unipotent_product_anisotropic_action, Matrix.mul_zero, Matrix.mul_zero, add_zero]

theorem upSum_one : upSum (1 : Mx D ρ ρ) = 0 := by
  unfold upSum
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  split_ifs with e
  · exact Matrix.one_apply_ne fun e' => by subst e'; omega
  · rfl

theorem upSum_add (A B : Mx D ρ ρ) : upSum (A + B) = upSum A + upSum B := by
  unfold upSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> simp

theorem entry_rat (d : HypDec S S₀ ρ) (d' : HypDec S S₁ ρ) (p q : Fin ρ) : (d'.pX ⬝ d.jX) p q ∈ (incA D).range := by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem ⟨_, rfl⟩ ⟨_, rfl⟩

section Two

variable {d : HypDec S S₀ ρ} {d' : HypDec S S₁ ρ} {z : Fin S₀.rank → D.host.E} {z' : Fin S₁.rank → D.host.E}

theorem jX_eq (hz : z ≠ 0) (hZ : d.j0 *ᵥ ratV z = d'.j0 *ᵥ ratV z') (hN : flagN d = flagN d') :
    d.jX = d'.jX ⬝ (d'.pX ⬝ d.jX) := by
  ext r i
  obtain ⟨n, hn, -, h2⟩ := exists_transl d hz (Pi.single i 1)
  obtain ⟨β, hβ⟩ := (flag_act d' (ratV z') (hN ▸ hn)).2
  rw [← hZ, h2, add_right_inj] at hβ
  have e : d'.jX *ᵥ (d'.pX *ᵥ (d.jX *ᵥ Pi.single i 1)) = d.jX *ᵥ Pi.single i 1 := by
    rw [hβ, Matrix.mulVec_mulVec β, d'.pX_jX, Matrix.one_mulVec]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at e
  exact (congrFun e r).symm

theorem last_row (hψ : ∃ s, psiE ψ s ≠ 1) (hz : z ≠ 0) (hz' : z' ≠ 0) (hZ : d.j0 *ᵥ ratV z = d'.j0 *ᵥ ratV z')
    (hN : flagN d = flagN d') (hc : ∀ n ∈ flagN d, psiBes ψ d 1 z n = psiBes ψ d' 1 z' n) (j : Fin ρ) (hj : j.1 + 1 = ρ) :
    UniRow (d'.pX ⬝ d.jX) j := by
  intro i _
  have hl : ∀ w : Fin ρ → AE D, ell D ρ ⬝ᵥ w = w j := fun w => last_dot w j hj
  refine eq_of_psiE hψ (entry_rat d d' j i) (by split_ifs; exacts [one_mem _, zero_mem _]) fun s => ?_
  obtain ⟨n, hn, h1, h2⟩ := exists_transl d hz (Pi.single i s)
  have h := hc n hn
  have h1' : mt S n ⬝ d'.jX = d'.jX := by
    conv_lhs => rw [jX_eq hz' hZ.symm hN.symm, ← Matrix.mul_assoc, h1, ← jX_eq hz' hZ.symm hN.symm]
  have e1 : simpleSum d z n = s * if i = j then 1 else 0 := by
    rw [simpleSum_eq, h1, h2, Matrix.mulVec_add, pX_Z, hl, d.pX_jX, upSum_one, mulVec_single_at, d.pX_jX, Matrix.one_apply]
    exact congrArg (s * ·) (if_congr eq_comm rfl rfl)
  have e2 : simpleSum d' z' n = s * (d'.pX ⬝ d.jX) j i := by
    rw [simpleSum_eq, h1', ← hZ, h2, Matrix.mulVec_add, hZ, pX_Z, hl, d'.pX_jX, upSum_one, mulVec_single_at]
  rw [psiBes_one, psiBes_one, e1, e2] at h
  exact h.symm

set_option maxHeartbeats 1000000 in
theorem keeps (hψ : ∃ s, psiE ψ s ≠ 1) (hz' : z' ≠ 0) (hZ : d.j0 *ᵥ ratV z = d'.j0 *ᵥ ratV z')
    (hN : flagN d = flagN d') (hc : ∀ n ∈ flagN d, psiBes ψ d 1 z n = psiBes ψ d' 1 z' n) :
    Keeps (d'.pX ⬝ d.jX) (d.pX ⬝ d'.jX) := by
  intro i j hij
  have hV := jX_eq hz' hZ.symm hN.symm
  have key : ∀ (s : AE D) (n : GA D S), mt S n ⬝ d.jX = d.jX ⬝ (1 + Matrix.single i j s) →
      d'.pX ⬝ (mt S n ⬝ d'.jX) = 1 + Matrix.of fun p q => s * ((d'.pX ⬝ d.jX) p i * (d.pX ⬝ d'.jX) j q) := fun s n h1 => by
    conv_lhs => rw [hV, ← Matrix.mul_assoc (mt S n), h1, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, ← hV, Matrix.mul_add,
      d'.pX_jX, Matrix.mul_assoc, ← Matrix.mul_assoc d'.pX, mul_single_mul]
  refine ⟨fun p q hpq => ?_, ?_⟩
  · obtain ⟨n, hn, h1, -⟩ := exists_elem d (ratV z) hij 1
    have := (flag_act d' (ratV z') (hN ▸ hn)).1 p q hpq
    rw [key 1 n h1] at this
    rw [Matrix.add_apply, add_eq_left, Matrix.of_apply, one_mul] at this
    exact this
  · refine eq_of_psiE hψ (sum_mem fun p _ => sum_mem fun q _ => ?_) (by split_ifs; exacts [one_mem _, zero_mem _]) fun s => ?_
    · split_ifs
      exacts [mul_mem (entry_rat d d' _ _) (entry_rat d' d _ _), zero_mem _]
    obtain ⟨n, hn, h1, h2⟩ := exists_elem d (ratV z) hij s
    have h := hc n hn
    have e1 : simpleSum d z n = s * if j.1 = i.1 + 1 then 1 else 0 := by
      rw [simpleSum_eq, h1, h2, pX_Z, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul, upSum_add, upSum_one, zero_tidy]
      exact sum_single i j s
    have e2 : simpleSum d' z' n = s * ∑ p : Fin ρ, ∑ q : Fin ρ,
        (if q.1 = p.1 + 1 then (d'.pX ⬝ d.jX) p i * (d.pX ⬝ d'.jX) j q else 0) := by
      rw [simpleSum_eq, key s n h1, ← hZ, h2, hZ, pX_Z, upSum_add, upSum_one, zero_tidy]
      exact sum_scal _ s
    rw [psiBes_one, psiBes_one, e1, e2] at h
    exact h.symm

theorem first_eq (hψ : ∃ s, psiE ψ s ≠ 1) (hz : z ≠ 0) (hz' : z' ≠ 0) (hZ : d.j0 *ᵥ ratV z = d'.j0 *ᵥ ratV z')
    (hN : flagN d = flagN d') (hc : ∀ n ∈ flagN d, psiBes ψ d 1 z n = psiBes ψ d' 1 z' n) (h0 : 0 < ρ) (r : Fin S.rank) :
    d.jX r ⟨0, h0⟩ = d'.jX r ⟨0, h0⟩ := by
  have hc' : ∀ n ∈ flagN d', psiBes ψ d' 1 z' n = psiBes ψ d 1 z n := fun n hn => (hc n (hN ▸ hn)).symm
  have hU := uniRow_all (keeps hψ hz' hZ hN hc) (keeps hψ hz hZ.symm hN.symm hc') (last_row hψ hz hz' hZ hN hc)
    (last_row hψ hz' hz hZ.symm hN.symm hc')
  rw [jX_eq hz hZ hN, Matrix.mul_apply, Finset.sum_eq_single ⟨0, h0⟩]
  · rw [hU _ _ le_rfl, if_pos rfl, mul_one]
  · intro p _ hp
    rw [hU p ⟨0, h0⟩ (Nat.zero_le _), if_neg hp.symm, mul_zero]
  · exact fun e => absurd (Finset.mem_univ _) e

end Two

end GlobalTheory.MiTop.FirstVec

end
