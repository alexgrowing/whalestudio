import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.Interface
import Formalism.LocalToGlobal.CharacterGerms.ScaledSecondIntegral
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataAdaptedChainData

noncomputable section

open scoped BigOperators
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.GoodCorank

variable {C : Type} [Field C] {V : VF C}

theorem div_int {x y : C} (h : V.v y ≤ V.v x) : V.Ge 0 (x / y) := by
  by_cases hy : y = 0
  · subst hy; simpa using VF.Ge.zero (V := V) 0
  · have e : V.v x = V.v y + V.v (x / y) := by
      rw [← V.v.map_mul, mul_div_cancel₀ _ hy]
    have hy' : V.v y ≠ ⊤ := by
      intro h0
      have h1 : V.v (y * y⁻¹) = 0 := by rw [mul_inv_cancel₀ hy, V.v.map_one]
      rw [V.v.map_mul, h0, top_add] at h1
      exact WithTop.top_ne_zero h1
    unfold VF.Ge
    rw [e] at h
    have h2 : V.v y + 0 ≤ V.v y + V.v (x / y) := by simpa using h
    simpa using (WithTop.add_le_add_iff_left hy').mp h2

theorem ge_ite (p : Prop) [Decidable p] : V.Ge 0 (if p then (1 : C) else 0) := by
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem exists_cut {N : ℕ} (φ : Fin (N + 1) → C) :
    ∃ A : Fin N → Fin (N + 1) → C, IsSat V A ∧ ∀ ν, ∑ k, A ν k * φ k = 0 := by
  obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ (fun k => V.v (φ k)) Finset.univ_nonempty
  refine ⟨fun ν k => (if k = k0.succAbove ν then 1 else 0) -
      (φ (k0.succAbove ν) / φ k0) * (if k = k0 then 1 else 0), ⟨fun ν k => ?_,
      fun k c => if k = k0.succAbove c then 1 else 0, fun k c => ge_ite _, fun c c' => ?_⟩, fun ν => ?_⟩
  · exact (ge_ite _).sub ((div_int (hk0 _ (Finset.mem_univ _))).mul_int (ge_ite _))
  · simp [Fin.succAbove_ne, eq_comm]
  · simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h0 : φ k0 = 0
    · have h1 := hk0 (k0.succAbove ν) (Finset.mem_univ _)
      rw [h0, V.v.map_zero, top_le_iff] at h1
      have h2 : φ (k0.succAbove ν) = 0 := by
        by_contra hy
        have h3 : V.v (φ (k0.succAbove ν) * (φ (k0.succAbove ν))⁻¹) = 0 := by
          rw [mul_inv_cancel₀ hy, V.v.map_one]
        rw [V.v.map_mul, h1, top_add] at h3
        exact WithTop.top_ne_zero h3
      simp [h0, h2]
    · rw [div_mul_cancel₀ _ h0, sub_self]

theorem isSat_comp {M N : ℕ} {σ : Type} [Fintype σ] {A : Fin M → Fin N → C} {w : Fin N → σ → C}
    (hA : IsSat V A) (hw : IsSat V w) : IsSat V (fun ν c => ∑ k, A ν k * w k c) := by
  obtain ⟨hA0, A', hA', hAA⟩ := hA
  obtain ⟨hw0, w', hw', hww⟩ := hw
  refine ⟨fun ν c => VF.Ge.sum fun k _ => (hA0 _ _).mul_int (hw0 _ _),
    fun x c => ∑ k, w' x k * A' k c, fun x c => VF.Ge.sum fun k _ => (hw' _ _).mul_int (hA' _ _),
    fun c c' => ?_⟩
  have e1 : Matrix.of A * Matrix.of A' = 1 := by
    ext i j; simpa [Matrix.mul_apply, Matrix.one_apply] using hAA i j
  have e2 : Matrix.of w * Matrix.of w' = 1 := by
    ext i j; simpa [Matrix.mul_apply, Matrix.one_apply] using hww i j
  have e3 : (Matrix.of A * Matrix.of w) * (Matrix.of w' * Matrix.of A') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.of w), e2, Matrix.one_mul, e1]
  simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun e3 c) c'

theorem exists_sat_ker {I κ : Type} [Fintype I] [DecidableEq I] (P : Finset I) (φ : κ → I → C) (S : Finset κ) :
    ∃ (N : ℕ) (w : Fin N → I → C), IsSat V w ∧ (∀ ν c, c ∉ P → w ν c = 0) ∧
      (∀ ν, ∀ b ∈ S, ∑ c, w ν c * φ b c = 0) ∧ P.card ≤ N + S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨P.card, fun ν c => if c = (P.equivFin.symm ν : I) then 1 else 0, ⟨fun ν c => ge_ite _,
      fun c ν => if c = (P.equivFin.symm ν : I) then 1 else 0, fun c ν => ge_ite _, fun ν ν' => ?_⟩,
      fun ν c hc => ?_, by simp, by simp⟩
    · simp [Subtype.val_inj, eq_comm]
    · refine if_neg ?_
      rintro rfl
      exact hc (P.equivFin.symm ν).2
  | insert b S hb ih =>
    obtain ⟨N, w, hs, hP, hφ, hN⟩ := ih
    rw [Finset.card_insert_of_notMem hb]
    cases N with
    | zero => exact ⟨0, w, hs, hP, fun ν => ν.elim0, by omega⟩
    | succ N =>
      obtain ⟨A, hA, hA0⟩ := exists_cut (V := V) (fun k => ∑ c, w k c * φ b c)
      have key : ∀ ν b', ∑ c, (∑ k, A ν k * w k c) * φ b' c = ∑ k, A ν k * ∑ c, w k c * φ b' c := by
        intro ν b'
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      refine ⟨N, fun ν c => ∑ k, A ν k * w k c, isSat_comp hA hs, fun ν c hc => ?_, fun ν b' hb' => ?_, by omega⟩
      · simp [hP _ c hc]
      · rw [key]
        rcases Finset.mem_insert.mp hb' with rfl | hb'
        · exact hA0 ν
        · simp [hφ _ b' hb']

variable {d : ℕ} {I J : Type} [Fintype I] [DecidableEq I]

theorem good_of_int (G : Cart V d I J) {a : ZMod d} {u : I → C} {y : ℕ → I ⊕ J → C} (hy : G.IsCurve a u y)
    (h1 : ∀ b, V.Ge 0 (y 1 (Sum.inl b))) : ∃ x, G.Good a u x := by
  obtain ⟨z, hz, hz0, hzp⟩ := G.t4 (a + 1) (fun b => y 1 (Sum.inl b)) h1
    (fun b hb => hy.2.2 1 _ (by simpa using hb))
  refine ⟨y - Vpow 1 z, ⟨G.Ty.sub_mem hy.1 (G.V_mem _ hz), ?_, fun i n hn => ?_⟩, fun c => ?_⟩
  · funext n
    simp [Vpow, hy.2.1]
  · cases i with
    | zero => simp [Vpow, hy.2.2 0 n hn]
    | succ i =>
      have : z i n = 0 := hzp i n (by
        intro hc; apply hn; rw [hc]; push_cast; ring)
      simp [Vpow, hy.2.2 _ n hn, this]
  · simp [Vpow, hz0]

theorem good_of_ker (G : Cart V d I J) {a : ZMod d} (r : I → I → C)
    (hr : ∀ b c, r b c ^ V.l = (V.l : C) * G.std c 1 (Sum.inl b)) {u : I → C} (hu : ∀ c, V.Ge 0 (u c))
    (hp : ∀ c, G.ty (Sum.inl c) ≠ a → u c = 0)
    (hk : ∀ b, G.ty (Sum.inl b) = a + 1 → ∑ c, u c * r b c = 0) : ∃ x, G.Good a u x := by
  have lpos : ∀ k : ℕ, V.l ^ k ≠ 0 := fun k => (pow_pos V.l_prime.pos k).ne'
  have hy : G.IsCurve a u (∑ c, teich V.l (u c) (G.std c)) := by
    refine ⟨G.Ty.sum_mem fun c _ => G.teich_mem _ (hu c) _ (G.std_spec c).1, ?_, fun i n hn => ?_⟩
    · funext n
      have : ∀ b, G.std b 0 n = Sum.elim (Pi.single b 1) 0 n := fun b => by rw [(G.std_spec b).2.1]
      simp only [Finset.sum_apply, teich, this, pow_zero, pow_one]
      cases n with
      | inl c => simp [Pi.single_apply]
      | inr j => simp
    · simp only [Finset.sum_apply, teich]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : G.ty (Sum.inl c) = a
      · rw [(G.std_spec c).2.2 i n (by rwa [hc]), mul_zero]
      · rw [hp c hc, zero_pow (lpos i), zero_mul]
  refine good_of_int G hy fun b => ?_
  by_cases hb : G.ty (Sum.inl b) = a + 1
  · have hrint : ∀ c, V.Ge 0 (r b c) := fun c => by
      refine GlobalTheory.AdaptedChain.int_of_pow V.l_prime.ne_zero ?_
      rw [hr]
      simpa using (G.bound0 1 _ (G.std_spec c).1 (Sum.inl b)).l_mul
    have hf := (GlobalTheory.AdaptedChain.frob_sum Finset.univ (fun c => u c * r b c)
      (fun c => (hu c).mul_int (hrint c)) 1).neg
    rw [hk b hb, zero_pow (lpos 1), zero_sub, neg_neg] at hf
    have e : ∑ c, (u c * r b c) ^ V.l ^ 1 =
        (V.l : C) * (∑ c, teich V.l (u c) (G.std c)) 1 (Sum.inl b) := by
      simp only [Finset.sum_apply, teich, pow_one, mul_pow, hr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e] at hf
    simpa using hf.of_l_mul
  · rw [hy.2.2 1 _ (by simpa using hb)]
    exact VF.Ge.zero 0

theorem exists_good_sat (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J]
    [DecidableEq I] (G : Cart V d I J) (a : ZMod d) :
    ∃ (N : ℕ) (w : Fin N → I → C) (x : Fin N → ℕ → I ⊕ J → C), (∀ ν, G.Good a (w ν) (x ν)) ∧
      (∀ ν c, G.ty (Sum.inl c) ≠ a → w ν c = 0) ∧ IsSat V w ∧
      (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a).card ≤
        N + (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a + 1).card := by
  have hex : ∀ b c : I, ∃ r : C, r ^ V.l = (V.l : C) * G.std c 1 (Sum.inl b) := fun b c =>
    IsAlgClosed.exists_pow_nat_eq _ V.l_prime.pos
  choose r hr using hex
  obtain ⟨N, w, hs, hP, hφ, hN⟩ := exists_sat_ker (V := V)
    (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a) r
    (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a + 1)
  have hp : ∀ ν c, G.ty (Sum.inl c) ≠ a → w ν c = 0 := fun ν c hc => hP ν c (by simpa using hc)
  have hx : ∀ ν, ∃ x, G.Good a (w ν) x := fun ν =>
    good_of_ker G r hr (hs.1 ν) (hp ν) fun b hb => hφ ν b (by simpa using hb)
  choose x hx using hx
  exact ⟨N, w, x, hx, hp, hs, hN⟩

end GlobalTheory.GoodCorank

end
