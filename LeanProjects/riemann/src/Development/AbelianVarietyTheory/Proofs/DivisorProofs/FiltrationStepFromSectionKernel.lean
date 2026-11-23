import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.PositionRel

variable {R S : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

lemma sameBlock_of_not {a b c : Ix R S} (hab : ¬ sameBlock a b) (hbc : ¬ sameBlock b c) : sameBlock a c := by
  cases a <;> cases b <;> cases c <;> simp_all [sameBlock]

lemma sameBlock_symm' {a b : Ix R S} (h : sameBlock a b) : sameBlock b a := by
  cases a <;> cases b <;> simp_all [sameBlock]

lemma sameBlock_trans' {a b c : Ix R S} (hab : sameBlock a b) (hbc : sameBlock b c) : sameBlock a c := by
  cases a <;> cases b <;> cases c <;> simp_all [sameBlock]

lemma isPC_eNC (x : NC R S) : IsPC (eNC x) := by
  intro a b hab
  simp only [eNC, Eab, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    exact absurd (h1 ▸ h2 ▸ hab) x.2
  · rfl

lemma isKC_comm_PC {X Y : Mat R S} (hX : IsPC X) (hY : IsPC Y) : IsKC (X * Y - Y * X) := by
  intro u v huv
  have h1 : ∀ (A B : Mat R S), IsPC A → IsPC B → (A * B) u v = 0 := by
    intro A B hA hB
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun w _ => ?_
    by_cases huw : sameBlock u w
    · rw [hA u w huw, zero_mul]
    · rw [hB w v (sameBlock_of_not (fun h => huw (sameBlock_symm' h)) huv), mul_zero]
  rw [Matrix.sub_apply, h1 X Y hX hY, h1 Y X hY hX, sub_zero]

lemma isPC_comm_KC {Z X : Mat R S} (hZ : IsKC Z) (hX : IsPC X) : IsPC (Z * X - X * Z) := by
  intro u v huv
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  have e1 : ∑ w, Z u w * X w v = 0 := Finset.sum_eq_zero fun w _ => by
    by_cases huw : sameBlock u w
    · rw [hX w v (sameBlock_trans' (sameBlock_symm' huw) huv), mul_zero]
    · rw [hZ u w huw, zero_mul]
  have e2 : ∑ w, X u w * Z w v = 0 := Finset.sum_eq_zero fun w _ => by
    by_cases huw : sameBlock u w
    · rw [hX u w huw, zero_mul]
    · rw [hZ w v (fun h => huw (sameBlock_trans' huv (sameBlock_symm' h))), mul_zero]
  rw [e1, e2, sub_zero]

variable (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)

lemma word_zero (h : Fin 0 → NC R S) : word act h = 1 := by simp [word]

lemma word_succ {j : ℕ} (h : Fin (j + 1) → NC R S) :
    word act h = act (eNC (h 0)) * word act (Fin.tail h) := by
  simp [word, List.ofFn_succ, Fin.tail]

lemma word_cons {j : ℕ} (x : NC R S) (h : Fin j → NC R S) :
    word act (Fin.cons x h : Fin (j + 1) → NC R S) = act (eNC x) * word act h := by
  rw [word_succ, Fin.cons_zero, Fin.tail_cons]

lemma filt_mono {m m' : ℕ} (hm : m ≤ m') : filt act N m ≤ filt act N m' := by
  refine iSup_le fun j => ?_
  exact le_iSup (fun j' : Fin (m' + 1) => LinearMap.range (phiN act N j')) ⟨j, by omega⟩

lemma word_mem {j m : ℕ} (hj : j ≤ m) (h : Fin j → NC R S) (n : N) : word act h n ∈ filt act N m := by
  have h1 : word act h n ∈ LinearMap.range (phiN act N j) := by
    refine ⟨fun g => if g = h then n else 0, ?_⟩
    rw [phiN_apply, Finset.sum_eq_single h (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have h2 : LinearMap.range (phiN act N j) ≤ filt act N j :=
    le_iSup (fun j' : Fin (j + 1) => LinearMap.range (phiN act N j')) ⟨j, by omega⟩
  exact filt_mono act N hj (h2 h1)

lemma mem_filt_zero (n : N) : (n : V) ∈ filt act N 0 := by
  have := word_mem act N le_rfl (Fin.elim0 : Fin 0 → NC R S) n
  rwa [word_zero, Module.End.one_apply] at this

lemma filt_map {m m' : ℕ} (T : V →ₗ[ℂ] V)
    (hT : ∀ j ≤ m, ∀ (h : Fin j → NC R S) (n : N), T (word act h n) ∈ filt act N m') :
    ∀ v ∈ filt act N m, T v ∈ filt act N m' := by
  intro v hv
  have hv' : v ∈ ⨆ j : Fin (m + 1), LinearMap.range (phiN act N j) := hv
  refine Submodule.iSup_induction (fun j : Fin (m + 1) => LinearMap.range (phiN act N j))
    (motive := fun v => T v ∈ filt act N m') hv' ?_ (by simp) (fun x y hx hy => by rw [map_add]; exact add_mem hx hy)
  rintro j _ ⟨Ψ, rfl⟩
  rw [phiN_apply, map_sum]
  exact Submodule.sum_mem _ fun g _ => hT j (Nat.lt_succ_iff.mp j.isLt) g (Ψ g)

lemma filt_X {m : ℕ} (x : NC R S) : ∀ v ∈ filt act N m, act (eNC x) v ∈ filt act N (m + 1) :=
  filt_map act N (act (eNC x)) fun j hj h n => by
    rw [← Module.End.mul_apply, ← word_cons]
    exact word_mem act N (by omega) _ n

lemma filt_word {m : ℕ} : ∀ {j : ℕ} (h : Fin j → NC R S), ∀ v ∈ filt act N m, word act h v ∈ filt act N (m + j) := by
  intro j
  induction j with
  | zero => intro h v hv; simpa [word_zero] using hv
  | succ j ih =>
    intro h v hv
    rw [word_succ, Module.End.mul_apply]
    exact filt_X act N (h 0) _ (ih (Fin.tail h) v hv)

lemma act_pc_mem {m : ℕ} {P : Mat R S} (hP : IsPC P) (v : V) (hv : v ∈ filt act N m) :
    act P v ∈ filt act N (m + 1) := by
  rw [Matrix.matrix_eq_sum_single P]
  simp only [map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  by_cases hab : sameBlock a b
  · simp [hP a b hab]
  · have : Matrix.single a b (P a b) = P a b • eNC (⟨(a, b), hab⟩ : NC R S) := by
      simp [eNC, Eab, Matrix.smul_single]
    rw [this, map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (filt_X act N _ v hv)

lemma filt_KC (hlie : IsLieAct act) (hN : KStable act N) {Z : Mat R S} (hZ : IsKC Z) {m : ℕ} :
    ∀ v ∈ filt act N m, act Z v ∈ filt act N m := by
  have key : ∀ (j : ℕ) (h : Fin j → NC R S) (n : N), act Z (word act h n) ∈ filt act N j := by
    intro j
    induction j with
    | zero =>
      intro h n
      have := word_mem act N le_rfl h ⟨act Z n, hN Z hZ n n.2⟩
      rwa [word_zero, Module.End.one_apply] at this ⊢
    | succ j ih =>
      intro h n
      rw [word_succ, Module.End.mul_apply]
      have hw : word act (Fin.tail h) n ∈ filt act N j := word_mem act N le_rfl _ n
      have e : act Z (act (eNC (h 0)) (word act (Fin.tail h) n)) =
          act (eNC (h 0)) (act Z (word act (Fin.tail h) n)) +
            act (Z * eNC (h 0) - eNC (h 0) * Z) (word act (Fin.tail h) n) := by
        rw [hlie, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]; abel
      rw [e]
      exact add_mem (filt_X act N _ _ (ih _ n)) (act_pc_mem act N (isPC_comm_KC hZ (isPC_eNC _)) _ hw)
  intro v hv
  exact filt_map act N (act Z) (fun j hj h n => filt_mono act N hj (key j h n)) v hv

lemma comm_word (hlie : IsLieAct act) (hN : KStable act N) (x : NC R S) {m : ℕ} :
    ∀ {j : ℕ} (h : Fin j → NC R S), ∀ v ∈ filt act N m,
      act (eNC x) (word act h v) - word act h (act (eNC x) v) ∈ filt act N (m + j) := by
  intro j
  induction j with
  | zero => intro h v hv; simp [word_zero]
  | succ j ih =>
    intro h v hv
    rw [word_succ, Module.End.mul_apply, Module.End.mul_apply]
    have e : act (eNC x) (act (eNC (h 0)) (word act (Fin.tail h) v)) -
        act (eNC (h 0)) (word act (Fin.tail h) (act (eNC x) v)) =
        act (eNC x * eNC (h 0) - eNC (h 0) * eNC x) (word act (Fin.tail h) v) +
          act (eNC (h 0)) (act (eNC x) (word act (Fin.tail h) v) - word act (Fin.tail h) (act (eNC x) v)) := by
      rw [hlie, map_sub, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]; abel
    rw [e]
    refine add_mem ?_ (filt_X act N _ _ (ih (Fin.tail h) v hv))
    exact filt_mono act N (by omega)
      (filt_KC act N hlie hN (isKC_comm_PC (isPC_eNC x) (isPC_eNC _)) _ (filt_word act N _ v hv))

lemma sum_cons {k : ℕ} {β : Type} [AddCommMonoid β] (f : (Fin (k + 1) → NC R S) → β) :
    ∑ g, f g = ∑ x, ∑ g' : Fin k → NC R S, f (Fin.cons x g') := by
  rw [← Fintype.sum_prod_type' (fun x (g' : Fin k → NC R S) => f (Fin.cons x g'))]
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => NC R S) _ _ (fun p => rfl)).symm

lemma phiN_succ (k : ℕ) (Ψ : (Fin (k + 1) → NC R S) → N) :
    phiN act N (k + 1) Ψ = ∑ x, act (eNC x) (phiN act N k (fun g' => Ψ (Fin.cons x g'))) := by
  rw [phiN_apply, sum_cons]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [phiN_apply, map_sum]
  refine Finset.sum_congr rfl fun g' _ => ?_
  rw [word_cons, Module.End.mul_apply]

lemma position_zero (hlie : IsLieAct act) (hN : KStable act N) (k : ℕ) (Ψ : (Fin (k + 1) → NC R S) → N)
    (hΨ : ∀ g, phiN act N 1 (section1 Ψ 0 g) = 0) : phiN act N (k + 1) Ψ ∈ filt act N k := by
  have hsum : ∀ g' : Fin k → NC R S, ∑ x, act (eNC x) (Ψ (Fin.cons x g') : V) = 0 := by
    intro g'
    rcases isEmpty_or_nonempty (NC R S) with hE | ⟨⟨x0⟩⟩
    · simp [Finset.univ_eq_empty]
    · have e2 : phiN act N 1 (section1 Ψ 0 (Fin.cons x0 g')) = ∑ x, act (eNC x) (Ψ (Fin.cons x g') : V) := by
        rw [phiN_apply]
        refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (NC R S)) _ _ fun h => ?_
        simp [section1, word, Fin.update_cons_zero]
      rw [← e2, hΨ]
  rw [phiN_apply, sum_cons]
  have e3 : ∀ x (g' : Fin k → NC R S), word act (Fin.cons x g' : Fin (k + 1) → NC R S) (Ψ (Fin.cons x g') : V) =
      word act g' (act (eNC x) (Ψ (Fin.cons x g'))) +
        (act (eNC x) (word act g' (Ψ (Fin.cons x g'))) - word act g' (act (eNC x) (Ψ (Fin.cons x g')))) := by
    intro x g'; rw [word_cons, Module.End.mul_apply]; abel
  simp_rw [e3, Finset.sum_add_distrib]
  have hmain : ∑ x, ∑ g' : Fin k → NC R S, word act g' (act (eNC x) (Ψ (Fin.cons x g') : V)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun g' _ => ?_
    rw [← map_sum, hsum g', map_zero]
  rw [hmain, zero_add]
  refine Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun g' _ => ?_
  simpa using comm_word act N hlie hN x g' _ (mem_filt_zero act N (Ψ (Fin.cons x g')))

theorem position_rel : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N → ∀ (k : ℕ) (i : Fin (k + 1))
    (Ψ : (Fin (k + 1) → NC R S) → N), (∀ g, phiN M.act N 1 (section1 Ψ i g) = 0) →
    phiN M.act N (k + 1) Ψ ∈ filt M.act N k := by
  intro R S M N hN k
  induction k with
  | zero =>
    intro i Ψ hΨ
    obtain rfl : i = 0 := Fin.ext (by omega)
    exact position_zero M.act N M.lie hN 0 Ψ hΨ
  | succ k ih =>
    intro i Ψ hΨ
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · exact position_zero M.act N M.lie hN _ Ψ hΨ
    · rw [phiN_succ]
      refine Submodule.sum_mem _ fun y _ => filt_X M.act N y _ (ih i' _ fun g' => ?_)
      have : section1 (fun g' => Ψ (Fin.cons y g')) i' g' = section1 Ψ i'.succ (Fin.cons y g') := by
        funext h; simp only [section1, Fin.cons_update]
      rw [this]; exact hΨ _

end GlobalTheory.PositionRel

end
