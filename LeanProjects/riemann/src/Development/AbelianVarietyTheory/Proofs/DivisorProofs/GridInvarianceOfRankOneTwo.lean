import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPowOfCommutatorEqSmul

open GlobalTheory.LeviCut

noncomputable section

namespace GlobalTheory.LeviCut.GridProof

variable {W : Type} [AddCommGroup W] [Module ℚ W]

def Keeps (P : W → Prop) (f : Module.End ℚ W) : Prop := ∀ x, P x → P (f x)

lemma keeps_one (P : W → Prop) : Keeps P 1 := fun x hx => by simpa using hx

lemma keeps_mul {P : W → Prop} {f g : Module.End ℚ W} (hf : Keeps P f) (hg : Keeps P g) : Keeps P (f * g) :=
  fun x hx => by rw [Module.End.mul_apply]; exact hf _ (hg _ hx)

lemma keeps_prod {P : W → Prop} (l : List (Module.End ℚ W)) (h : ∀ f ∈ l, Keeps P f) : Keeps P l.prod := by
  induction l with
  | nil => simpa using keeps_one P
  | cons f l ih =>
    rw [List.prod_cons]
    exact keeps_mul (h f (by simp)) (ih fun g hg => h g (by simp [hg]))

lemma commute_proj' {A : Type} [Ring A] [Algebra ℚ A] {f X Y : A} (h : ∀ k : ℕ, Commute f (Y ^ k * X ^ k))
    (K j : ℕ) : Commute f (proj K j X Y) := by
  unfold proj
  exact Commute.sum_right _ _ _ fun k _ => (h k).smul_right _

lemma commute_proj {A : Type} [Ring A] [Algebra ℚ A] {f X Y : A} (hX : Commute f X) (hY : Commute f Y) (K j : ℕ) :
    Commute f (proj K j X Y) :=
  commute_proj' (fun k => (hY.pow_right k).mul_right (hX.pow_right k)) K j

lemma commute_proj_proj {A : Type} [Ring A] [Algebra ℚ A] {X Y X' Y' : A} (h1 : Commute X X') (h2 : Commute X Y')
    (h3 : Commute Y X') (h4 : Commute Y Y') (K j K' j' : ℕ) : Commute (proj K j X Y) (proj K' j' X' Y') :=
  (commute_proj (commute_proj h1 h2 K' j').symm (commute_proj h3 h4 K' j').symm K j).symm

lemma proj_neg {A : Type} [Ring A] [Algebra ℚ A] (K j : ℕ) (X Y : A) : proj K j (-X) (-Y) = proj K j X Y := by
  unfold proj
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_pow, h.neg_pow]
  · rw [h.neg_pow, h.neg_pow, neg_mul_neg]

lemma comm_pow_of {A : Type} [Ring A] [Algebra ℚ A] {H X : A} {s : ℚ} (h : H * X - X * H = s • X) (k : ℕ) :
    H * X ^ k - X ^ k * H = ((k : ℚ) * s) • X ^ k := by
  first
  | exact @_root_.GlobalTheory.CommutatorPowerFormula.commutator_pow_of_commutator_eq_smul
  | exact _root_.GlobalTheory.CommutatorPowerFormula.commutator_pow_of_commutator_eq_smul
  | (apply _root_.GlobalTheory.CommutatorPowerFormula.commutator_pow_of_commutator_eq_smul <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommutatorPowerFormula.commutator_pow_of_commutator_eq_smul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommutatorPowerFormula.commutator_pow_of_commutator_eq_smul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommutatorPowerFormula.commutator_pow_of_commutator_eq_smul ..)

lemma commute_pair_pow {A : Type} [Ring A] [Algebra ℚ A] {H X Y : A} {s : ℚ} (hX : H * X - X * H = s • X)
    (hY : H * Y - Y * H = (-s) • Y) (k : ℕ) : Commute H (Y ^ k * X ^ k) := by
  have h1 := comm_pow_of hX k
  have h2 := comm_pow_of hY k
  have e : H * (Y ^ k * X ^ k) = (H * Y ^ k - Y ^ k * H) * X ^ k + Y ^ k * (H * X ^ k - X ^ k * H)
      + Y ^ k * X ^ k * H := by noncomm_ring
  show H * (Y ^ k * X ^ k) = Y ^ k * X ^ k * H
  rw [e, h1, h2, smul_mul_assoc, mul_smul_comm, ← add_smul]
  have : ((k : ℚ) * -s + (k : ℚ) * s) = 0 := by ring
  rw [this, zero_smul, zero_add]

variable {N : ℕ} {D : ℕ → ℕ → Module.End ℚ W}

lemma comm_off (hD : GlRel N D) {a b c d : ℕ} (ha : a < N) (hb : b < N) (hc : c < N) (hd : d < N)
    (hbc : b ≠ c) (hda : d ≠ a) : Commute (D a b) (D c d) := by
  have := hD a b c d ha hb hc hd
  rw [if_neg hbc, if_neg hda, sub_zero] at this
  exact sub_eq_zero.mp this

lemma diag_comm (hD : GlRel N D) {c i j : ℕ} (hc : c < N) (hi : i < N) (hj : j < N) :
    D c c * D i j - D i j * D c c = ((if c = i then 1 else 0) - (if c = j then 1 else 0) : ℚ) • D i j := by
  rw [hD c c i j hc hc hi hj]
  by_cases h1 : c = i <;> by_cases h2 : j = c
  · subst h1; subst h2; simp
  · subst h1; simp [h2, Ne.symm h2]
  · subst h2; simp [h1]
  · simp [h1, h2, Ne.symm h2]

lemma commute_diag_rootP (hD : GlRel N D) (K : ℕ) {c i j : ℕ} (hc : c < N) (hi : i < N) (hj : j < N) :
    Commute (D c c) (rootP D K i j) := by
  unfold rootP
  refine commute_proj' (fun k => commute_pair_pow (diag_comm hD hc hi hj) ?_ k) _ _
  rw [diag_comm hD hc hj hi, neg_sub]

def PZ (N : ℕ) (D : ℕ → ℕ → Module.End ℚ W) (k : ℕ) (x : W) : Prop :=
  (∀ c < N, D c c x = 0) ∧ D k (k + 1) x = 0

lemma zero_of_comm {f X : Module.End ℚ W} (h : Commute X f) {x : W} (hx : X x = 0) : X (f x) = 0 := by
  rw [← Module.End.mul_apply, h.eq, Module.End.mul_apply, hx, map_zero]

lemma keeps_of_comm {k : ℕ} {f : Module.End ℚ W} (hc : ∀ c < N, Commute (D c c) f)
    (hk : Commute (D k (k + 1)) f) : Keeps (PZ N D k) f := by
  rintro x ⟨h0, h1⟩
  exact ⟨fun c hc' => zero_of_comm (hc c hc') (h0 c hc'), zero_of_comm hk h1⟩

lemma keeps_rootP_far (hD : GlRel N D) (K : ℕ) {k i j : ℕ} (hk : k + 1 < N) (hi : i < N) (hj : j < N)
    (hik : i ≠ k) (hik' : i ≠ k + 1) (hjk : j ≠ k) (hjk' : j ≠ k + 1) : Keeps (PZ N D k) (rootP D K i j) := by
  refine keeps_of_comm (fun c hc => commute_diag_rootP hD K hc hi hj) ?_
  unfold rootP
  exact commute_proj (comm_off hD (by omega) hk hi hj (Ne.symm hik') hjk)
    (comm_off hD (by omega) hk hj hi (Ne.symm hjk') hik) _ _

lemma keeps_pair_row (hD : GlRel N D) {K : ℕ} (hB : Bdd N (2 * K) D) (h2 : RankTwo) {k i : ℕ} (hk : k + 1 < N)
    (hi : i < k) : Keeps (PZ N D k) (rootP D K i k * rootP D K i (k + 1)) := by
  rintro x ⟨h0, h1⟩
  refine ⟨fun c hc => ?_, ?_⟩
  · rw [Module.End.mul_apply]
    exact zero_of_comm (commute_diag_rootP hD K hc (by omega) (by omega))
      (zero_of_comm (commute_diag_rootP hD K hc (by omega) hk) (h0 c hc))
  · have := h2 W N K D hD hB i k (k + 1) (by omega) (by omega) hk (by omega) (by omega) (by omega) (k - i - 1) x
      (h0 i (by omega)) (h0 k (by omega)) (h0 (k + 1) hk) h1
    have e : k + 1 - i - 1 = k - i - 1 + 1 := by omega
    simpa only [Module.End.mul_apply, rootP, e] using this

lemma glRel_twist (hD : GlRel N D) : GlRel N (fun c d => -D d c) := by
  intro a b c d ha hb hc hd
  have h := hD d c b a hd hc hb ha
  have e : -D b a * -D d c - -D d c * -D b a = -(D d c * D b a - D b a * D d c) := by noncomm_ring
  simp only
  rw [e, h]
  by_cases h1 : b = c <;> by_cases h3 : d = a
  · subst h1; subst h3; simp; abel
  · subst h1; simp [h3, Ne.symm h3]
  · subst h3; simp [h1, Ne.symm h1]
  · simp [h1, h3, Ne.symm h1, Ne.symm h3]

lemma bdd_twist {K : ℕ} (hB : Bdd N K D) : Bdd N K (fun c d => -D d c) := by
  intro a ha b hb n x hx hn
  refine hB b hb a ha n x ?_ hn
  rw [← hx]
  simp only [LinearMap.neg_apply]
  abel

lemma keeps_pair_twist (hD : GlRel N D) {K : ℕ} (hB : Bdd N (2 * K) D) (h2 : RankTwo) {k j : ℕ}
    (hkj : k + 1 < j) (hj : j < N) : Keeps (PZ N D k) (rootP D K (k + 1) j * rootP D K k j) := by
  rintro x ⟨h0, h1⟩
  refine ⟨fun c hc => ?_, ?_⟩
  · rw [Module.End.mul_apply]
    exact zero_of_comm (commute_diag_rootP hD K hc (by omega) hj)
      (zero_of_comm (commute_diag_rootP hD K hc (by omega) hj) (h0 c hc))
  · have := h2 W N K (fun c d => -D d c) (glRel_twist hD) (bdd_twist hB) j (k + 1) k hj (by omega) (by omega)
      (by omega) (by omega) (by omega) (j - (k + 1) - 1) x
      (by simp [h0 j hj]) (by simp [h0 (k + 1) (by omega)]) (by simp [h0 k (by omega)]) (by simp [h1])
    have e : j - k - 1 = j - (k + 1) - 1 + 1 := by omega
    simp only [proj_neg, LinearMap.neg_apply, neg_eq_zero] at this
    simpa only [Module.End.mul_apply, rootP, e] using this

lemma keeps_range' {P : W → Prop} (h : ℕ → Module.End ℚ W) (s n : ℕ)
    (hm : ∀ m, s ≤ m → m < s + n → Keeps P (h m)) : Keeps P ((List.range' s n).map h).prod := by
  refine keeps_prod _ fun f hf => ?_
  obtain ⟨m, hm', rfl⟩ := List.mem_map.mp hf
  rw [List.mem_range'_1] at hm'
  exact hm m hm'.1 hm'.2

lemma keeps_range'_pair {P : W → Prop} (h : ℕ → Module.End ℚ W) (k : ℕ) (hpair : Keeps P (h k * h (k + 1))) :
    ∀ n s, s ≤ k → k + 1 < s + n → (∀ m, s ≤ m → m < s + n → m ≠ k → m ≠ k + 1 → Keeps P (h m)) →
      Keeps P ((List.range' s n).map h).prod := by
  intro n
  induction n with
  | zero => intro s hs hn; omega
  | succ n ih =>
    intro s hs hn hm
    rw [List.range'_succ, List.map_cons, List.prod_cons]
    by_cases hsk : s = k
    · subst hsk
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [List.range'_succ, List.map_cons, List.prod_cons, ← mul_assoc]
      exact keeps_mul hpair (keeps_range' h _ _ fun m h1 h2 => hm m (by omega) (by omega) (by omega) (by omega))
    · exact keeps_mul (hm s le_rfl (by omega) hsk (by omega))
        (ih (s + 1) (by omega) (by omega) fun m h1 h2 h3 h4 => hm m (by omega) (by omega) h3 h4)

lemma grid_succ (g : ℕ → Module.End ℚ W) (n : ℕ) :
    ((List.range (n + 1)).reverse.map g).prod = g n * ((List.range n).reverse.map g).prod := by
  rw [List.range_succ, List.reverse_append]
  simp

lemma keeps_grid {P : W → Prop} (g : ℕ → Module.End ℚ W) (n : ℕ) (hm : ∀ m < n, Keeps P (g m)) :
    Keeps P ((List.range n).reverse.map g).prod := by
  refine keeps_prod _ fun f hf => ?_
  obtain ⟨m, hm', rfl⟩ := List.mem_map.mp hf
  rw [List.mem_reverse, List.mem_range] at hm'
  exact hm m hm'

lemma keeps_grid_pair {P : W → Prop} (g : ℕ → Module.End ℚ W) (k : ℕ) (hpair : Keeps P (g (k + 1) * g k)) :
    ∀ n, k + 2 ≤ n → (∀ m < n, m ≠ k → m ≠ k + 1 → Keeps P (g m)) →
      Keeps P ((List.range n).reverse.map g).prod := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hn hm
    rw [grid_succ]
    by_cases hnk : n = k + 1
    · subst hnk
      rw [grid_succ, ← mul_assoc]
      exact keeps_mul hpair (keeps_grid g k fun m hm' => hm m (by omega) (by omega) (by omega))
    · exact keeps_mul (hm n (by omega) (by omega) hnk) (ih (by omega) fun m h1 h2 h3 => hm m (by omega) h2 h3)

lemma keeps_rows_pair {P : W → Prop} (A B : ℕ → Module.End ℚ W) :
    ∀ n s, (∀ j, s ≤ j → j < s + n → Keeps P (A j * B j)) →
      (∀ j j', s ≤ j → j < s + n → s ≤ j' → j' < s + n → j ≠ j' → Commute (A j') (B j)) →
      Keeps P (((List.range' s n).map A).prod * ((List.range' s n).map B).prod) := by
  intro n
  induction n with
  | zero => intro s _ _; simpa using keeps_one P
  | succ n ih =>
    intro s hp hc
    rw [List.range'_succ, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    have hcomm : Commute ((List.range' (s + 1) n).map A).prod (B s) := by
      refine Commute.list_prod_left _ _ fun f hf => ?_
      obtain ⟨m, hm', rfl⟩ := List.mem_map.mp hf
      rw [List.mem_range'_1] at hm'
      exact hc s m le_rfl (by omega) (by omega) (by omega) (by omega)
    have e : A s * ((List.range' (s + 1) n).map A).prod * (B s * ((List.range' (s + 1) n).map B).prod) =
        (A s * B s) * (((List.range' (s + 1) n).map A).prod * ((List.range' (s + 1) n).map B).prod) := by
      rw [mul_assoc, ← mul_assoc ((List.range' (s + 1) n).map A).prod, hcomm.eq]
      simp only [mul_assoc]
    rw [e]
    exact keeps_mul (hp s le_rfl (by omega))
      (ih (s + 1) (fun j h1 h2 => hp j (by omega) (by omega))
        fun j j' h1 h2 h3 h4 h5 => hc j j' (by omega) (by omega) (by omega) (by omega) h5)

lemma fill (hD : GlRel N D) (x : W) (hZ : ∀ c < N, D c c x = 0) (hup : ∀ k, k + 1 < N → D k (k + 1) x = 0)
    (hdown : ∀ k, k + 1 < N → D (k + 1) k x = 0) : ∀ c < N, ∀ d < N, D c d x = 0 := by
  have key : ∀ n c, c + n + 1 < N → D c (c + n + 1) x = 0 ∧ D (c + n + 1) c x = 0 := by
    intro n
    induction n with
    | zero => intro c hc; exact ⟨hup c hc, hdown c hc⟩
    | succ n ih =>
      intro c hc
      obtain ⟨ih1, ih2⟩ := ih c (by omega)
      have e : c + (n + 1) + 1 = c + n + 1 + 1 := by omega
      rw [e] at hc ⊢
      have e1 := hD c (c + n + 1) (c + n + 1) (c + n + 1 + 1) (by omega) (by omega) (by omega) hc
      rw [if_pos rfl, if_neg (by omega), sub_zero] at e1
      have e2 := hD (c + n + 1 + 1) (c + n + 1) (c + n + 1) c hc (by omega) (by omega) (by omega)
      rw [if_pos rfl, if_neg (by omega), sub_zero] at e2
      constructor
      · rw [← e1, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hup _ hc, ih1, map_zero,
          map_zero, sub_zero]
      · rw [← e2, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hdown _ hc, ih2, map_zero,
          map_zero, sub_zero]
  intro c hc d hd
  rcases lt_trichotomy c d with h | rfl | h
  · obtain ⟨n, rfl⟩ : ∃ n, d = c + n + 1 := ⟨d - c - 1, by omega⟩
    exact (key n c hd).1
  · exact hZ c hc
  · obtain ⟨n, rfl⟩ : ∃ n, c = d + n + 1 := ⟨c - d - 1, by omega⟩
    exact (key n d hc).2

end GlobalTheory.LeviCut.GridProof

open GlobalTheory.LeviCut.GridProof in

theorem GlobalTheory.LeviCut.gridInv_of_rankOne_rankTwo (h1 : RankOne) (h2 : RankTwo) : GridInv := by
  intro W _ _ a b K D hD hB T hT
  have hcommG : ∀ c < a + b, Commute (D c c) (gridP D K a b a) := by
    intro c hc
    refine Commute.list_prod_right _ _ fun f hf => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    rw [List.mem_reverse, List.mem_range] at hi
    refine Commute.list_prod_right _ _ fun f hf => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
    rw [List.mem_range'_1] at hj
    exact commute_diag_rootP hD K hc (by omega) (by omega)
  have hZ : ∀ c < a + b, D c c (gridP D K a b a T) = 0 :=
    fun c hc => zero_of_comm (hcommG c hc) (hT c hc c hc Iff.rfl)
  have hup : ∀ k, k + 1 < a + b → D k (k + 1) (gridP D K a b a T) = 0 := by
    intro k hk
    rcases lt_trichotomy (k + 1) a with hka | hka | hka
    ·
      have hT0 : PZ (a + b) D k T := ⟨fun c hc => hT c hc c hc Iff.rfl, hT k (by omega) (k + 1) hk (by omega)⟩
      refine (keeps_grid_pair (P := PZ (a + b) D k) (fun i => rowP D K i a b) k ?_ a (by omega) ?_ T hT0).2
      · exact keeps_rows_pair (rootP D K (k + 1)) (rootP D K k) b a
          (fun j hj1 hj2 => keeps_pair_twist hD hB h2 (by omega) (by omega))
          fun j j' h1 h2 h3 h4 h5 => commute_proj_proj
            (comm_off hD (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
            (comm_off hD (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
            (comm_off hD (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
            (comm_off hD (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) _ _ _ _
      · intro m hm hmk hmk'
        exact keeps_range' _ _ _ fun j h1 h2 =>
          keeps_rootP_far hD K hk (by omega) (by omega) hmk hmk' (by omega) (by omega)
    ·
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      subst hka
      have e : gridP D K (k + 1) (b' + 1) (k + 1) =
          rootP D K k (k + 1) * (rowP D K k (k + 1 + 1) b' * gridP D K (k + 1) (b' + 1) k) := by
        unfold gridP
        rw [grid_succ]
        unfold rowP
        rw [List.range'_succ, List.map_cons, List.prod_cons, mul_assoc]
      have hcommR : ∀ c < k + 1 + (b' + 1), Commute (D c c) (rowP D K k (k + 1 + 1) b') := by
        intro c hc
        refine Commute.list_prod_right _ _ fun f hf => ?_
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
        rw [List.mem_range'_1] at hj
        exact commute_diag_rootP hD K hc (by omega) (by omega)
      have hcommG' : ∀ c < k + 1 + (b' + 1), Commute (D c c) (gridP D K (k + 1) (b' + 1) k) := by
        intro c hc
        refine Commute.list_prod_right _ _ fun f hf => ?_
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
        rw [List.mem_reverse, List.mem_range] at hi
        refine Commute.list_prod_right _ _ fun f hf => ?_
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
        rw [List.mem_range'_1] at hj
        exact commute_diag_rootP hD K hc (by omega) (by omega)
      have hU : ∀ c < k + 1 + (b' + 1),
          D c c ((rowP D K k (k + 1 + 1) b' * gridP D K (k + 1) (b' + 1) k) T) = 0 := by
        intro c hc
        rw [Module.End.mul_apply]
        exact zero_of_comm (hcommR c hc) (zero_of_comm (hcommG' c hc) (hT c hc c hc Iff.rfl))
      have := (h1 W (k + 1 + (b' + 1)) K D hD hB k (k + 1) (by omega) hk (by omega) _
        (hU k (by omega)) (hU (k + 1) hk)).1
      have e0 : k + 1 - k - 1 = 0 := by omega
      rw [e, Module.End.mul_apply]
      simpa only [rootP, e0] using this
    ·
      have hT0 : PZ (a + b) D k T := ⟨fun c hc => hT c hc c hc Iff.rfl, hT k (by omega) (k + 1) hk (by omega)⟩
      refine (keeps_grid (P := PZ (a + b) D k) (fun i => rowP D K i a b) a (fun i hi => ?_) T hT0).2
      exact keeps_range'_pair _ k (keeps_pair_row hD hB h2 hk (by omega)) b a (by omega) (by omega)
        fun m hm1 hm2 h3 h4 => keeps_rootP_far hD K hk (by omega) (by omega) (by omega) (by omega) h3 h4
  have hdown : ∀ k, k + 1 < a + b → D (k + 1) k (gridP D K a b a T) = 0 := fun k hk =>
    (h1 W (a + b) K D hD hB k (k + 1) (by omega) hk (by omega) _ (hZ k (by omega)) (hZ (k + 1) hk)).2 (hup k hk)
  exact fill hD _ hZ hup hdown
