import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace HeightVanishing

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def ht (w : List (Fin n × Fin n)) : ℤ := (w.map fun x => ((x.2 : ℕ) : ℤ) - ((x.1 : ℕ) : ℤ)).sum

def word (E : Fin n → Fin n → Module.End ℂ M) (w : List (Fin n × Fin n)) : Module.End ℂ M :=
  (w.map fun x => E x.1 x.2).prod

def W (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (h : ℤ) : Submodule ℂ (Module.End ℂ M) :=
  Submodule.span ℂ {A | ∃ w, w.length ≤ k ∧ ht w = h ∧ word E w = A}

variable (E : Fin n → Fin n → Module.End ℂ M)

theorem ht_cons (x : Fin n × Fin n) (w : List (Fin n × Fin n)) :
    ht (x :: w) = (((x.2 : ℕ) : ℤ) - ((x.1 : ℕ) : ℤ)) + ht w := by
  simp [ht]

theorem word_cons (x : Fin n × Fin n) (w : List (Fin n × Fin n)) : word E (x :: w) = E x.1 x.2 * word E w := by
  simp [word]

theorem word_mem {k : ℕ} {h : ℤ} (w : List (Fin n × Fin n)) (hk : w.length ≤ k) (hh : ht w = h) :
    word E w ∈ W E k h := Submodule.subset_span ⟨w, hk, hh, rfl⟩

theorem W_of {k k' : ℕ} {h h' : ℤ} {A : Module.End ℂ M} (hk : k ≤ k') (hh : h = h') (hA : A ∈ W E k h) :
    A ∈ W E k' h' := hh ▸ Submodule.span_mono (fun _ hx => by obtain ⟨w, h1, h2, h3⟩ := hx; exact ⟨w, h1.trans hk, h2, h3⟩) hA

theorem W_ind {k : ℕ} {h : ℤ} {p : Module.End ℂ M → Prop} (h0 : p 0) (hadd : ∀ x y, p x → p y → p (x + y))
    (hsm : ∀ (c : ℂ) x, p x → p (c • x)) (hw : ∀ w : List (Fin n × Fin n), w.length ≤ k → ht w = h → p (word E w))
    {A : Module.End ℂ M} (hA : A ∈ W E k h) : p A := by
  induction hA using Submodule.span_induction with
  | mem x hx => obtain ⟨w, h1, h2, rfl⟩ := hx; exact hw w h1 h2
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul c x _ hx => exact hsm c x hx

theorem one_mem (k : ℕ) : (1 : Module.End ℂ M) ∈ W E k 0 :=
  word_mem E [] (Nat.zero_le _) (by simp [ht])

theorem letter_mem (a b : Fin n) : E a b ∈ W E 1 (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) := by
  have := word_mem E [(a, b)] le_rfl rfl
  simpa [word, ht] using this

theorem mul_mem {k k' : ℕ} {h h' : ℤ} {A B : Module.End ℂ M} (hA : A ∈ W E k h) (hB : B ∈ W E k' h') :
    A * B ∈ W E (k + k') (h + h') := by
  have key : ∀ w w' : List (Fin n × Fin n), w.length ≤ k → ht w = h → w'.length ≤ k' → ht w' = h' →
      word E w * word E w' ∈ W E (k + k') (h + h') := by
    intro w w' h1 h2 h3 h4
    have e : word E w * word E w' = word E (w ++ w') := by simp [word, List.prod_append]
    rw [e]
    refine word_mem E _ (by simp only [List.length_append]; omega) ?_
    rw [← h2, ← h4]; simp [ht, List.sum_append]
  refine W_ind E (p := fun A => A * B ∈ W E (k + k') (h + h')) (by simp)
    (fun x y hx hy => by rw [add_mul]; exact add_mem hx hy)
    (fun c x hx => by rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx) ?_ hA
  intro w h1 h2
  refine W_ind E (p := fun B => word E w * B ∈ W E (k + k') (h + h')) (by simp)
    (fun x y hx hy => by rw [mul_add]; exact add_mem hx hy)
    (fun c x hx => by rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx) ?_ hB
  intro w' h3 h4
  exact key w w' h1 h2 h3 h4

theorem comm_mem (hE : GlRel E) (a b : Fin n) {k : ℕ} {h : ℤ} {A : Module.End ℂ M} (hA : A ∈ W E k h) :
    E a b * A - A * E a b ∈ W E k (h + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))) := by
  have gl : ∀ c e : Fin n, E a b * E c e - E c e * E a b ∈
      W E 1 ((((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)) + (((e : ℕ) : ℤ) - ((c : ℕ) : ℤ))) := by
    intro c e
    rw [hE a b c e]
    refine sub_mem ?_ ?_
    · split_ifs with h1
      · subst h1; exact W_of E le_rfl (by ring) (letter_mem E a e)
      · exact zero_mem _
    · split_ifs with h1
      · subst h1; exact W_of E le_rfl (by ring) (letter_mem E c b)
      · exact zero_mem _
  have hw : ∀ w : List (Fin n × Fin n),
      E a b * word E w - word E w * E a b ∈ W E w.length (ht w + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))) := by
    intro w
    induction w with
    | nil => simp [word]
    | cons y w ih =>
      rw [word_cons]
      have e1 : E a b * (E y.1 y.2 * word E w) - E y.1 y.2 * word E w * E a b =
          (E a b * E y.1 y.2 - E y.1 y.2 * E a b) * word E w +
            E y.1 y.2 * (E a b * word E w - word E w * E a b) := by noncomm_ring
      rw [e1]
      refine add_mem ?_ ?_
      · exact W_of E (by simp only [List.length_cons]; omega) (by rw [ht_cons]; ring)
          (mul_mem E (gl y.1 y.2) (word_mem E w le_rfl rfl))
      · exact W_of E (by simp only [List.length_cons]; omega) (by rw [ht_cons]; ring)
          (mul_mem E (letter_mem E y.1 y.2) ih)
  refine W_ind E (p := fun A => E a b * A - A * E a b ∈ W E k (h + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ)))) (by simp) ?_ ?_ ?_ hA
  · intro x y hx hy
    have e : E a b * (x + y) - (x + y) * E a b = (E a b * x - x * E a b) + (E a b * y - y * E a b) := by
      noncomm_ring
    rw [e]; exact add_mem hx hy
  · intro c x hx
    have e : E a b * (c • x) - (c • x) * E a b = c • (E a b * x - x * E a b) := by
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    rw [e]; exact Submodule.smul_mem _ c hx
  · intro w h1 h2
    exact W_of E h1 (by rw [h2]) (hw w)

section wh
variable {ℓ : M →ₗ[ℂ] ℂ} {ψ : Fin n → Fin n → ℂ} (hE : GlRel E)
  (hψ2 : ∀ a b : Fin n, (a : ℕ) + 1 < b → ψ a b = 0) (hψ : ∀ a b : Fin n, a < b → ℓ ∘ₗ E a b = ψ a b • ℓ)
include hE hψ2 hψ

theorem letter_zero {k : ℕ} (hQ : ∀ (h : ℤ) (A : Module.End ℂ M), A ∈ W E k h → (k : ℤ) < h → ℓ ∘ₗ A = 0)
    (a b : Fin n) (hab : ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) ≤ 0) {h : ℤ} {A : Module.End ℂ M} (hA : A ∈ W E k h)
    (hk : (k : ℤ) < h + (((b : ℕ) : ℤ) - ((a : ℕ) : ℤ))) : ℓ ∘ₗ (E a b * A) = 0 := by
  have e : E a b * A = A * E a b + (E a b * A - A * E a b) := by abel
  rw [e, LinearMap.comp_add]
  have h1 : ℓ ∘ₗ (A * E a b) = 0 := by
    rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hQ h A hA (by linarith), LinearMap.zero_comp]
  rw [h1, hQ _ _ (comm_mem E hE a b hA) hk, add_zero]

theorem vanish (k : ℕ) : ∀ (h : ℤ) (A : Module.End ℂ M), A ∈ W E k h → (k : ℤ) < h → ℓ ∘ₗ A = 0 := by
  induction k with
  | zero =>
    intro h A hA hk
    refine W_ind E (p := fun A => ℓ ∘ₗ A = 0) (by simp)
      (fun x y hx hy => by rw [LinearMap.comp_add, hx, hy, add_zero])
      (fun c x hx => by rw [LinearMap.comp_smul, hx, smul_zero]) ?_ hA
    intro w h1 h2
    have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [ht] at h2; omega
  | succ k ih =>
    intro h A hA hk
    refine W_ind E (p := fun A => ℓ ∘ₗ A = 0) (by simp)
      (fun x y hx hy => by rw [LinearMap.comp_add, hx, hy, add_zero])
      (fun c x hx => by rw [LinearMap.comp_smul, hx, smul_zero]) ?_ hA
    intro w h1 h2
    cases w with
    | nil => simp [ht] at h2; omega
    | cons x w =>
      obtain ⟨a, b⟩ := x
      rw [ht_cons] at h2
      simp only [List.length_cons] at h1
      rw [word_cons]
      have hw : word E w ∈ W E k (ht w) := word_mem E w (by omega) rfl
      rcases lt_or_ge a b with hab | hab
      · have hab' := Fin.lt_def.1 hab
        rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hψ a b hab]
        rcases (show (a : ℕ) + 1 = b ∨ (a : ℕ) + 1 < b by omega) with h3 | h3
        · rw [LinearMap.smul_comp, ih _ _ hw (by push_cast at hk h2 ⊢; omega), smul_zero]
        · rw [hψ2 a b h3, zero_smul, LinearMap.zero_comp]
      · have hab' := Fin.le_def.1 hab
        exact letter_zero E hE hψ2 hψ ih a b (by push_cast; omega) hw (by push_cast at hk h2 ⊢; omega)

theorem scalar (d : ℕ) : ∀ A : Module.End ℂ M, A ∈ W E d d → ∃ c : ℂ, ℓ ∘ₗ A = c • ℓ := by
  induction d with
  | zero =>
    intro A hA
    refine W_ind E (p := fun A => ∃ c : ℂ, ℓ ∘ₗ A = c • ℓ) ⟨0, by simp⟩ ?_ ?_ ?_ hA
    · rintro x y ⟨c, hc⟩ ⟨c', hc'⟩; exact ⟨c + c', by rw [LinearMap.comp_add, hc, hc', add_smul]⟩
    · rintro c x ⟨c', hc'⟩; exact ⟨c * c', by rw [LinearMap.comp_smul, hc', smul_smul]⟩
    · intro w h1 h2
      have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      exact ⟨1, by simp only [word, List.map_nil, List.prod_nil, one_smul]; exact LinearMap.comp_id ℓ⟩
  | succ d ih =>
    intro A hA
    refine W_ind E (p := fun A => ∃ c : ℂ, ℓ ∘ₗ A = c • ℓ) ⟨0, by simp⟩ ?_ ?_ ?_ hA
    · rintro x y ⟨c, hc⟩ ⟨c', hc'⟩; exact ⟨c + c', by rw [LinearMap.comp_add, hc, hc', add_smul]⟩
    · rintro c x ⟨c', hc'⟩; exact ⟨c * c', by rw [LinearMap.comp_smul, hc', smul_smul]⟩
    · intro w h1 h2
      cases w with
      | nil => simp [ht] at h2; omega
      | cons x w =>
        obtain ⟨a, b⟩ := x
        rw [ht_cons] at h2
        simp only [List.length_cons] at h1
        rw [word_cons]
        rcases lt_or_ge a b with hab | hab
        · have hab' := Fin.lt_def.1 hab
          rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hψ a b hab]
          rcases (show (a : ℕ) + 1 = b ∨ (a : ℕ) + 1 < b by omega) with h3 | h3
          · obtain ⟨c, hc⟩ := ih _ (word_mem E w (by omega) (by push_cast at h2; omega))
            exact ⟨ψ a b * c, by rw [LinearMap.smul_comp, hc, smul_smul]⟩
          · exact ⟨0, by rw [hψ2 a b h3]; simp⟩
        · have hab' := Fin.le_def.1 hab
          exact ⟨0, by rw [letter_zero E hE hψ2 hψ (vanish E hE hψ2 hψ d) a b (by push_cast; omega)
            (word_mem E w (by omega) rfl) (by push_cast at h2 ⊢; omega), zero_smul]⟩

end wh

section eval
variable {P : Type} [Fintype P] [DecidableEq P]

theorem Om_single (p : P) (I : P → Fin n) (v : M) :
    Om E p (Pi.single I v : TV n M P) = ∑ c, Pi.single (Function.update I p c) (E (I p) c v) := by
  funext J
  rw [Om_apply, Finset.sum_apply]
  by_cases hJ : ∀ q, q ≠ p → J q = I q
  · rw [Finset.sum_eq_single_of_mem (I p) (Finset.mem_univ _) ?_,
      Finset.sum_eq_single_of_mem (J p) (Finset.mem_univ _) ?_]
    · have h1 : Function.update J p (I p) = I := by
        funext q; by_cases hq : q = p
        · subst hq; simp
        · rw [Function.update_of_ne hq]; exact hJ q hq
      have h2 : J = Function.update I p (J p) := by
        funext q; by_cases hq : q = p
        · subst hq; simp
        · rw [Function.update_of_ne hq]; exact hJ q hq
      rw [h1, Pi.single_eq_same, ← h2, Pi.single_eq_same]
    · intro c _ hc
      rw [Pi.single_eq_of_ne]
      intro h; apply hc; rw [h]; simp
    · intro a _ ha
      rw [Pi.single_eq_of_ne, map_zero]
      intro h; apply ha; rw [← h]; simp
  · push_neg at hJ
    obtain ⟨q, hq, hne⟩ := hJ
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro c _; rw [Pi.single_eq_of_ne]; intro h; apply hne; rw [h, Function.update_of_ne hq]
    · intro a _; rw [Pi.single_eq_of_ne, map_zero]; intro h; apply hne; rw [← h, Function.update_of_ne hq]

theorem pm_single (σ : Equiv.Perm P) (I : P → Fin n) (v : M) :
    pm σ (Pi.single I v : TV n M P) = Pi.single (I ∘ σ.symm) v := by
  funext J
  rw [pm_apply]
  simp only [Pi.single_apply, Equiv.eq_comp_symm]

def H (J I : P → Fin n) : ℤ := ∑ p, (((J p : ℕ) : ℤ) - ((I p : ℕ) : ℤ))

theorem eval {d : ℕ} {g : Module.End ℂ (TV n M P)} (hg : Deg E d g) (J : P → Fin n) :
    ∀ I : P → Fin n, ∃ A ∈ W E d (H J I), ∀ v, g (Pi.single I v) J = A v := by
  induction hg with
  | one d =>
    intro I
    by_cases h : J = I
    · subst h; exact ⟨1, W_of E le_rfl (by simp [H]) (one_mem E d), fun v => by simp⟩
    · exact ⟨0, zero_mem _, fun v => by simp [Pi.single_eq_of_ne h]⟩
  | add _ _ ih1 ih2 =>
    intro I
    obtain ⟨A, hA, hAv⟩ := ih1 I
    obtain ⟨B, hB, hBv⟩ := ih2 I
    exact ⟨A + B, add_mem hA hB, fun v => by simp [hAv, hBv]⟩
  | smul c _ ih =>
    intro I
    obtain ⟨A, hA, hAv⟩ := ih I
    exact ⟨c • A, Submodule.smul_mem _ c hA, fun v => by simp [hAv]⟩
  | om p _ ih =>
    intro I
    choose A hA hAv using fun c => ih (Function.update I p c)
    refine ⟨∑ c, A c * E (I p) c, Submodule.sum_mem _ fun c _ => ?_, fun v => ?_⟩
    · refine W_of E le_rfl ?_ (mul_mem E (hA c) (letter_mem E (I p) c))
      have : H J (Function.update I p c) - H J I = ((I p : ℕ) : ℤ) - ((c : ℕ) : ℤ) := by
        simp only [H, ← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_single p]
        · simp
        · intro q _ hq; simp [Function.update_of_ne hq]
        · simp
      linarith
    · rw [Module.End.mul_apply, Om_single, map_sum, Finset.sum_apply, LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun c _ => by rw [hAv]; rfl
  | perm σ _ ih =>
    intro I
    obtain ⟨A, hA, hAv⟩ := ih (I ∘ σ.symm)
    refine ⟨A, W_of E le_rfl ?_ hA, fun v => ?_⟩
    · simp only [H, Finset.sum_sub_distrib, Function.comp_apply]
      rw [Equiv.sum_comp σ.symm (fun p => ((I p : ℕ) : ℤ))]
    · rw [Module.End.mul_apply, pm_single, hAv]

theorem deg_succ {d : ℕ} {g : Module.End ℂ (TV n M P)} (hg : Deg E d g) : Deg E (d + 1) g := by
  induction hg with
  | one d => exact Deg.one _
  | add _ _ ih1 ih2 => exact Deg.add ih1 ih2
  | smul c _ ih => exact Deg.smul c ih
  | om p _ ih => exact Deg.om p ih
  | perm σ _ ih => exact Deg.perm σ ih

end eval

theorem prod_deg (L : List ℂ) :
    Deg E L.length (L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod ∧
      Commute (Om E (0 : Fin 1)) (L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod := by
  induction L with
  | nil => exact ⟨Deg.one 0, Commute.one_right _⟩
  | cons r L ih =>
    obtain ⟨h1, h2⟩ := ih
    have hc : Commute (Om E (0 : Fin 1)) (Om E 0 - algebraMap ℂ _ r) :=
      (Commute.refl _).sub_right (show Commute (algebraMap ℂ _ r) (Om E (0 : Fin 1)) from Algebra.commutes r _).symm
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    refine ⟨?_, hc.mul_right h2⟩
    rw [sub_mul, h2.eq, ← Algebra.smul_def, sub_eq_add_neg, ← neg_smul]
    exact Deg.add (Deg.om 0 h1) (Deg.smul (-r) (deg_succ E h1))

theorem prod_exact {ℓ : M →ₗ[ℂ] ℂ} {ψ : Fin n → Fin n → ℂ} (hE : GlRel E)
    (hψ1 : ∀ a b : Fin n, (a : ℕ) + 1 = b → ψ a b ≠ 0)
    (hψ2 : ∀ a b : Fin n, (a : ℕ) + 1 < b → ψ a b = 0) (hψ : ∀ a b : Fin n, a < b → ℓ ∘ₗ E a b = ψ a b • ℓ)
    (L : List ℂ) : ∀ j i : Fin n, (j : ℕ) + L.length = i → ∃ c : ℂ, c ≠ 0 ∧ ∀ v,
      ℓ ((L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod (Pi.single (fun _ => j) v) (fun _ => i)) =
        c * ℓ v := by
  have hl : ∀ (b c : Fin n) (X : M), b < c → ℓ (E b c X) = ψ b c * ℓ X := fun b c X hbc => by
    rw [← LinearMap.comp_apply, hψ b c hbc]; rfl
  have hu : ∀ b : Fin n, Function.update (fun _ : Fin 1 => b) 0 = fun c => (fun _ : Fin 1 => c) := by
    intro b; funext c x; rw [Subsingleton.elim x 0]; simp
  induction L with
  | nil =>
    intro j i hji
    have : j = i := Fin.ext (by simpa using hji)
    subst this
    exact ⟨1, one_ne_zero, fun v => by simp⟩
  | cons r L ih =>
    intro j i hji
    simp only [List.length_cons] at hji
    obtain ⟨hdeg, -⟩ := prod_deg E L
    set a : Fin n := ⟨(i : ℕ) - 1, by omega⟩ with ha
    obtain ⟨c, hc, hcv⟩ := ih j a (by simp only [a]; omega)
    refine ⟨ψ a i * c, mul_ne_zero (hψ1 a i (by simp only [a]; omega)) hc, fun v => ?_⟩
    simp only [List.map_cons, List.prod_cons]
    rw [Module.End.mul_apply, LinearMap.sub_apply, Pi.sub_apply, map_sub]
    obtain ⟨B, hB, hBv⟩ := eval E hdeg (fun _ => i) (fun _ => j)
    have h2 : ℓ (algebraMap ℂ (Module.End ℂ (TV n M (Fin 1))) r ((L.map fun r => Om E (0 : Fin 1) - algebraMap ℂ _ r).prod
        (Pi.single (fun _ => j) v)) (fun _ => i)) = 0 := by
      rw [Module.algebraMap_end_apply, Pi.smul_apply, hBv, map_smul, ← LinearMap.comp_apply,
        vanish E hE hψ2 hψ L.length _ B hB (by simp [H]; omega)]
      simp
    rw [h2, sub_zero, Om_apply, map_sum, hu]
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _) ?_]
    · rw [hl a i _ (Fin.lt_def.2 (by simp only [a]; omega)), hcv]; ring
    · intro a' _ ha'
      rcases lt_or_ge a' i with h3 | h3
      · have h3' := Fin.lt_def.1 h3
        have h4 : (a' : ℕ) + 1 < i := by
          rcases (show (a' : ℕ) + 1 < i ∨ (a' : ℕ) = (i : ℕ) - 1 by omega) with h | h
          · exact h
          · exact absurd (Fin.ext (by simp only [a]; omega)) ha'
        rw [hl a' i _ h3, hψ2 a' i h4, zero_mul]
      · have h3' := Fin.le_def.1 h3
        obtain ⟨B', hB', hB'v⟩ := eval E hdeg (fun _ => a') (fun _ => j)
        rw [hB'v, ← Module.End.mul_apply, ← LinearMap.comp_apply,
          letter_zero E hE hψ2 hψ (vanish E hE hψ2 hψ L.length) a' i (by push_cast; omega) hB'
            (by simp [H]; omega)]
        rfl

end HeightVanishing

open HeightVanishing in
theorem height_of : TensorGl → Height := by
  intro _ n M _ _ E hE ℓ hW top htop
  obtain ⟨ψ, hψ1, hψ2, hψ⟩ := hW
  have hcast : ∀ {P : Type} [Fintype P] (I : P → Fin n),
      ((∑ p, ((top : ℕ) - I p) : ℕ) : ℤ) = H (fun _ => top) I := by
    intro P _ I
    simp only [H]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_sub (by omega)]
  refine ⟨fun P _ _ d g hg I => ⟨fun hd v => ?_, fun hd => ?_⟩, fun hl L hL => ?_, fun m => ?_⟩
  · obtain ⟨A, hA, hAv⟩ := eval E hg (fun _ => top) I
    rw [hAv, ← LinearMap.comp_apply, vanish E hE hψ2 hψ d _ A hA (by rw [← hcast]; exact_mod_cast hd)]
    rfl
  · obtain ⟨A, hA, hAv⟩ := eval E hg (fun _ => top) I
    obtain ⟨c, hc⟩ := scalar E hE hψ2 hψ d A (W_of E le_rfl (by rw [← hcast, hd]) hA)
    exact ⟨c, fun v => by rw [hAv, ← LinearMap.comp_apply, hc]; rfl⟩
  · have h0 : 0 < n := by omega
    obtain ⟨c, hc, hcv⟩ := prod_exact E hE hψ1 hψ2 hψ L ⟨0, h0⟩ top (by simp [hL])
    obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
      by_contra h; push_neg at h; exact hl (LinearMap.ext h)
    intro h
    have := LinearMap.congr_fun h (Pi.single (fun _ => ⟨0, h0⟩) v)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.zero_apply] at this
    rw [hcv] at this
    exact mul_ne_zero hc hv this
  · refine ⟨ψ, hψ1, hψ2, fun a b hab => ?_⟩
    have hab' := Fin.lt_def.1 hab
    have hta : top ≠ a := by
      intro h; subst h; have := b.2; omega
    ext f
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smul_apply]
    rw [tE_apply]
    simp only [hta, if_false, Finset.sum_const_zero, add_zero]
    rw [← LinearMap.comp_apply, hψ a b hab]
    rfl

end PositivityTheory.Rg.Cz

end
