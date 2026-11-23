import Formalism.RealPlaceAnalysis.StatementU
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

section U1Pfil
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)

theorem mem_kSpan_self' : u ∈ kSpan ε E u := by
  unfold kSpan
  exact Submodule.mem_sInf.mpr fun S hS => hS.1

theorem compact_span_compact_stable : KStable ε E (kSpan ε E u) := by
  intro a b hab x hx
  unfold kSpan at hx ⊢
  rw [Submodule.mem_sInf] at hx ⊢
  intro S hS
  exact hS.2 a b hab x (hx S hS)

theorem mem_cyclic_self : u ∈ cyc E u := by
  unfold cyc
  exact Submodule.mem_sInf.mpr fun W hW => hW.1

theorem cyclic_submodule_stable (a b : Fin n) (x : V) (hx : x ∈ cyc E u) : E a b x ∈ cyc E u := by
  unfold cyc at hx ⊢
  rw [Submodule.mem_sInf] at hx ⊢
  intro W hW
  exact hW.2 a b x (hx W hW)

theorem compact_span_le_cyclic : kSpan ε E u ≤ cyc E u := by
  unfold kSpan
  apply sInf_le
  refine ⟨mem_cyclic_self E u, ?_⟩
  intro a b _ x hx
  exact cyclic_submodule_stable E u a b x hx

theorem ew_cons (p : Fin n × Fin n) (w : List (Fin n × Fin n)) (y : V) :
    ew E (p :: w) y = E p.1 p.2 (ew E w y) := by
  first | rfl | simp [ew]

theorem ew_nil (y : V) : ew E [] y = y := by
  first | rfl | simp [ew]

theorem word_action_mem_pfil (j : ℕ) (w : List (Fin n × Fin n)) (hw : w.length ≤ j)
    (hnc : ∀ p ∈ w, ε p.1 ≠ ε p.2) (y : V) (hy : y ∈ kSpan ε E u) : ew E w y ∈ pfil ε E u j := by
  unfold pfil
  exact Submodule.subset_span ⟨w, hw, hnc, y, hy, rfl⟩

theorem pfil_monotone_in_length {j j' : ℕ} (h : j ≤ j') : pfil ε E u j ≤ pfil ε E u j' := by
  unfold pfil
  apply Submodule.span_mono
  rintro x ⟨w, hw, hnc, y, hy, rfl⟩
  exact ⟨w, hw.trans h, hnc, y, hy, rfl⟩

theorem noncompact_generator_raises_pfil (j : ℕ) (a b : Fin n) (hab : ε a ≠ ε b) :
    ∀ x ∈ pfil ε E u j, E a b x ∈ pfil ε E u (j + 1) := by
  have key : pfil ε E u j ≤ (pfil ε E u (j + 1)).comap (E a b) := by
    unfold pfil
    rw [Submodule.span_le]
    rintro z ⟨w, hw, hnc, y, hy, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    refine Submodule.subset_span ⟨(a, b) :: w, ?_, ?_, y, hy, ?_⟩
    · simp only [List.length_cons]; omega
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hab
      · exact hnc p hp
    · exact (ew_cons E (a, b) w y).symm
  intro x hx
  exact key hx

theorem gl_commutator_apply (hE : GlRel E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by
  have h : E a b (E c d x) - E c d (E a b x) =
      (if b = c then E a d else 0) x - (if d = a then E c b else 0) x :=
    LinearMap.congr_fun (hE a b c d) x
  rw [← sub_eq_iff_eq_add', h]
  split_ifs <;> simp

theorem compact_generator_word_mem_pfil (hE : GlRel E) (a b : Fin n) (hab : ε a = ε b) (y : V) (hy : y ∈ kSpan ε E u) :
    ∀ w : List (Fin n × Fin n), (∀ p ∈ w, ε p.1 ≠ ε p.2) →
      E a b (ew E w y) ∈ pfil ε E u w.length := by
  intro w
  induction w with
  | nil =>
    intro _
    have hy' : E a b y ∈ kSpan ε E u := compact_span_compact_stable ε E u a b hab y hy
    have h0 := word_action_mem_pfil ε E u 0 [] (le_refl _) (by intro p hp; cases hp) (E a b y) hy'
    rw [ew_nil] at h0
    rw [ew_nil]
    exact h0
  | cons p w ih =>
    intro hnc
    have hnc' : ∀ q ∈ w, ε q.1 ≠ ε q.2 := fun q hq => hnc q (List.mem_cons.mpr (Or.inr hq))
    have hp : ε p.1 ≠ ε p.2 := hnc p (List.mem_cons.mpr (Or.inl rfl))
    have hih := ih hnc'
    rw [ew_cons, gl_commutator_apply E hE a b p.1 p.2]
    simp only [List.length_cons]
    refine add_mem (noncompact_generator_raises_pfil ε E u _ p.1 p.2 hp _ hih) (sub_mem ?_ ?_)
    · split_ifs with h1
      · have hne : ε a ≠ ε p.2 := by rw [hab, h1]; exact hp
        have hnc2 : ∀ q ∈ (a, p.2) :: w, ε q.1 ≠ ε q.2 := by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hne
          · exact hnc' q hq
        have h3 := word_action_mem_pfil ε E u (w.length + 1) ((a, p.2) :: w) (by simp) hnc2 y hy
        rw [ew_cons] at h3
        exact h3
      · exact Submodule.zero_mem _
    · split_ifs with h2
      · have hne : ε p.1 ≠ ε b := by rw [← hab, ← h2]; exact hp
        have hnc2 : ∀ q ∈ (p.1, b) :: w, ε q.1 ≠ ε q.2 := by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hne
          · exact hnc' q hq
        have h3 := word_action_mem_pfil ε E u (w.length + 1) ((p.1, b) :: w) (by simp) hnc2 y hy
        rw [ew_cons] at h3
        exact h3
      · exact Submodule.zero_mem _

theorem pfil_compact_stable (hE : GlRel E) (j : ℕ) : KStable ε E (pfil ε E u j) := by
  intro a b hab x hx
  have key : pfil ε E u j ≤ (pfil ε E u j).comap (E a b) :=
    Submodule.span_le.mpr (by
      rintro z ⟨w, hw, hnc, y, hy, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      exact pfil_monotone_in_length ε E u hw (compact_generator_word_mem_pfil ε E u hE a b hab y hy w hnc))
  exact key hx

theorem poincare_filtration_succ (hE : GlRel E) (j : ℕ) (a b : Fin n) :
    ∀ x ∈ pfil ε E u j, E a b x ∈ pfil ε E u (j + 1) := by
  intro x hx
  by_cases hab : ε a = ε b
  · exact pfil_monotone_in_length ε E u (Nat.le_succ j) (pfil_compact_stable ε E u hE j a b hab x hx)
  · exact noncompact_generator_raises_pfil ε E u j a b hab x hx

theorem poincare_filtration_zero : pfil ε E u 0 = kSpan ε E u := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨w, hw, hnc, y, hy, rfl⟩
    cases w with
    | nil => rw [SetLike.mem_coe, ew_nil]; exact hy
    | cons p w => simp at hw
  · intro y hy
    have h0 := word_action_mem_pfil ε E u 0 [] (le_refl _) (by intro p hp; cases hp) y hy
    rw [ew_nil] at h0
    exact h0

theorem pfil_le_cyclic (j : ℕ) : pfil ε E u j ≤ cyc E u := by
  apply Submodule.span_le.mpr
  rintro z ⟨w, -, -, y, hy, rfl⟩
  rw [SetLike.mem_coe]
  have hy' : y ∈ cyc E u := compact_span_le_cyclic ε E u hy
  clear hy
  induction w with
  | nil => rw [ew_nil]; exact hy'
  | cons p w ih => rw [ew_cons]; exact cyclic_submodule_stable E u p.1 p.2 _ ih

theorem pfil_succ_le_sup_map (j : ℕ) : pfil ε E u (j + 1) ≤
    pfil ε E u j ⊔ ⨆ p : Fin n × Fin n, (pfil ε E u j).map (E p.1 p.2) := by
  apply Submodule.span_le.mpr
  rintro z ⟨w, hw, hnc, y, hy, rfl⟩
  rw [SetLike.mem_coe]
  cases w with
  | nil => exact Submodule.mem_sup_left (word_action_mem_pfil ε E u j [] (Nat.zero_le _) hnc y hy)
  | cons p w =>
    have hlen : w.length ≤ j := by
      have h' := hw
      simp only [List.length_cons] at h'
      omega
    have hmem : ew E w y ∈ pfil ε E u j :=
      word_action_mem_pfil ε E u j w hlen (fun q hq => hnc q (List.mem_cons.mpr (Or.inr hq))) y hy
    rw [ew_cons]
    apply Submodule.mem_sup_right
    apply Submodule.mem_iSup_of_mem p
    exact Submodule.mem_map_of_mem hmem

theorem pfil_finite_dimensional (h0 : FiniteDimensional ℂ (kSpan ε E u)) (j : ℕ) :
    FiniteDimensional ℂ (pfil ε E u j) := by
  induction j with
  | zero => rw [poincare_filtration_zero]; exact h0
  | succ j ih =>
    haveI := ih
    exact Submodule.finiteDimensional_of_le (pfil_succ_le_sup_map ε E u j)

end U1Pfil

theorem pfil_facts_hold : PfilFacts := by
  intro V _ _ n ε E u hE
  refine ⟨poincare_filtration_zero ε E u, fun j => pfil_monotone_in_length ε E u (Nat.le_succ j),
    fun j => pfil_compact_stable ε E u hE j, fun j a b => poincare_filtration_succ ε E u hE j a b,
    fun j => pfil_le_cyclic ε E u j, ?_, fun h0 j => pfil_finite_dimensional ε E u h0 j⟩
  intro x hx
  have hmono : Monotone (pfil ε E u) := by
    intro i k h
    exact pfil_monotone_in_length ε E u h
  have hdir : Directed (· ≤ ·) (pfil ε E u) := hmono.directed_le
  have hle : cyc E u ≤ ⨆ j, pfil ε E u j := by
    unfold cyc
    apply sInf_le
    refine ⟨?_, ?_⟩
    · apply Submodule.mem_iSup_of_mem 0
      rw [poincare_filtration_zero]
      exact mem_kSpan_self' ε E u
    · intro a b y hy
      obtain ⟨j, hj⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hy
      exact Submodule.mem_iSup_of_mem (j + 1) (poincare_filtration_succ ε E u hE j a b y hj)
  exact (Submodule.mem_iSup_of_directed _ hdir).mp (hle hx)

theorem casimir_on_cyclic_holds : CasOnCyc := by
  intro V _ _ n E c u hE hu x hx
  have hcom := (casimir_central_holds (Module.End ℂ V) n (fun _ => true) E hE).1
  have hle : cyc E u ≤ LinearMap.ker (Cas E - c • (1 : Module.End ℂ V)) := by
    apply sInf_le
    refine ⟨?_, ?_⟩
    · simp [hu]
    · intro a b y hy
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hy ⊢
      have := congrArg (fun T : Module.End ℂ V => T y) (hcom a b)
      simp only [Module.End.mul_apply] at this
      rw [this, sub_eq_zero.mp hy, map_smul, sub_self]
  have := hle hx
  simpa [sub_eq_zero] using this

section U1Arr
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem arr_finset_sum_apply {j : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Arr V n j) (α : Fin j → Fin n × Fin n) :
    (∑ i ∈ s, f i) α = ∑ i ∈ s, f i α := by
  have h := congrFun (map_sum (arrOf V n j) f s) α
  rw [Finset.sum_apply] at h
  exact h

private theorem arrTo_comp_pi_comp_arrOf_apply {j : ℕ}
    (g : (Fin j → Fin n × Fin n) → ((Fin j → Fin n × Fin n) → V) →ₗ[ℂ] V)
    (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    (arrTo V n j ∘ₗ LinearMap.pi g ∘ₗ arrOf V n j) F α = g α (arrOf V n j F) := rfl

theorem factorAction_apply' {j : ℕ} (i : Fin j) (c d : Fin n) (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    factorAction i c d F α = (if (α i).1 = c then F (Function.update α i (d, (α i).2)) else 0) -
      (if (α i).2 = d then F (Function.update α i ((α i).1, c)) else 0) := by
  unfold factorAction
  rw [arrTo_comp_pi_comp_arrOf_apply]
  split_ifs <;> first | rfl | simp [arrOf]

theorem pointwise_operator_apply {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) (F : Arr V n j)
    (α : Fin j → Fin n × Fin n) : ptE E c d F α = E c d (F α) := by
  rfl

private theorem arr_add_apply {j : ℕ} (F G : Arr V n j) (α : Fin j → Fin n × Fin n) :
    (F + G) α = F α + G α := rfl

theorem arr_operator_apply {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) (F : Arr V n j)
    (α : Fin j → Fin n × Fin n) : arrE E j c d F α = ∑ i, factorAction i c d F α + E c d (F α) := by
  have h1 : arrE E j c d F = (∑ i : Fin j, factorAction i c d F) + ptE E c d F := by
    show ((∑ i : Fin j, factorAction i c d) + ptE E c d : Module.End ℂ (Arr V n j)) F = _
    rw [LinearMap.add_apply, LinearMap.sum_apply]
  rw [h1, arr_add_apply, arr_finset_sum_apply, pointwise_operator_apply]

theorem sum_update_first_index_swap {M : Type*} [AddCommMonoid M] {j : ℕ} (i : Fin j) (c d : Fin n)
    (f : (Fin j → Fin n × Fin n) → (Fin j → Fin n × Fin n) → M) :
    ∑ α, (if (α i).1 = c then f α (Function.update α i (d, (α i).2)) else 0) =
      ∑ β, (if (β i).1 = d then f (Function.update β i (c, (β i).2)) β else 0) := by
  refine Finset.sum_nbij' (fun α => Function.update α i ((Equiv.swap c d) (α i).1, (α i).2))
    (fun β => Function.update β i ((Equiv.swap c d) (β i).1, (β i).2))
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro α _; simp
  · intro β _; simp
  · intro α _
    by_cases hc : (α i).1 = c
    · have hα : Function.update α i (c, (α i).2) = α := by
        rw [← hc]; exact Function.update_eq_self i α
      simp [hc, hα]
    · have hne : (Equiv.swap c d) (α i).1 ≠ d := by
        intro h; apply hc
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
        exact h
      simp [hc, hne]

theorem sum_update_second_index_swap {M : Type*} [AddCommMonoid M] {j : ℕ} (i : Fin j) (c d : Fin n)
    (f : (Fin j → Fin n × Fin n) → (Fin j → Fin n × Fin n) → M) :
    ∑ α, (if (α i).2 = d then f α (Function.update α i ((α i).1, c)) else 0) =
      ∑ β, (if (β i).2 = c then f (Function.update β i ((β i).1, d)) β else 0) := by
  refine Finset.sum_nbij' (fun α => Function.update α i ((α i).1, (Equiv.swap c d) (α i).2))
    (fun β => Function.update β i ((β i).1, (Equiv.swap c d) (β i).2))
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro α _; simp
  · intro β _; simp
  · intro α _
    by_cases hc : (α i).2 = d
    · have hα : Function.update α i ((α i).1, d) = α := by
        rw [← hc]; exact Function.update_eq_self i α
      simp [hc, hα]
    · have hne : (Equiv.swap c d) (α i).2 ≠ c := by
        intro h; apply hc
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
        exact h
      simp [hc, hne]

end U1Arr

section U1Arr2
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

private theorem arr_ext {j : ℕ} {F G : Arr V n j} (h : ∀ α, F α = G α) : F = G := by
  first
  | exact PiLp.ext h
  | exact (WithLp.linearEquiv 2 ℂ ((Fin j → Fin n × Fin n) → V)).injective (funext h)
  | exact funext h

private theorem arr_sub_apply {j : ℕ} (F G : Arr V n j) (α : Fin j → Fin n × Fin n) :
    (F - G) α = F α - G α := rfl

private theorem arr_zero_apply {j : ℕ} (α : Fin j → Fin n × Fin n) :
    (0 : Arr V n j) α = 0 := rfl

theorem factorAction_commutator {j : ℕ} (i : Fin j) (a b c d : Fin n) :
    (factorAction i a b * factorAction i c d - factorAction i c d * factorAction i a b : Module.End ℂ (Arr V n j)) =
      (if b = c then factorAction i a d else 0) - (if d = a then factorAction i c b else 0) := by
  apply LinearMap.ext; intro F
  apply arr_ext; intro α
  show factorAction i a b (factorAction i c d F) α - factorAction i c d (factorAction i a b F) α = _
  split_ifs <;> simp [arr_sub_apply, arr_zero_apply, factorAction_apply'] <;> (try split_ifs) <;>
    first | abel1 | (simp_all; done) | (simp_all; abel1) | (subst_vars; abel1) | (subst_vars; simp_all)

end U1Arr2

section U1Arr3
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem factorAction_commute_of_ne {j : ℕ} (i i' : Fin j) (hii : i ≠ i') (a b c d : Fin n) :
    (factorAction i a b * factorAction i' c d : Module.End ℂ (Arr V n j)) = factorAction i' c d * factorAction i a b := by
  apply LinearMap.ext; intro F
  apply arr_ext; intro α
  have hcomm : ∀ v w : Fin n × Fin n, Function.update (Function.update α i v) i' w =
      Function.update (Function.update α i' w) i v := fun v w => Function.update_comm hii v w α
  show factorAction i a b (factorAction i' c d F) α = factorAction i' c d (factorAction i a b F) α
  simp only [factorAction_apply', Function.update_apply, if_neg hii, if_neg (Ne.symm hii), hcomm]
  split_ifs <;> first | abel1 | (simp_all; done) | (simp_all; abel1) | (subst_vars; abel1) | (subst_vars; simp_all)

theorem factorAction_commute_pointwiseAction {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (i : Fin j) (a b c d : Fin n) :
    (factorAction i a b * ptE E c d : Module.End ℂ (Arr V n j)) = ptE E c d * factorAction i a b := by
  apply LinearMap.ext; intro F
  apply arr_ext; intro α
  show factorAction i a b (ptE E c d F) α = ptE E c d (factorAction i a b F) α
  simp only [factorAction_apply', pointwise_operator_apply]
  split_ifs <;> simp

theorem pointwise_operator_gl_relation {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (a b c d : Fin n) :
    (ptE E a b * ptE E c d - ptE E c d * ptE E a b : Module.End ℂ (Arr V n j)) =
      (if b = c then ptE E a d else 0) - (if d = a then ptE E c b else 0) := by
  apply LinearMap.ext; intro F
  apply arr_ext; intro α
  show E a b (E c d (F α)) - E c d (E a b (F α)) = _
  rw [sub_eq_of_eq_add' (gl_commutator_apply E hE a b c d (F α))]
  split_ifs <;> first | rfl | simp [arr_sub_apply, arr_zero_apply, pointwise_operator_apply]

theorem commutator_of_sums_split {A : Type*} [Ring A] {ι : Type*} (s : Finset ι) (S T : ι → A) (P Q : A)
    (hST : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → S i * T i' = T i' * S i)
    (hSQ : ∀ i ∈ s, S i * Q = Q * S i) (hPT : ∀ i ∈ s, P * T i = T i * P) :
    (∑ i ∈ s, S i + P) * (∑ i ∈ s, T i + Q) - (∑ i ∈ s, T i + Q) * (∑ i ∈ s, S i + P) =
      ∑ i ∈ s, (S i * T i - T i * S i) + (P * Q - Q * P) := by
  have key : ∀ i ∈ s, ∑ i' ∈ s, (S i * T i' - T i' * S i) = S i * T i - T i * S i := by
    intro i hi
    rw [Finset.sum_eq_single i]
    · intro i' hi' hne
      rw [hST i hi i' hi' (Ne.symm hne), sub_self]
    · intro h
      exact absurd hi h
  have hSQ' : (∑ i ∈ s, S i) * Q = Q * ∑ i ∈ s, S i := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl hSQ
  have hPT' : P * (∑ i ∈ s, T i) = (∑ i ∈ s, T i) * P := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl hPT
  have e1 : (∑ i ∈ s, S i) * (∑ i ∈ s, T i) = ∑ i ∈ s, ∑ i' ∈ s, S i * T i' := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  have e2 : (∑ i ∈ s, T i) * (∑ i ∈ s, S i) = ∑ i ∈ s, ∑ i' ∈ s, T i' * S i := by
    simp only [Finset.sum_mul, Finset.mul_sum]
  have hST' : (∑ i ∈ s, S i) * (∑ i ∈ s, T i) - (∑ i ∈ s, T i) * (∑ i ∈ s, S i) =
      ∑ i ∈ s, (S i * T i - T i * S i) := by
    rw [e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [← Finset.sum_sub_distrib]
    exact key i hi
  have expand : (∑ i ∈ s, S i + P) * (∑ i ∈ s, T i + Q) - (∑ i ∈ s, T i + Q) * (∑ i ∈ s, S i + P) =
      ((∑ i ∈ s, S i) * (∑ i ∈ s, T i) - (∑ i ∈ s, T i) * (∑ i ∈ s, S i)) +
        ((∑ i ∈ s, S i) * Q - Q * ∑ i ∈ s, S i) + (P * (∑ i ∈ s, T i) - (∑ i ∈ s, T i) * P) +
        (P * Q - Q * P) := by
    noncomm_ring
  rw [expand, hST', hSQ', hPT']
  simp only [sub_self, add_zero]

theorem arr_operators_gl_relation {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) :
    GlRel (arrE E j) := by
  intro a b c d
  simp only [arrE]
  rw [commutator_of_sums_split Finset.univ (fun i => factorAction i a b) (fun i => factorAction i c d) (ptE E a b) (ptE E c d)
    (fun i _ i' _ h => factorAction_commute_of_ne i i' h a b c d) (fun i _ => factorAction_commute_pointwiseAction E i a b c d)
    (fun i _ => (factorAction_commute_pointwiseAction E i c d a b).symm)]
  simp only [factorAction_commutator, pointwise_operator_gl_relation E hE]
  split_ifs <;> simp [Finset.sum_sub_distrib] <;> abel

theorem factorAction_adjoint {j : ℕ} (i : Fin j) (a b : Fin n) (F G : Arr V n j) :
    ⟪factorAction i a b F, G⟫_ℂ = ⟪F, factorAction i b a G⟫_ℂ := by
  have hL : ∀ α, ⟪factorAction i a b F α, G α⟫_ℂ =
      (if (α i).1 = a then ⟪F (Function.update α i (b, (α i).2)), G α⟫_ℂ else 0) -
      (if (α i).2 = b then ⟪F (Function.update α i ((α i).1, a)), G α⟫_ℂ else 0) := by
    intro α; rw [factorAction_apply']; split_ifs <;> simp [inner_sub_left]
  have hR : ∀ β, ⟪F β, factorAction i b a G β⟫_ℂ =
      (if (β i).1 = b then ⟪F β, G (Function.update β i (a, (β i).2))⟫_ℂ else 0) -
      (if (β i).2 = a then ⟪F β, G (Function.update β i ((β i).1, b))⟫_ℂ else 0) := by
    intro β; rw [factorAction_apply']; split_ifs <;> simp [inner_sub_right]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [hL, hR, Finset.sum_sub_distrib]
  rw [sum_update_first_index_swap i a b (fun α β => ⟪F β, G α⟫_ℂ), sum_update_second_index_swap i a b (fun α β => ⟪F β, G α⟫_ℂ)]

theorem arr_operators_compact_unitary {j : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (hU : IsUnitary ε E) : KUnit ε (arrE E j) := by
  intro a b hab F G
  have hs : (sgn ε a b : ℂ) = 1 := by
    unfold sgn
    rw [if_pos hab]
    simp
  have hpt : ⟪ptE E a b F, G⟫_ℂ = ⟪F, ptE E b a G⟫_ℂ := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [pointwise_operator_apply, pointwise_operator_apply, hU a b (F α) (G α), hs, one_mul]
  show ⟪((∑ i : Fin j, factorAction i a b) + ptE E a b : Module.End ℂ (Arr V n j)) F, G⟫_ℂ =
    ⟪F, ((∑ i : Fin j, factorAction i b a) + ptE E b a : Module.End ℂ (Arr V n j)) G⟫_ℂ
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.sum_apply,
    inner_add_left, inner_add_right, sum_inner, inner_sum, hpt]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => factorAction_adjoint i a b F G)

end U1Arr3

section U1Arr4
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

def u1W (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} (α : Fin j → Fin n × Fin n) : Module.End ℂ V :=
  ew E (List.ofFn α).reverse

theorem word_product_zero (E : Fin n → Fin n → Module.End ℂ V) (α : Fin 0 → Fin n × Fin n) : u1W E α = 1 := by
  unfold u1W
  rw [List.ofFn_zero]
  rfl

theorem word_product_succ (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} (α : Fin (j + 1) → Fin n × Fin n) :
    u1W E α = E (α (Fin.last j)).1 (α (Fin.last j)).2 * u1W E (Fin.init α) := by
  unfold u1W
  rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append]
  rfl

theorem commutator_word_operator_sum (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (c d : Fin n) :
    ∀ (j : ℕ) (α : Fin j → Fin n × Fin n), E c d * u1W E α - u1W E α * E c d =
      ∑ i, ((if d = (α i).1 then u1W E (Function.update α i (c, (α i).2)) else 0) -
        (if (α i).2 = c then u1W E (Function.update α i ((α i).1, d)) else 0)) := by
  intro j
  induction j with
  | zero =>
    intro α
    rw [word_product_zero]
    simp
  | succ j ih =>
    intro α
    have hlast : ∀ v : Fin n × Fin n, u1W E (Function.update α (Fin.last j) v) =
        E v.1 v.2 * u1W E (Fin.init α) := by
      intro v
      rw [word_product_succ]
      simp
    have hcast : ∀ (i : Fin j) (v : Fin n × Fin n), u1W E (Function.update α i.castSucc v) =
        E (α (Fin.last j)).1 (α (Fin.last j)).2 * u1W E (Function.update (Fin.init α) i v) := by
      intro i v
      rw [word_product_succ]
      have hne : Fin.last j ≠ i.castSucc := (Fin.castSucc_lt_last i).ne'
      simp [Function.update_apply, hne, Fin.init_update_castSucc]
    have hsplit : E c d * u1W E α - u1W E α * E c d =
        (E c d * E (α (Fin.last j)).1 (α (Fin.last j)).2 -
          E (α (Fin.last j)).1 (α (Fin.last j)).2 * E c d) * u1W E (Fin.init α) +
        E (α (Fin.last j)).1 (α (Fin.last j)).2 *
          (E c d * u1W E (Fin.init α) - u1W E (Fin.init α) * E c d) := by
      rw [word_product_succ E α]
      noncomm_ring
    rw [hsplit, hE c d (α (Fin.last j)).1 (α (Fin.last j)).2, ih (Fin.init α), Finset.mul_sum,
      Fin.sum_univ_castSucc, hlast, hlast]
    rw [add_comm ((_ - _) * u1W E (Fin.init α))]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hcast, hcast]
      simp only [Fin.init]
      by_cases h1 : d = (α i.castSucc).1 <;> by_cases h2 : (α i.castSucc).2 = c <;>
        simp [h1, h2, mul_sub]
    · by_cases h1 : d = (α (Fin.last j)).1 <;> by_cases h2 : (α (Fin.last j)).2 = c <;>
        simp [h1, h2, sub_mul]

theorem theta_map_apply (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} (F : Arr V n j) :
    thetaA E j F = ∑ α, u1W E α (F α) := by
  unfold thetaA
  rw [LinearMap.sum_apply]
  rfl

theorem symmetrization_equivariant (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) {j : ℕ} (c d : Fin n)
    (F : Arr V n j) : thetaA E j (arrE E j c d F) = E c d (thetaA E j F) := by
  have hder : ∀ α : Fin j → Fin n × Fin n, E c d (u1W E α (F α)) = u1W E α (E c d (F α)) +
      ∑ i, ((if (α i).1 = d then u1W E (Function.update α i (c, (α i).2)) (F α) else 0) -
        (if (α i).2 = c then u1W E (Function.update α i ((α i).1, d)) (F α) else 0)) := by
    intro α
    have h := LinearMap.congr_fun (commutator_word_operator_sum E hE c d j α) (F α)
    rw [LinearMap.sub_apply, LinearMap.sum_apply] at h
    have h' : E c d (u1W E α (F α)) - u1W E α (E c d (F α)) =
        ∑ i, ((if d = (α i).1 then u1W E (Function.update α i (c, (α i).2)) else 0) -
          (if (α i).2 = c then u1W E (Function.update α i ((α i).1, d)) else 0)) (F α) := h
    rw [← sub_eq_iff_eq_add', h']
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [eq_comm (a := d)]
    split_ifs <;> simp
  have hkey : ∑ α : Fin j → Fin n × Fin n, ∑ i, u1W E α (factorAction i c d F α) =
      ∑ α : Fin j → Fin n × Fin n, ∑ i,
        ((if (α i).1 = d then u1W E (Function.update α i (c, (α i).2)) (F α) else 0) -
          (if (α i).2 = c then u1W E (Function.update α i ((α i).1, d)) (F α) else 0)) := by
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have e1 : ∀ α : Fin j → Fin n × Fin n, u1W E α (factorAction i c d F α) =
        (if (α i).1 = c then u1W E α (F (Function.update α i (d, (α i).2))) else 0) -
        (if (α i).2 = d then u1W E α (F (Function.update α i ((α i).1, c))) else 0) := by
      intro α; rw [factorAction_apply']; split_ifs <;> simp
    simp only [e1, Finset.sum_sub_distrib]
    rw [sum_update_first_index_swap i c d (fun α β => u1W E α (F β)), sum_update_second_index_swap i c d (fun α β => u1W E α (F β))]
  rw [theta_map_apply, theta_map_apply, map_sum]
  simp only [arr_operator_apply, map_add, map_sum, hder, Finset.sum_add_distrib]
  rw [hkey]
  exact add_comm _ _

end U1Arr4

section U1Theta
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)

theorem symmetrization_apply {j : ℕ} (F : Arr V n j) :
    thetaA E j F = ∑ α, ew E (List.ofFn α).reverse (F α) := by
  unfold thetaA
  rw [LinearMap.sum_apply]
  rfl

theorem mem_noncompact_arr_iff {j : ℕ} (F : Arr V n j) :
    F ∈ arrV0 ε E u j ↔ ∀ α, F α ∈ (if ∀ i, ε (α i).1 ≠ ε (α i).2 then kSpan ε E u else ⊥) := by
  unfold arrV0
  rw [Submodule.mem_iInf]
  first | rfl | exact Iff.rfl | (simp only [Submodule.mem_comap]; rfl)

theorem perm_arr_apply {j : ℕ} (σ : Equiv.Perm (Fin j)) (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    permArr V n σ F α = F (fun i => α (σ i)) := by
  rfl

theorem reverse_of_fn_noncompact {j : ℕ} (α : Fin j → Fin n × Fin n) (h : ∀ i, ε (α i).1 ≠ ε (α i).2) :
    ∀ p ∈ (List.ofFn α).reverse, ε p.1 ≠ ε p.2 := by
  intro p hp
  rw [List.mem_reverse, List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  exact h i

theorem theta_noncompact_mem_pfil (j : ℕ) (F : Arr V n j) (hF : F ∈ arrV0 ε E u j) :
    thetaA E j F ∈ pfil ε E u j := by
  rw [symmetrization_apply (E := E) (F := F)]
  refine sum_mem (fun α _ => ?_)
  have hα := (mem_noncompact_arr_iff ε E u F).mp hF α
  by_cases h : ∀ i, ε (α i).1 ≠ ε (α i).2
  · rw [if_pos h] at hα
    exact word_action_mem_pfil ε E u j _ (by simp) (reverse_of_fn_noncompact ε α h) _ hα
  · rw [if_neg h, Submodule.mem_bot] at hα
    rw [hα, map_zero]
    exact Submodule.zero_mem _

theorem pfil_succ_le_theta_image_sup (j : ℕ) : pfil ε E u (j + 1) ≤
    (arrV0 ε E u (j + 1)).map (thetaA E (j + 1)) ⊔ pfil ε E u j := by
  apply Submodule.span_le.mpr
  rintro z ⟨w, hw, hnc, y, hy, rfl⟩
  rw [SetLike.mem_coe]
  by_cases hlen : w.length ≤ j
  · exact Submodule.mem_sup_right (word_action_mem_pfil ε E u j w hlen hnc y hy)
  · have hl : w.length = j + 1 := by omega
    apply Submodule.mem_sup_left
    let α0 : Fin (j + 1) → Fin n × Fin n := fun i =>
      w.reverse.get ⟨i, by rw [List.length_reverse, hl]; exact i.isLt⟩
    have hα0 : (List.ofFn α0).reverse = w := by
      rw [List.reverse_eq_iff]
      first
      | (apply List.ext_get (by simp [hl]); intro k h1 h2; rw [List.get_ofFn]; rfl)
      | (apply List.ext_getElem (by simp [hl]); intro k h1 h2; rw [List.getElem_ofFn]; rfl)
    have hnc0 : ∀ i, ε (α0 i).1 ≠ ε (α0 i).2 := by
      intro i
      have hm : α0 i ∈ w.reverse := by
        first
        | exact List.get_mem _ _
        | exact List.get_mem _ _ _
        | simp [α0, List.getElem_mem]
      exact hnc (α0 i) (List.mem_reverse.mp hm)
    let F : Arr V n (j + 1) :=
      (WithLp.linearEquiv 2 ℂ ((Fin (j + 1) → Fin n × Fin n) → V)).symm
        (fun β => if β = α0 then y else 0)
    have hF : ∀ β, F β = if β = α0 then y else 0 := fun β => rfl
    rw [Submodule.mem_map]
    refine ⟨F, ?_, ?_⟩
    · rw [mem_noncompact_arr_iff]
      intro β
      rw [hF]
      by_cases hb : β = α0
      · rw [if_pos hb, hb, if_pos hnc0]
        exact hy
      · rw [if_neg hb]
        exact Submodule.zero_mem _
    · rw [symmetrization_apply (E := E) (F := F), Finset.sum_eq_single α0]
      · rw [hF, if_pos rfl, hα0]
      · intro β _ hb
        rw [hF, if_neg hb, map_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h

private theorem bool_eq_of_ne_of_ne {p q r : Bool} (h1 : p ≠ q) (h2 : q ≠ r) : p = r := by
  cases p <;> cases q <;> cases r <;> simp_all

theorem permuted_words_diff_mem_pfil (hE : GlRel E) (y : V) (hy : y ∈ kSpan ε E u) :
    ∀ l1 l2 : List (Fin n × Fin n), l1.Perm l2 → (∀ p ∈ l1, ε p.1 ≠ ε p.2) →
      ∀ m, l1.length = m + 1 → ew E l1 y - ew E l2 y ∈ pfil ε E u m := by
  intro l1 l2 hp
  induction hp with
  | nil =>
    intro _ m hm
    simp only [List.length_nil] at hm
    omega
  | @cons x l₁ l₂ h ih =>
    intro hnc m hm
    have hnc' : ∀ q ∈ l₁, ε q.1 ≠ ε q.2 := fun q hq => hnc q (List.mem_cons.mpr (Or.inr hq))
    simp only [ew_cons]
    rw [← map_sub]
    simp only [List.length_cons] at hm
    cases m with
    | zero =>
      have e1 : l₁ = [] := by
        first
        | exact List.eq_nil_of_length_eq_zero (by omega)
        | exact List.length_eq_zero_iff.mp (by omega)
        | exact List.length_eq_zero.mp (by omega)
      subst e1
      have e2 : l₂ = [] := by
        first
        | exact h.symm.eq_nil
        | exact h.nil_eq.symm
      subst e2
      rw [sub_self, map_zero]
      exact Submodule.zero_mem _
    | succ k =>
      exact poincare_filtration_succ ε E u hE k x.1 x.2 _ (ih hnc' k (by omega))
  | swap x z l =>
    intro hnc m hm
    simp only [List.length_cons] at hm
    have hx : ε x.1 ≠ ε x.2 := hnc x (by simp)
    have hz : ε z.1 ≠ ε z.2 := hnc z (by simp)
    have hl : ∀ q ∈ l, ε q.1 ≠ ε q.2 := fun q hq => hnc q (by simp [hq])
    have key : ∀ A B : V, A + B - A = B := fun A B => by abel
    simp only [ew_cons]
    rw [gl_commutator_apply E hE z.1 z.2 x.1 x.2, key]
    have hmono : pfil ε E u l.length ≤ pfil ε E u m := pfil_monotone_in_length ε E u (by omega)
    refine sub_mem ?_ ?_
    · split_ifs with h1
      · exact hmono (compact_generator_word_mem_pfil ε E u hE z.1 x.2
          (bool_eq_of_ne_of_ne hz (by rw [h1]; exact hx)) y hy l hl)
      · exact Submodule.zero_mem _
    · split_ifs with h2
      · exact hmono (compact_generator_word_mem_pfil ε E u hE x.1 z.2
          (bool_eq_of_ne_of_ne hx (by rw [h2]; exact hz)) y hy l hl)
      · exact Submodule.zero_mem _
  | @trans l₁ l₂ l₃ h12 h23 ih12 ih23 =>
    intro hnc m hm
    have hnc2 : ∀ q ∈ l₂, ε q.1 ≠ ε q.2 := fun q hq => hnc q (h12.mem_iff.mpr hq)
    have hlen : l₂.length = m + 1 := by rw [← h12.length_eq]; exact hm
    have e : ew E l₁ y - ew E l₃ y = (ew E l₁ y - ew E l₂ y) + (ew E l₂ y - ew E l₃ y) := by abel
    rw [e]
    exact add_mem (ih12 hnc m hm) (ih23 hnc2 m hlen)

theorem symmetrization_perm_sub_mem (hE : GlRel E) (j : ℕ) (F : Arr V n (j + 1)) (hF : F ∈ arrV0 ε E u (j + 1))
    (σ : Equiv.Perm (Fin (j + 1))) :
    thetaA E (j + 1) (permArr V n σ F) - thetaA E (j + 1) F ∈ pfil ε E u j := by
  let e : (Fin (j + 1) → Fin n × Fin n) ≃ (Fin (j + 1) → Fin n × Fin n) :=
    ⟨fun β => β ∘ σ.symm, fun α => α ∘ σ, fun α => by funext i; simp, fun β => by funext i; simp⟩
  rw [symmetrization_apply (E := E) (F := permArr V n σ F), symmetrization_apply (E := E) (F := F)]
  simp only [perm_arr_apply]
  rw [← Equiv.sum_comp e, ← Finset.sum_sub_distrib]
  refine sum_mem (fun β _ => ?_)
  have he1 : e β = β ∘ σ.symm := rfl
  have he2 : (fun i => e β (σ i)) = β := by
    funext i
    simp [he1]
  rw [he2, he1]
  have hβ := (mem_noncompact_arr_iff ε E u F).mp hF β
  by_cases h : ∀ i, ε (β i).1 ≠ ε (β i).2
  · rw [if_pos h] at hβ
    have hperm : (List.ofFn (β ∘ σ.symm)).reverse.Perm (List.ofFn β).reverse := by
      have h0 : (List.ofFn (β ∘ σ.symm)).Perm (List.ofFn β) := by
        first
        | exact Equiv.Perm.ofFn_comp_perm σ.symm β
        | exact List.ofFn_comp_perm σ.symm β
      exact (List.reverse_perm _).trans (h0.trans (List.reverse_perm _).symm)
    exact permuted_words_diff_mem_pfil ε E u hE (F β) hβ _ _ hperm
      (reverse_of_fn_noncompact ε (β ∘ σ.symm) (fun i => h (σ.symm i))) j (by simp)
  · rw [if_neg h, Submodule.mem_bot] at hβ
    rw [hβ, map_zero, map_zero, sub_zero]
    exact Submodule.zero_mem _

end U1Theta

theorem thetaFil_of (hp : PfilFacts) : ThetaFil := by
  intro V _ _ n ε E u hE
  exact ⟨fun j F hF => theta_noncompact_mem_pfil ε E u j F hF, fun j => pfil_succ_le_theta_image_sup ε E u j,
    fun j F hF σ => symmetrization_perm_sub_mem ε E u hE j F hF σ⟩

theorem arr_module_facts : ArrModule := by
  intro V _ _ n ε E j
  exact ⟨fun hE => ⟨arr_operators_gl_relation E hE, fun c d F => symmetrization_equivariant E hE c d F⟩,
    fun hU => arr_operators_compact_unitary ε E hU⟩

theorem theta_filtration_holds : ThetaFil := thetaFil_of pfil_facts_hold

end Formalism.REAL
