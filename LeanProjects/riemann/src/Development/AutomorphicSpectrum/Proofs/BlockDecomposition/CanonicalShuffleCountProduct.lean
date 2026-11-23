import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open Classical

namespace GlobalTheory.CompanionTheory.WordCount

variable {α : Type*}

noncomputable def T {ι : Type*} [Fintype ι] [DecidableEq ι] : List α → (ι → List α) → ℕ
  | [], E => if ∀ i, E i = [] then 1 else 0
  | a :: L, E => ∑ i, if (E i).head? = some a then T L (Function.update E i (E i).tail) else 0

theorem T_nil {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → List α) : T [] E = if ∀ i, E i = [] then 1 else 0 := by
  rfl

theorem T_cons {ι : Type*} [Fintype ι] [DecidableEq ι] (a : α) (L : List α) (E : ι → List α) :
    T (a :: L) E = ∑ i, if (E i).head? = some a then T L (Function.update E i (E i).tail) else 0 := by
  rfl

theorem T_comp {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι ≃ ι) (L : List α) (E : ι → List α) : T L (E ∘ σ) = T L E := by
  induction L generalizing E with
  | nil =>
    rw [T_nil, T_nil]
    have hiff : (∀ i, (E ∘ σ) i = []) ↔ ∀ i, E i = [] :=
      ⟨fun h i => by simpa using h (σ.symm i), fun h i => h (σ i)⟩
    by_cases hE : ∀ i, E i = []
    · rw [if_pos hE, if_pos (hiff.2 hE)]
    · rw [if_neg hE, if_neg (fun h' => hE (hiff.1 h'))]
  | cons a L ih =>
    rw [T_cons, T_cons]
    refine Fintype.sum_equiv σ _ _ fun i => ?_
    have hu : Function.update (E ∘ σ) i (E (σ i)).tail = Function.update E (σ i) (E (σ i)).tail ∘ σ := by
      funext j
      simp [Function.update_apply]
    simp only [Function.comp_apply, hu, ih]

theorem T_last {h : ℕ} (L : List α) (E : Fin (h + 1) → List α) (hE : E (Fin.last h) = []) :
    T L E = T L fun i : Fin h => E i.castSucc := by
  induction L generalizing E with
  | nil =>
    rw [T_nil, T_nil]
    have hiff : (∀ i, E i = []) ↔ ∀ i : Fin h, E i.castSucc = [] := by
      constructor
      · intro H i
        exact H _
      · intro H i
        induction i using Fin.lastCases with
        | last => exact hE
        | cast j => exact H j
    by_cases H : ∀ i : Fin h, E i.castSucc = []
    · rw [if_pos (hiff.2 H), if_pos H]
    · rw [if_neg (fun h' => H (hiff.1 h')), if_neg H]
  | cons a L ih =>
    rw [T_cons, T_cons, Fin.sum_univ_castSucc]
    have hlast : (if (E (Fin.last h)).head? = some a then
        T L (Function.update E (Fin.last h) (E (Fin.last h)).tail) else 0) = 0 := by
      simp [hE]
    rw [hlast, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hne : Fin.castSucc i ≠ Fin.last h := (Fin.castSucc_lt_last i).ne
    have hE' : Function.update E i.castSucc (E i.castSucc).tail (Fin.last h) = [] := by
      rw [Function.update_of_ne (Ne.symm hne)]
      exact hE
    rw [ih _ hE']
    have hf : (fun j : Fin h => Function.update E i.castSucc (E i.castSucc).tail j.castSucc) =
        Function.update (fun j : Fin h => E j.castSucc) i (E i.castSucc).tail := by
      funext j
      simp [Function.update_apply, Fin.castSucc_inj]
    rw [hf]

theorem T_block {ι : Type*} [Fintype ι] [DecidableEq ι] (R B : List α) (E : ι → List α) (g : ι)
    (H : ∀ i, i ≠ g → ∀ a ∈ B, (E i).head? ≠ some a) :
    T (B ++ R) E = if B <+: E g then T R (Function.update E g ((E g).drop B.length)) else 0 := by
  induction B generalizing E with
  | nil => simp
  | cons b B ih =>
    have H' : ∀ i, i ≠ g → ∀ a ∈ B, ((Function.update E g (E g).tail) i).head? ≠ some a := by
      intro i hi a ha
      rw [Function.update_of_ne hi]
      exact H i hi a (by simp [ha])
    rw [List.cons_append, T_cons, Finset.sum_eq_single g
      (fun i _ hi => by rw [if_neg (H i hi b (by simp))])
      (fun hg => absurd (Finset.mem_univ g) hg), ih _ H', Function.update_self, Function.update_idem]
    rcases hEg : E g with _ | ⟨x, xs⟩
    · simp
    · by_cases hx : x = b
      · subst hx
        by_cases hB : B <+: xs <;> simp [hB]
      · have hx' : b ≠ x := Ne.symm hx
        simp [hx, hx']

theorem sub_last {ι : Type*} [DecidableEq ι] {n : ℕ} (w : Fin (n + 1) → α) (c : Fin (n + 1) → ι) (i : ι) :
    ((List.finRange (n + 1)).filter (fun p => c p = i)).map w =
      ((List.finRange n).filter (fun p => c p.castSucc = i)).map (fun p => w p.castSucc) ++
        (if c (Fin.last n) = i then [w (Fin.last n)] else []) := by
  rw [List.finRange_succ_last, List.filter_append, List.map_append, List.filter_map, List.map_map]
  by_cases hc : c (Fin.last n) = i
  · simp [hc, Function.comp_def]
  · simp [hc, Function.comp_def]

theorem step_iff {ι : Type*} [DecidableEq ι] (R E : ι → List α) (j : ι) (a : α) :
    (∀ i, (if j = i then a :: R i else R i) = E i) ↔
      (E j).head? = some a ∧ ∀ i, R i = Function.update E j (E j).tail i := by
  constructor
  · intro h
    have hj := h j
    rw [if_pos rfl] at hj
    refine ⟨by rw [← hj, List.head?_cons], fun i => ?_⟩
    by_cases hij : i = j
    · rw [hij, Function.update_self, ← hj, List.tail_cons]
    · have hi := h i
      rw [if_neg (Ne.symm hij)] at hi
      rw [Function.update_of_ne hij, hi]
  · rintro ⟨hh, hR⟩ i
    by_cases hij : j = i
    · rw [if_pos hij, hR i, ← hij, Function.update_self]
      cases hE : E j with
      | nil =>
        rw [hE] at hh
        exact absurd hh (by simp)
      | cons x t =>
        rw [hE] at hh
        simp only [List.head?_cons, Option.some.injEq] at hh
        rw [hh, List.tail_cons]
    · rw [if_neg hij, hR i, Function.update_of_ne (Ne.symm hij)]

theorem card_filter_reverse_map_eq_shuffle_count {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (w : Fin n → α) (E : ι → List α) :
    (Finset.univ.filter fun c : Fin n → ι =>
      ∀ i, (((List.finRange n).filter (fun p => c p = i)).map w).reverse = E i).card = T (List.ofFn w).reverse E := by
  induction n generalizing E with
  | zero =>
    rw [Finset.card_filter, Fintype.sum_unique, List.ofFn_zero, List.reverse_nil, T_nil]
    simp only [List.finRange_zero, List.filter_nil, List.map_nil, List.reverse_nil]
    by_cases hE : ∀ i, E i = []
    · rw [if_pos hE, if_pos (fun i => (hE i).symm)]
    · rw [if_neg hE, if_neg (fun h' => hE fun i => (h' i).symm)]
  | succ n ih =>
    have hw : (List.ofFn w).reverse = w (Fin.last n) :: (List.ofFn fun i : Fin n => w i.castSucc).reverse := by
      rw [List.ofFn_succ', List.concat_eq_append, List.reverse_append, List.reverse_singleton,
        List.singleton_append]
    rw [hw, T_cons, Finset.card_filter]
    let e : ι × (Fin n → ι) ≃ (Fin (n + 1) → ι) :=
      { toFun := fun q => Fin.snoc (α := fun _ => ι) q.2 q.1
        invFun := fun c => (c (Fin.last n), Fin.init c)
        left_inv := fun q => by simp [Fin.init_snoc, Fin.snoc_last]
        right_inv := fun c => by simp [Fin.snoc_init_self] }
    rw [← e.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    have key : ∀ c' : Fin n → ι,
        (∀ j, (((List.finRange (n + 1)).filter (fun p => e (i, c') p = j)).map w).reverse = E j) ↔
        ((E i).head? = some (w (Fin.last n)) ∧
          ∀ j, (((List.finRange n).filter (fun p => c' p = j)).map (fun p => w p.castSucc)).reverse =
            Function.update E i (E i).tail j) := by
      intro c'
      refine Iff.trans ?_ (step_iff (fun j => (((List.finRange n).filter (fun p => c' p = j)).map
        (fun p => w p.castSucc)).reverse) E i (w (Fin.last n)))
      refine forall_congr' fun j => ?_
      rw [sub_last w (e (i, c')) j]
      simp only [e, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.snoc_last]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    rw [← ih (fun p => w p.castSucc) (Function.update E i (E i).tail), Finset.card_filter]
    by_cases hh : (E i).head? = some (w (Fin.last n))
    · rw [if_pos hh]
      refine Finset.sum_congr rfl fun c' _ => ?_
      by_cases hQ : ∀ j, (((List.finRange n).filter (fun p => c' p = j)).map (fun p => w p.castSucc)).reverse =
          Function.update E i (E i).tail j
      · rw [if_pos ((key c').2 ⟨hh, hQ⟩), if_pos hQ]
      · rw [if_neg (fun h' => hQ ((key c').1 h').2), if_neg hQ]
    · rw [if_neg hh]
      refine Finset.sum_eq_zero fun c' _ => ?_
      rw [if_neg (fun h' => hh ((key c').1 h').1)]

theorem shuffleCount_eq_T_reverse {h : ℕ} (W : List α) (D : Fin h → List α) :
    shuffleCount W D = T W.reverse fun i => (D i).reverse := by
  have hc := card_filter_reverse_map_eq_shuffle_count W.get (fun i => (D i).reverse)
  rw [List.ofFn_get] at hc
  delta shuffleCount Zc.Cos.sub
  rw [← hc]
  congr 1
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.reverse_inj]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ofFn_term_cons (Δ : Segment k) : ∃ B : List (IrrGL k), List.ofFn Δ.term = Δ.first :: B ∧
    B.length + 1 = Δ.len ∧ ∀ a ∈ B, ∃ n : ℕ, 0 < n ∧ a = Δ.first.nu (n : ℂ) := by
  have key : ∀ (m : ℕ) (f : Fin m → IrrGL k), 0 < m → (∀ a : Fin m, f a = Δ.first.nu ((a : ℕ) : ℂ)) →
      ∃ B : List (IrrGL k), List.ofFn f = Δ.first :: B ∧ B.length + 1 = m ∧
        ∀ a ∈ B, ∃ n : ℕ, 0 < n ∧ a = Δ.first.nu (n : ℂ) := by
    intro m f hm hf
    cases m with
    | zero => exact absurd hm (lt_irrefl 0)
    | succ m =>
      refine ⟨List.ofFn fun i : Fin m => f i.succ, ?_, by simp, ?_⟩
      · rw [List.ofFn_succ, hf 0]
        simp
      · intro a ha
        rw [List.mem_ofFn] at ha
        obtain ⟨i, rfl⟩ := ha
        exact ⟨(i.succ : ℕ), by simp, hf i.succ⟩
  exact key Δ.len Δ.term Δ.len_pos (fun a => rfl)

theorem T_step {h : ℕ} (Γ : Fin (h + 1) → Segment k) (hc : IsCanon Γ) (R : List (IrrGL k)) :
    T (List.ofFn (Γ (Fin.last h)).term ++ R) (fun i => List.ofFn (Γ i).term) =
      (Finset.univ.filter fun g => Γ g = Γ (Fin.last h)).card *
        T R (fun i : Fin h => List.ofFn (Γ i.castSucc).term) := by
  obtain ⟨hc1, -⟩ := hc
  obtain ⟨B', hB', hlen', hmem'⟩ := ofFn_term_cons (Γ (Fin.last h))
  have hlt : ∀ i, i ≠ Fin.last h → i < Fin.last h := fun i hi => lt_of_le_of_ne (Fin.le_last i) hi
  have hempty : ∀ g, Γ g = Γ (Fin.last h) →
      T R (Function.update (fun i => List.ofFn (Γ i).term) g []) =
        T R (fun i : Fin h => List.ofFn (Γ i.castSucc).term) := by
    intro g hg
    have hEg : List.ofFn (Γ g).term = List.ofFn (Γ (Fin.last h)).term := by rw [hg]
    have h1 : Function.update (fun i => List.ofFn (Γ i).term) g [] ∘ Equiv.swap g (Fin.last h) =
        Function.update (fun i => List.ofFn (Γ i).term) (Fin.last h) [] := by
      funext j
      rw [Function.comp_apply]
      by_cases hjl : j = Fin.last h
      · rw [hjl, Equiv.swap_apply_right, Function.update_self, Function.update_self]
      · by_cases hjg : j = g
        · rw [hjg] at hjl ⊢
          rw [Equiv.swap_apply_left, Function.update_of_ne (Ne.symm hjl), Function.update_of_ne hjl]
          exact hEg.symm
        · rw [Equiv.swap_apply_of_ne_of_ne hjg hjl, Function.update_of_ne hjg, Function.update_of_ne hjl]
    rw [← T_comp (Equiv.swap g (Fin.last h)) R, h1, T_last R _ (by simp)]
    congr 1
    funext i
    rw [Function.update_of_ne (Fin.castSucc_lt_last i).ne]
  rw [hB', List.cons_append, T_cons, Finset.card_eq_sum_ones, Finset.sum_mul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨Bi, hBi, hleni, -⟩ := ofFn_term_cons (Γ i)
  rw [hBi, List.head?_cons, List.tail_cons, one_mul]
  by_cases hf : (Γ i).first = (Γ (Fin.last h)).first
  · rw [if_pos (by rw [hf])]
    have H : ∀ j, j ≠ i → ∀ a ∈ B', ((Function.update (fun i => List.ofFn (Γ i).term) i Bi) j).head? ≠ some a := by
      intro j hj a ha heq
      rw [Function.update_of_ne hj] at heq
      obtain ⟨Bj, hBj, -, -⟩ := ofFn_term_cons (Γ j)
      simp only [hBj, List.head?_cons, Option.some.injEq] at heq
      obtain ⟨n, hn, rfl⟩ := hmem' a ha
      by_cases hjl : j = Fin.last h
      · have hil : i ≠ Fin.last h := fun e => hj (hjl.trans e.symm)
        rw [hjl] at heq
        exact (hc1 i (Fin.last h) (hlt i hil)).1 ⟨n, hn, hf.trans heq⟩
      · exact (hc1 j (Fin.last h) (hlt j hjl)).1 ⟨n, hn, heq⟩
    rw [T_block R B' _ i H, Function.update_self, Function.update_idem]
    by_cases hΓ : Γ i = Γ (Fin.last h)
    · have hBB : Bi = B' := by
        rw [hΓ] at hBi
        exact (List.cons.inj (hBi.symm.trans hB')).2
      rw [hBB, if_pos (show B' <+: B' from ⟨[], List.append_nil B'⟩), if_pos hΓ, List.drop_length]
      exact hempty i hΓ
    · rw [if_neg hΓ, if_neg]
      intro hp
      have hle := hp.length_le
      have hil : i ≠ Fin.last h := fun e => hΓ (by rw [e])
      have hle2 := (hc1 i (Fin.last h) (hlt i hil)).2 hf
      apply hΓ
      exact Segment.ext_first hf (by omega)
  · rw [if_neg (fun e => hf (Option.some.inj e)), if_neg (fun e => hf (by rw [e]))]

theorem canon_castSucc {h : ℕ} {Γ : Fin (h + 1) → Segment k} (hc : IsCanon Γ) :
    IsCanon fun i : Fin h => Γ i.castSucc := by
  obtain ⟨h1, h2⟩ := hc
  exact ⟨fun i j hij => h1 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij),
    fun i j l hij hjl => h2 _ _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij) (Fin.castSucc_lt_castSucc_iff.mpr hjl)⟩

theorem T_canon {h : ℕ} (Γ : Fin h → Segment k) (hc : IsCanon Γ) :
    T (List.ofFn fun i => decWord (Γ i)).flatten.reverse (fun i => List.ofFn (Γ i).term) =
      ∏ i, (Finset.univ.filter fun j => j ≤ i ∧ Γ j = Γ i).card := by
  have hd : ∀ Δ : Segment k, (decWord Δ).reverse = List.ofFn Δ.term := fun Δ =>
    List.reverse_reverse (List.ofFn Δ.term)
  induction h with
  | zero => simp [T_nil]
  | succ h ih =>
    have hw : (List.ofFn fun i => decWord (Γ i)).flatten.reverse =
        List.ofFn (Γ (Fin.last h)).term ++ (List.ofFn fun i : Fin h => decWord (Γ i.castSucc)).flatten.reverse := by
      simp only [List.ofFn_succ', List.concat_eq_append, List.flatten_append, List.reverse_append,
        List.flatten_cons, List.flatten_nil, List.append_nil, hd]
    rw [hw, T_step Γ hc, ih (fun i => Γ i.castSucc) (canon_castSucc hc), Fin.prod_univ_castSucc, mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      refine Finset.card_bij (fun a _ => a.castSucc) ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact ⟨Fin.castSucc_le_castSucc_iff.mpr ha.1, ha.2⟩
      · intro a _ b _ hab
        exact Fin.castSucc_injective _ hab
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have hbl : b ≠ Fin.last h := by
          intro e
          rw [e] at hb
          exact absurd hb.1 (not_le.mpr (Fin.castSucc_lt_last i))
        refine ⟨b.castPred hbl, ?_, Fin.castSucc_castPred b hbl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← Fin.castSucc_le_castSucc_iff, Fin.castSucc_castPred]
        exact hb
    · congr 1
      ext j
      simp [Fin.le_last]

theorem shuffleCount_canon {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {h : ℕ} (Γ : Fin h → Segment k) (hc : IsCanon Γ) :
    shuffleCount (List.ofFn fun i => decWord (Γ i)).flatten (fun i => decWord (Γ i)) =
      ∏ i, (Finset.univ.filter fun j : Fin h => j ≤ i ∧ Γ j = Γ i).card := by
  rw [shuffleCount_eq_T_reverse]
  have hD : (fun i => (decWord (Γ i)).reverse) = fun i => List.ofFn (Γ i).term := by
    funext i
    exact List.reverse_reverse (List.ofFn (Γ i).term)
  rw [hD]
  exact T_canon Γ hc

end GlobalTheory.CompanionTheory.WordCount
