import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEigenCoindMackeyDoubleCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoindEigenEqBotOfRootInUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoindEigenEqBotOfBlockCutCuspidalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoindEigenSortingPermEqLeviWhittakerStatement

noncomputable section

namespace GlobalTheory.FinGL.WhCutInd

open GlobalTheory.FinGL Formalism.L2.DIV Module

variable {F : Type} [Field F] {r : ℕ}

def pm (F : Type) [Field F] (w : Equiv.Perm (Fin r)) : GL (Fin r) F where
  val := Matrix.of fun a c => if a = w c then 1 else 0
  inv := Matrix.of fun a c => if c = w a then 1 else 0
  val_inv := by
    ext a c
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (w.symm a)]
    · simp [eq_comm]
    · intro l _ hl
      rw [if_neg, zero_mul]
      rintro rfl
      exact hl (by simp)
    · simp
  inv_val := by
    ext a c
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (w a)]
    · simp
    · intro l _ hl
      rw [if_neg hl, zero_mul]
    · simp

theorem pm_val (w : Equiv.Perm (Fin r)) (a c : Fin r) :
    (pm F w : Matrix (Fin r) (Fin r) F) a c = if a = w c then 1 else 0 := rfl

theorem pm_inv_val (w : Equiv.Perm (Fin r)) (a c : Fin r) :
    (((pm F w)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = if c = w a then 1 else 0 := rfl

theorem pm_conj (w' w : Equiv.Perm (Fin r)) (g : GL (Fin r) F) (a c : Fin r) :
    (((pm F w')⁻¹ * g * pm F w : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c =
      (g : Matrix (Fin r) (Fin r) F) (w' a) (w c) := by
  simp only [Units.val_mul, Matrix.mul_apply, pm_val, pm_inv_val]
  simp

theorem pm_mul_inv_mem {b : Fin r → ℕ} {w w' : Equiv.Perm (Fin r)} (h : ∀ c, b (w c) = b (w' c)) :
    pm F w * (pm F w')⁻¹ ∈ blockTri (κ := F) b := by
  rw [mem_blockTri]
  intro i k hik
  simp only [Units.val_mul, Matrix.mul_apply, pm_val, pm_inv_val]
  refine Finset.sum_eq_zero fun c _ => ?_
  split_ifs with h1 h2
  · subst h1 h2
    exact absurd (h c) hik.ne'
  all_goals simp

theorem unip_le {b : Fin r → ℕ} (hb : Monotone b) : unip F r ≤ blockTri (κ := F) b := by
  intro u hu
  rw [mem_blockTri]
  intro i k hik
  exact unip_lower hu (hb.reflect_lt hik)

theorem exists_pm {b : Fin r → ℕ} (hb : Monotone b) (g : GL (Fin r) F) :
    ∃ w : Equiv.Perm (Fin r), ∃ p ∈ blockTri (κ := F) b, ∃ u ∈ unip F r, g = p * pm F w * u := by
  obtain ⟨⟨w, t⟩, ⟨u, hu, u', hu', e⟩, -⟩ := GlobalTheory.FinGL.Bruhat.bruhat F r g
  refine ⟨w, u * (u⁻¹ * g * u'⁻¹ * (pm F w)⁻¹), Subgroup.mul_mem _ (unip_le hb hu) ?_, u', hu', by group⟩
  have e1 : ((u⁻¹ * g * u'⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      Matrix.of fun a c => if a = w c then (t c : F) else 0 := by
    rw [Units.val_mul, Units.val_mul, e]
    simp only [← Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [mem_blockTri]
  intro i k hik
  rw [Units.val_mul, e1]
  simp only [Matrix.mul_apply, pm_inv_val, Matrix.of_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  split_ifs with h1 h2
  · subst h1 h2
    exact absurd hik (lt_irrefl _)
  all_goals simp

theorem blk_eq_of_rel {b : Fin r → ℕ} {w w' : Equiv.Perm (Fin r)} {p u : GL (Fin r) F} (hp : p ∈ blockTri (κ := F) b)
    (hu : u ∈ unip F r) (e : p * pm F w = pm F w' * u) (c : Fin r) : b (w' c) = b (w c) := by
  have h1 : ∀ c, b (w' c) ≤ b (w c) := fun c => by
    by_contra hlt
    have h2 := pm_conj w' w p c c
    rw [mul_assoc, e, inv_mul_cancel_left, unip_diag hu, mem_blockTri.1 hp _ _ (not_le.1 hlt)] at h2
    exact one_ne_zero h2
  have h2 : ∑ c, b (w' c) = ∑ c, b (w c) := by
    rw [Equiv.sum_comp w' b, Equiv.sum_comp w b]
  exact (Finset.sum_eq_sum_iff_of_le fun c _ => h1 c).1 h2 c (Finset.mem_univ c)

def key (b : Fin r → ℕ) (J : Finset ℕ) (i : Fin r) : ℕ ×ₗ ℕᵒᵈ :=
  toLex (if b i ∈ J then 0 else 1, OrderDual.toDual (b i))

theorem key_le_iff (b : Fin r → ℕ) (J : Finset ℕ) (i k : Fin r) :
    key b J i ≤ key b J k ↔ (b i ∈ J ∧ b k ∉ J) ∨ ((b i ∈ J ↔ b k ∈ J) ∧ b k ≤ b i) := by
  unfold key
  rw [Prod.Lex.toLex_le_toLex]
  by_cases h1 : b i ∈ J <;> by_cases h2 : b k ∈ J <;> simp [h1, h2]

theorem key_eq_iff (b : Fin r → ℕ) (J : Finset ℕ) (i k : Fin r) : key b J i = key b J k ↔ b i = b k := by
  constructor
  · intro h
    exact congrArg (fun z => OrderDual.ofDual (ofLex z).2) h
  · intro h
    unfold key
    rw [h]

theorem sort_mem_iff (b : Fin r → ℕ) (J : Finset ℕ) (a : Fin r) :
    b (Tuple.sort (key b J) a) ∈ J ↔ a.val < (Finset.univ.filter fun i => b i ∈ J).card := by
  set w := Tuple.sort (key b J)
  have hm : Monotone fun a => if b (w a) ∈ J then 0 else 1 := fun a c hac => by
    have := (key_le_iff b J _ _).1 (Tuple.monotone_sort (key b J) hac)
    dsimp only
    split_ifs with h1 h2 h2 <;> first | omega | tauto
  have h := Tuple.lt_card_le_iff_apply_le_of_monotone (a := 0) (j := a) hm
  have hc : (Finset.univ.filter fun i => (if b (w i) ∈ J then 0 else 1) ≤ 0).card =
      (Finset.univ.filter fun i => b i ∈ J).card := by
    refine Finset.card_equiv w fun i => ?_
    by_cases h1 : b (w i) ∈ J <;> simp [h1]
  rw [hc] at h
  rw [h]
  by_cases h1 : b (w a) ∈ J <;> simp [h1]

theorem monotone_of_succ {α : Type} [Preorder α] (f : Fin r → α) (h : ∀ a c : Fin r, c.val = a.val + 1 → f a ≤ f c) :
    Monotone f := by
  cases r with
  | zero => intro a; exact a.elim0
  | succ n => exact Fin.monotone_iff_le_succ.2 fun i => h _ _ (by simp)

theorem exists_set (b : Fin r → ℕ) {j : ℕ} (hj : j ≤ r) (w : Equiv.Perm (Fin r))
    (h1 : ∀ a c : Fin r, cutEdge j a c → b (w c) ≤ b (w a))
    (h2 : ∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) ≠ b (w c)) :
    ∃ J ∈ (Finset.univ.image b).powerset.filter fun J => (Finset.univ.filter fun i => b i ∈ J).card = j,
      ∀ c, b (w c) = b (Tuple.sort (key b J) c) := by
  set J : Finset ℕ := (Finset.univ.filter fun a : Fin r => a.val < j).image fun a => b (w a) with hJ
  have hmem : ∀ c, b (w c) ∈ J ↔ c.val < j := fun c => by
    simp only [hJ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, e⟩
      by_contra hc
      exact h2 a c ha (not_lt.1 hc) e
    · exact fun hc => ⟨c, hc, rfl⟩
  refine ⟨J, ?_, fun c => ?_⟩
  · rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro z hz
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hz
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · have : (Finset.univ.filter fun a : Fin r => a.val < j).card = (Finset.univ.filter fun i => b i ∈ J).card :=
        Finset.card_equiv w fun i => by simp [hmem]
      rw [← this, Fin.card_filter_val_lt]
      omega
  · have hm : Monotone (key b J ∘ w) := monotone_of_succ _ fun a c hac => by
      show key b J (w a) ≤ key b J (w c)
      rw [key_le_iff, hmem, hmem]
      by_cases h : a.val + 1 = j
      · left; omega
      · right; exact ⟨by omega, h1 a c ⟨hac, h⟩⟩
    exact (key_eq_iff b J _ _).1 (congrFun (Tuple.unique_monotone hm (Tuple.monotone_sort (key b J))) c)

theorem edgeSum_cut_mul (j : ℕ) {u u' : GL (Fin r) F} (hu : u ∈ unip F r) (hu' : u' ∈ unip F r) :
    edgeSum (cutEdge j) (u * u') = edgeSum (cutEdge j) u + edgeSum (cutEdge j) u' := by
  unfold edgeSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with h
  · have h' := h.1
    refine unip_mul_entry hu hu' (show a.val < c.val by omega) fun l h1 h2 => ?_
    have h1' : a.val < l.val := h1
    have h2' : l.val < c.val := h2
    omega
  · rw [add_zero]

theorem edgeSum_cut_one (j : ℕ) : edgeSum (cutEdge j) (1 : GL (Fin r) F) = 0 := by
  have := edgeSum_cut_mul (F := F) (r := r) j (Subgroup.one_mem _) (Subgroup.one_mem _)
  rw [mul_one] at this
  exact left_eq_add.1 this

theorem degenerateWhittakerDim_parabolicInduction (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (r : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V)
    (hσ : IsCuspDatum b σ) (j : ℕ) (hj : j < r ∨ j = 0) : whCut ψ (parInd b σ) j = splitDoublingNBlock b j * leviWh ψ b σ := by
  have hj' : j ≤ r := by omega
  set T := (Finset.univ.image b).powerset.filter fun J => (Finset.univ.filter fun i => b i ∈ J).card = j with hT
  have hmem : ∀ J : T, ∀ a, b (Tuple.sort (key b J.1) a) ∈ J.1 ↔ a.val < j := fun J a => by
    rw [sort_mem_iff, (Finset.mem_filter.1 J.2).2]
  have hsub : ∀ J J' : T, (∀ c, b (Tuple.sort (key b J.1) c) = b (Tuple.sort (key b J'.1) c)) → J.1 ⊆ J'.1 := by
    intro J J' h z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_powerset.1 (Finset.mem_filter.1 J.2).1 hz)
    obtain ⟨a, rfl⟩ := (Tuple.sort (key b J.1)).surjective i
    rw [h, hmem, ← hmem J]
    exact hz
  unfold whCut
  rw [GlobalTheory.T.finrank_eigen_coind_mackey_double_cosets (GL (Fin r) F) (blockTri b) (unip F r) V σ (fun g => ψ (edgeSum (cutEdge j) g))
    (by simp only [edgeSum_cut_one, AddChar.map_zero_eq_one])
    (fun u hu u' hu' => by simp only [edgeSum_cut_mul j hu hu', AddChar.map_add_eq_mul])
    T (fun J => pm F (Tuple.sort (key b J.1)))
    (fun J J' p hp u hu e => Subtype.ext (Finset.Subset.antisymm
      (hsub J J' fun c => (blk_eq_of_rel hp hu e c).symm) (hsub J' J (blk_eq_of_rel hp hu e)))) ?_]
  · rw [Finset.sum_congr rfl (g := fun _ => leviWh ψ b σ) fun J _ => ?_]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
      rfl
    · have hs := (Tuple.eq_sort_iff (f := key b J.1)).1 rfl
      unfold leviWh
      rw [GlobalTheory.T.coindEigen_sorting_perm_eq_levi_whittaker F ψ r V b σ hσ j (Tuple.sort (key b J.1)) _ (pm_conj _ _)]
      · exact fun a c hac e => hs.2 a c hac ((key_eq_iff b J.1 _ _).2 e)
      · intro a e c h1 h2 h3
        have h4 : key b J.1 _ ≤ key b J.1 _ := hs.1 h1
        have h5 : key b J.1 _ ≤ key b J.1 _ := hs.1 h2
        rw [← (key_eq_iff b J.1 _ _).2 h3] at h5
        exact (key_eq_iff b J.1 _ _).1 (le_antisymm h5 h4)
      · intro a c hac
        have h1 := hac.1
        have h2 := hac.2
        have h4 : key b J.1 _ ≤ key b J.1 _ := hs.1 (show a ≤ c from show a.val ≤ c.val by omega)
        rw [key_le_iff, hmem, hmem] at h4
        rcases h4 with h4 | h4
        · omega
        · exact h4.2
      · intro a c ha hc e
        have := (hmem J a).2 ha
        rw [e, hmem] at this
        omega
  · intro g
    obtain ⟨w, p, hp, u, hu, e⟩ := exists_pm hσ.mono g
    by_cases h1 : ∀ a c : Fin r, cutEdge j a c → b (w c) ≤ b (w a)
    · by_cases h2 : ∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) ≠ b (w c)
      · obtain ⟨J, hJ, h⟩ := exists_set b hj' w h1 h2
        refine Or.inl ⟨⟨J, hJ⟩, p * (pm F w * (pm F (Tuple.sort (key b J)))⁻¹),
          Subgroup.mul_mem _ hp (pm_mul_inv_mem h), u, hu, ?_⟩
        rw [e]
        group
      · push Not at h2
        obtain ⟨a, c, ha, hc, h⟩ := h2
        exact Or.inr ⟨pm F w, ⟨p, hp, u, hu, e⟩, GlobalTheory.T.coindEigen_eq_bot_of_block_cut_cuspidal F ψ r V b σ hσ j w _ (pm_conj _ _) a c ha hc h⟩
    · push Not at h1
      obtain ⟨a, c, hac, h⟩ := h1
      exact Or.inr ⟨pm F w, ⟨p, hp, u, hu, e⟩, GlobalTheory.T.coindEigen_eq_bot_of_root_in_unipotent_radical F ψ r V b σ hσ j w _ (pm_conj _ _) hψ a c hac h⟩

end GlobalTheory.FinGL.WhCutInd
