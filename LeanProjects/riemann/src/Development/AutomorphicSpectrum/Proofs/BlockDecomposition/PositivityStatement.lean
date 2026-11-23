import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif

noncomputable section

set_option linter.unusedSectionVars false

open Matrix

namespace GlobalTheory.CompanionTheory.Jp.Pos

variable {k : Type} [Field k] [Fintype k] {n : ℕ}

def hC (ψ₀ : AddChar k ℂ) (β : Matrix (Fin n) (Fin n) k) (a : ℕ) (g : GL (Ix n) k) : ℂ :=
  ∑ Y : Matrix (Fin n) (Fin n) k,
    (starRingEnd ℂ) (ψ₀ (Matrix.trace (Y * β))) * (Fintype.card k : ℂ) ^ (a * iD (g * nU Y))

def wM : GL (Ix n) k where
  val := fromBlocks 0 1 1 0
  inv := fromBlocks 0 1 1 0
  val_inv := by simp [fromBlocks_multiply, ← fromBlocks_one]
  inv_val := by simp [fromBlocks_multiply, ← fromBlocks_one]

abbrev sV (V W : Submodule k (Fin n → k)) (Y : Matrix (Fin n) (Fin n) k) : Type :=
  {c : Fin n → k // c ∈ V ∧ c ᵥ* Y ∈ W}

theorem nU_mul_nU (Y' Y : Matrix (Fin n) (Fin n) k) : (nU Y' * nU Y : GL (Ix n) k) = nU (Y' + Y) := by
  apply Units.ext
  simp [nU, fromBlocks_multiply, add_comm]

theorem lowerRightBlock_mul_unipotent (g : GL (Ix n) k) (Y : Matrix (Fin n) (Fin n) k) :
    dBlk (g * nU Y) = dBlk g + lowerLeftBlock g * Y := by
  have key : ∀ A B C D : Matrix (Fin n) (Fin n) k,
      (fromBlocks A B C D * fromBlocks 1 Y 0 1).toBlocks₂₂ = D + C * Y := by
    intro A B C D
    simp [fromBlocks_multiply, add_comm]
  have := key g.1.toBlocks₁₁ g.1.toBlocks₁₂ g.1.toBlocks₂₁ g.1.toBlocks₂₂
  rw [fromBlocks_toBlocks] at this
  exact this

theorem lowerLeftBlock_mul_unipotent (g : GL (Ix n) k) (Y : Matrix (Fin n) (Fin n) k) :
    lowerLeftBlock (g * nU Y) = lowerLeftBlock g := by
  have key : ∀ A B C D : Matrix (Fin n) (Fin n) k,
      (fromBlocks A B C D * fromBlocks 1 Y 0 1).toBlocks₂₁ = C := by
    intro A B C D
    simp [fromBlocks_multiply]
  have := key g.1.toBlocks₁₁ g.1.toBlocks₁₂ g.1.toBlocks₂₁ g.1.toBlocks₂₂
  rw [fromBlocks_toBlocks] at this
  exact this

theorem lower_rows_indep (g : GL (Ix n) k) (x : Fin n → k) (hC' : x ᵥ* lowerLeftBlock g = 0) (hD : x ᵥ* dBlk g = 0) : x = 0 := by
  have hv : (Sum.elim 0 x : Ix n → k) ᵥ* g.1 = 0 := by
    funext j
    rcases j with j | j
    · have := congrFun hC' j
      simpa [vecMul, dotProduct, Fintype.sum_sum_type, lowerLeftBlock, toBlocks₂₁] using this
    · have := congrFun hD j
      simpa [vecMul, dotProduct, Fintype.sum_sum_type, dBlk, toBlocks₂₂] using this
  have h0 : (Sum.elim 0 x : Ix n → k) = 0 := by
    have h1 : (g.1 * (g⁻¹).1 : Matrix (Ix n) (Ix n) k) = 1 := by
      rw [← Units.val_mul]; simp
    calc (Sum.elim 0 x : Ix n → k) = (Sum.elim 0 x : Ix n → k) ᵥ* (g.1 * (g⁻¹).1) := by rw [h1, vecMul_one]
      _ = 0 := by rw [← vecMul_vecMul, hv, zero_vecMul]
  funext i
  simpa using congrFun h0 (Sum.inr i)

theorem hC_shift (ψ₀ : AddChar k ℂ) (β : Matrix (Fin n) (Fin n) k) (a : ℕ) (g : GL (Ix n) k)
    (Y' : Matrix (Fin n) (Fin n) k) :
    hC ψ₀ β a (g * nU Y') = ψ₀ (Matrix.trace (Y' * β)) * hC ψ₀ β a g := by
  unfold hC
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft Y') _ _ fun Y => ?_
  rw [Equiv.coe_addLeft, mul_assoc g, nU_mul_nU, ← mul_assoc]
  congr 1
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  congr 1
  rw [add_mul, Matrix.trace_add]
  ring

theorem card_lker (M : Matrix (Fin n) (Fin n) k) :
    Fintype.card k ^ (n - M.rank) = Nat.card {x : Fin n → k // x ᵥ* M = 0} := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Mᵀ.mulVecLin)
  have h2 : Module.finrank k (LinearMap.range Mᵀ.mulVecLin) = M.rank := by
    rw [← Matrix.rank_transpose M]; rfl
  rw [h2, Module.finrank_fin_fun] at h1
  have h3 : n - M.rank = Module.finrank k (LinearMap.ker Mᵀ.mulVecLin) := by omega
  have h4 := Module.natCard_eq_pow_finrank (K := k) (V := LinearMap.ker Mᵀ.mulVecLin)
  rw [h3, ← Nat.card_eq_fintype_card, ← h4]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  simp [LinearMap.mem_ker, Matrix.mulVec_transpose]

theorem count_sV (C D : Matrix (Fin n) (Fin n) k)
    (h : ∀ x : Fin n → k, x ᵥ* C = 0 → x ᵥ* D = 0 → x = 0)
    (hs : ∀ x₁ x₂ : Fin n → k, ∃ x : Fin n → k, x ᵥ* C = x₁ ᵥ* C ∧ x ᵥ* D = x₂ ᵥ* D)
    (Y : Matrix (Fin n) (Fin n) k) :
    Fintype.card k ^ (n - (D + C * Y).rank) =
      Nat.card (sV (LinearMap.range C.vecMulLinear) (LinearMap.range D.vecMulLinear) Y) := by
  rw [card_lker]
  have hx : ∀ x : Fin n → k, x ᵥ* (D + C * Y) = x ᵥ* D + (x ᵥ* C) ᵥ* Y := by
    intro x; rw [vecMul_add, vecMul_vecMul]
  refine Nat.card_eq_of_bijective
    (fun x => ⟨x.1 ᵥ* C, ⟨x.1, rfl⟩, ⟨-x.1, ?_⟩⟩) ⟨?_, ?_⟩
  · have := hx x.1
    rw [x.2] at this
    simp only [Matrix.vecMulLinear_apply, neg_vecMul]
    exact (neg_eq_of_add_eq_zero_right this.symm)
  · rintro ⟨x, hx0⟩ ⟨y, hy0⟩ hxy
    have hc : x ᵥ* C = y ᵥ* C := congrArg Subtype.val hxy
    have e1 := hx x
    have e2 := hx y
    rw [hx0] at e1
    rw [hy0] at e2
    have hd : x ᵥ* D = y ᵥ* D := by
      rw [hc] at e1
      have := e1.symm.trans e2
      exact add_right_cancel this
    have : x - y = 0 := h _ (by rw [sub_vecMul, hc, sub_self]) (by rw [sub_vecMul, hd, sub_self])
    exact Subtype.ext (sub_eq_zero.mp this)
  · rintro ⟨c, ⟨x₁, rfl⟩, ⟨x₂, hx₂⟩⟩
    obtain ⟨x, h1, h2⟩ := hs x₁ (-x₂)
    simp only [Matrix.vecMulLinear_apply] at hx₂ ⊢
    refine ⟨⟨x, ?_⟩, Subtype.ext h1⟩
    rw [hx, h1, h2, neg_vecMul, hx₂]
    simp

theorem split_exists (C D : Matrix (Fin n) (Fin n) k) :
    ∃ Y₀ : Matrix (Fin n) (Fin n) k, ∀ x₁ x₂ : Fin n → k, ∃ x : Fin n → k,
      x ᵥ* C = x₁ ᵥ* C ∧ x ᵥ* (D + C * Y₀) = x₂ ᵥ* (D + C * Y₀) := by
  obtain ⟨E', hE⟩ := Submodule.exists_isCompl (LinearMap.ker C.vecMulLinear)
  have hinj : LinearMap.ker (C.vecMulLinear.domRestrict E') = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro e he
    have : (e : Fin n → k) ∈ LinearMap.ker C.vecMulLinear := by
      simpa [LinearMap.mem_ker] using he
    exact Subtype.ext ((Submodule.disjoint_def.mp hE.disjoint) _ this e.2)
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  let Φ : (Fin n → k) →ₗ[k] (Fin n → k) := -(D.vecMulLinear ∘ₗ E'.subtype ∘ₗ ρ)
  refine ⟨(LinearMap.toMatrix' Φ)ᵀ, ?_⟩
  set Y₀ := (LinearMap.toMatrix' Φ)ᵀ with hY₀
  have hv : ∀ c : Fin n → k, c ᵥ* Y₀ = Φ c := by
    intro c
    rw [hY₀, vecMul_transpose, LinearMap.toMatrix'_mulVec]
  have hk : ∀ e ∈ E', e ᵥ* (D + C * Y₀) = 0 := by
    intro e he
    have hρe : ρ (e ᵥ* C) = ⟨e, he⟩ := by
      have := LinearMap.congr_fun hρ ⟨e, he⟩
      simpa using this
    rw [vecMul_add, ← vecMul_vecMul, hv]
    simp [Φ, hρe]
  have hdec : ∀ x : Fin n → k, ∃ y ∈ LinearMap.ker C.vecMulLinear, ∃ z ∈ E', y + z = x := by
    intro x
    have : x ∈ LinearMap.ker C.vecMulLinear ⊔ E' := by rw [hE.sup_eq_top]; trivial
    exact Submodule.mem_sup.mp this
  intro x₁ x₂
  obtain ⟨e₁, he₁, f₁, hf₁, rfl⟩ := hdec x₁
  obtain ⟨e₂, he₂, f₂, hf₂, rfl⟩ := hdec x₂
  have hc₁ : e₁ ᵥ* C = 0 := by simpa [LinearMap.mem_ker] using he₁
  have hc₂ : e₂ ᵥ* C = 0 := by simpa [LinearMap.mem_ker] using he₂
  refine ⟨f₁ + e₂, ?_, ?_⟩
  · rw [add_vecMul, add_vecMul, hc₁, hc₂]; simp
  · rw [add_vecMul, add_vecMul, hk _ hf₁, hk _ hf₂]; simp

theorem iD_card_sub (g : GL (Ix n) k) :
    ∃ Y₀ : Matrix (Fin n) (Fin n) k, ∃ V W : Submodule k (Fin n → k), ∀ Y : Matrix (Fin n) (Fin n) k,
      Fintype.card k ^ iD (g * nU Y₀ * nU Y) = Nat.card (sV V W Y) := by
  obtain ⟨Y₀, hY⟩ := split_exists (lowerLeftBlock g) (dBlk g)
  refine ⟨Y₀, LinearMap.range (lowerLeftBlock (g * nU Y₀)).vecMulLinear, LinearMap.range (dBlk (g * nU Y₀)).vecMulLinear, fun Y => ?_⟩
  rw [← count_sV _ _ (lower_rows_indep _)]
  · unfold iD
    rw [lowerRightBlock_mul_unipotent]
  · rw [lowerLeftBlock_mul_unipotent, lowerRightBlock_mul_unipotent]
    exact hY

theorem iD_card_wM (Y : Matrix (Fin n) (Fin n) k) :
    Fintype.card k ^ iD ((wM : GL (Ix n) k) * nU Y) = Nat.card (sV (⊤ : Submodule k (Fin n → k)) ⊥ Y) := by
  have hc : lowerLeftBlock (wM : GL (Ix n) k) = 1 := by simp [lowerLeftBlock, wM]
  have hd : dBlk (wM : GL (Ix n) k) = 0 := by simp [dBlk, wM]
  have h1 : LinearMap.range (1 : Matrix (Fin n) (Fin n) k).vecMulLinear = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact fun x => ⟨x, by simp⟩
  have h0 : LinearMap.range (0 : Matrix (Fin n) (Fin n) k).vecMulLinear = ⊥ := by
    rw [LinearMap.range_eq_bot]
    ext x
    simp
  have := count_sV (1 : Matrix (Fin n) (Fin n) k) 0 (fun x h _ => by simpa using h)
    (fun x₁ x₂ => ⟨x₁, rfl, by simp⟩) Y
  rw [h1, h0] at this
  rw [← this]
  unfold iD
  rw [lowerRightBlock_mul_unipotent, hc, hd]

theorem sum_subgroup {G : Type} [AddCommGroup G] [Fintype G] (φ : G → ℂ) (hφ : ∀ x y, φ (x + y) = φ x * φ y)
    (h0 : φ 0 = 1) (Z : AddSubgroup G) [DecidablePred (· ∈ Z)] :
    ∃ t : ℝ, 0 ≤ t ∧ (∑ Y, if Y ∈ Z then φ Y else 0) = t ∧ ((∀ Y ∈ Z, φ Y = 1) → 0 < t) := by
  by_cases h : ∀ Y ∈ Z, φ Y = 1
  · refine ⟨((Finset.univ.filter (· ∈ Z)).card : ℝ), by positivity, ?_, fun _ => ?_⟩
    · rw [← Finset.sum_filter, Finset.sum_congr rfl (g := fun _ => (1 : ℂ))
        (fun Y hY => h Y (Finset.mem_filter.mp hY).2)]
      simp
    · exact_mod_cast Finset.card_pos.mpr ⟨0, by simp [Z.zero_mem]⟩
  · push_neg at h
    obtain ⟨y, hy, hy1⟩ := h
    refine ⟨0, le_rfl, ?_, fun h' => absurd (h' y hy) hy1⟩
    set S := ∑ Y, if Y ∈ Z then φ Y else 0 with hS
    have : S = φ y * S := by
      rw [hS, Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.addLeft (-y)) _ _ fun Y => ?_
      have hm : (-y + Y ∈ Z) ↔ Y ∈ Z := by
        rw [AddSubgroup.add_mem_cancel_left Z (Z.neg_mem hy)]
      simp only [Equiv.coe_addLeft, hm]
      split_ifs
      · rw [← hφ]; simp
      · simp
    have h2 : (1 - φ y) * S = 0 := by linear_combination this
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3).symm hy1
    · simpa using h3

theorem card_pow_sV (V W : Submodule k (Fin n → k)) (a : ℕ) (Y : Matrix (Fin n) (Fin n) k)
    [∀ (c : Fin a → Fin n → k), Decidable (∀ i, c i ∈ V ∧ c i ᵥ* Y ∈ W)] :
    (Nat.card (sV V W Y) : ℂ) ^ a =
      ∑ c : Fin a → Fin n → k, if ∀ i, c i ∈ V ∧ c i ᵥ* Y ∈ W then 1 else 0 := by
  have h1 : Nat.card (sV V W Y) ^ a = Nat.card (Fin a → sV V W Y) := by simp [Nat.card_fun]
  have h2 : Nat.card (Fin a → sV V W Y) = Nat.card {c : Fin a → Fin n → k // ∀ i, c i ∈ V ∧ c i ᵥ* Y ∈ W} :=
    Nat.card_congr (Equiv.subtypePiEquivPi).symm
  rw [← Nat.cast_pow, h1, h2, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

theorem fourier_nonneg (ψ₀ : AddChar k ℂ) (β : Matrix (Fin n) (Fin n) k) (V W : Submodule k (Fin n → k)) (a : ℕ) :
    ∃ x : ℝ, 0 ≤ x ∧
      (∑ Y : Matrix (Fin n) (Fin n) k, (starRingEnd ℂ) (ψ₀ (Matrix.trace (Y * β))) * (Nat.card (sV V W Y) : ℂ) ^ a) = x ∧
      ((∃ c : Fin a → Fin n → k, (∀ i, c i ∈ V) ∧
        ∀ Y : Matrix (Fin n) (Fin n) k, (∀ i, c i ᵥ* Y ∈ W) → Matrix.trace (Y * β) = 0) → 0 < x) := by
  classical
  set φ : Matrix (Fin n) (Fin n) k → ℂ := fun Y => (starRingEnd ℂ) (ψ₀ (Matrix.trace (Y * β))) with hφdef
  have hφ : ∀ x y, φ (x + y) = φ x * φ y := by
    intro x y
    simp only [hφdef, add_mul, Matrix.trace_add, AddChar.map_add_eq_mul, map_mul]
  have h0 : φ 0 = 1 := by simp [hφdef]
  have hc : ∀ c : Fin a → Fin n → k, ∃ t : ℝ, 0 ≤ t ∧
      (∑ Y : Matrix (Fin n) (Fin n) k, if ∀ i, c i ∈ V ∧ c i ᵥ* Y ∈ W then φ Y else 0) = t ∧
      ((∀ i, c i ∈ V) → (∀ Y : Matrix (Fin n) (Fin n) k, (∀ i, c i ᵥ* Y ∈ W) → Matrix.trace (Y * β) = 0) → 0 < t) := by
    intro c
    by_cases hV : ∀ i, c i ∈ V
    · let Z : AddSubgroup (Matrix (Fin n) (Fin n) k) :=
        { carrier := {Y | ∀ i, c i ᵥ* Y ∈ W}
          add_mem' := fun {x y} hx hy i => by rw [vecMul_add]; exact W.add_mem (hx i) (hy i)
          zero_mem' := fun i => by simp
          neg_mem' := fun {x} hx i => by rw [vecMul_neg]; exact W.neg_mem (hx i) }
      obtain ⟨t, ht, e, hp⟩ := sum_subgroup φ hφ h0 Z
      refine ⟨t, ht, ?_, fun _ hz => hp fun Y hY => ?_⟩
      · rw [← e]
        refine Finset.sum_congr rfl fun Y _ => ?_
        have : (∀ i, c i ∈ V ∧ c i ᵥ* Y ∈ W) ↔ Y ∈ Z :=
          ⟨fun h i => (h i).2, fun h i => ⟨hV i, h i⟩⟩
        simp only [this]
      · simp [hφdef, hz Y hY]
    · refine ⟨0, le_rfl, ?_, fun h => absurd h hV⟩
      push_neg at hV
      obtain ⟨i, hi⟩ := hV
      have : ∀ Y : Matrix (Fin n) (Fin n) k, ¬ ∀ i, c i ∈ V ∧ c i ᵥ* Y ∈ W := fun Y h => hi (h i).1
      simp [this]
  choose t ht0 ht hpos using hc
  refine ⟨∑ c, t c, Finset.sum_nonneg fun c _ => ht0 c, ?_, ?_⟩
  · have : ∀ Y : Matrix (Fin n) (Fin n) k, φ Y * (Nat.card (sV V W Y) : ℂ) ^ a =
        ∑ c : Fin a → Fin n → k, if ∀ i, c i ∈ V ∧ c i ᵥ* Y ∈ W then φ Y else 0 := by
      intro Y
      rw [card_pow_sV, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun Y _ => this Y, Finset.sum_comm]
    push_cast
    exact Finset.sum_congr rfl fun c _ => ht c
  · rintro ⟨c, hV, hz⟩
    exact Finset.sum_pos' (fun c _ => ht0 c) ⟨c, Finset.mem_univ _, hpos c hV hz⟩

theorem exists_rows (β : Matrix (Fin n) (Fin n) k) (a : ℕ) (h : β.rank ≤ a) :
    ∃ c : Fin a → Fin n → k, ∀ Y : Matrix (Fin n) (Fin n) k, (∀ i, c i ᵥ* Y = 0) → Matrix.trace (Y * β) = 0 := by
  obtain ⟨f, -, hf, -⟩ := Submodule.exists_fun_fin_finrank_span_eq k (Set.range β.row)
  have hd : Module.finrank k (Submodule.span k (Set.range β.row)) ≤ a := by
    rw [← Matrix.rank_eq_finrank_span_row]; exact h
  refine ⟨fun i => if h' : i.1 < Module.finrank k (Submodule.span k (Set.range β.row)) then f ⟨i.1, h'⟩ else 0,
    fun Y hY => ?_⟩
  have hle : Submodule.span k (Set.range f) ≤ LinearMap.ker Y.vecMulLinear := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have := hY ⟨i.1, i.2.trans_le hd⟩
    simpa [LinearMap.mem_ker] using this
  have hrow : ∀ j, β j ᵥ* Y = 0 := by
    intro j
    have h1 : β j ∈ Submodule.span k (Set.range f) := by
      rw [hf]; exact Submodule.subset_span ⟨j, rfl⟩
    simpa [LinearMap.mem_ker] using hle h1
  rw [Matrix.trace_mul_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp [Matrix.diag, Matrix.mul_apply_eq_vecMul, hrow j]

theorem sum_eq (ψ₀ : AddChar k ℂ) (β : Matrix (Fin n) (Fin n) k) (r m : ℕ) :
    sumG (fun g : GL (Ix n) k => ∑ Y : Matrix (Fin n) (Fin n) k,
        (Fintype.card k : ℂ) ^ (r * iD g) * coY ψ₀ β Y * (Fintype.card k : ℂ) ^ (m * iD (g * nU Y))) =
      ((Fintype.card k : ℂ) ^ (n * n))⁻¹ ^ 2 *
        sumG (fun g : GL (Ix n) k => (starRingEnd ℂ) (hC ψ₀ β r g) * hC ψ₀ β m g) := by
  classical
  haveI : Fintype (GL (Ix n) k) := Fintype.ofFinite _
  set q : ℂ := (Fintype.card k : ℂ) with hq
  have hq0 : q ^ (n * n) ≠ 0 := pow_ne_zero _ (by
    rw [hq]; exact_mod_cast Fintype.card_ne_zero)
  unfold sumG
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  set T : ℂ := ∑ g : GL (Ix n) k, q ^ (r * iD g) * hC ψ₀ β m g with hT
  have h1 : (∑ g : GL (Ix n) k, ∑ Y : Matrix (Fin n) (Fin n) k,
      q ^ (r * iD g) * coY ψ₀ β Y * q ^ (m * iD (g * nU Y))) = (q ^ (n * n))⁻¹ * T := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold hC coY
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Y _ => ?_
    simp only [← hq]
    ring
  have h2 : ∀ Y' : Matrix (Fin n) (Fin n) k, T =
      ∑ g : GL (Ix n) k, q ^ (r * iD (g * nU Y')) * (ψ₀ (Matrix.trace (Y' * β)) * hC ψ₀ β m g) := by
    intro Y'
    rw [hT]
    refine (Fintype.sum_equiv (Equiv.mulRight (nU Y')) _ _ fun g => ?_).symm
    rw [Equiv.coe_mulRight, hC_shift]
  have hcard : (Fintype.card (Matrix (Fin n) (Fin n) k) : ℂ) = q ^ (n * n) := by
    have : Fintype.card (Matrix (Fin n) (Fin n) k) = Fintype.card k ^ (n * n) := by
      show Fintype.card (Fin n → Fin n → k) = _
      simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    rw [this]; push_cast; rfl
  have h3 : q ^ (n * n) * T = ∑ g : GL (Ix n) k, (starRingEnd ℂ) (hC ψ₀ β r g) * hC ψ₀ β m g := by
    calc q ^ (n * n) * T = ∑ _Y' : Matrix (Fin n) (Fin n) k, T := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      _ = ∑ Y' : Matrix (Fin n) (Fin n) k, ∑ g : GL (Ix n) k,
            q ^ (r * iD (g * nU Y')) * (ψ₀ (Matrix.trace (Y' * β)) * hC ψ₀ β m g) :=
          Finset.sum_congr rfl fun Y' _ => h2 Y'
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun g _ => ?_
          unfold hC
          rw [map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun Y _ => ?_
          simp only [map_mul, map_pow, Complex.conj_conj, map_natCast, hq]
          ring
  rw [h1, ← h3]
  field_simp

theorem hC_real (ψ₀ : AddChar k ℂ) (β : Matrix (Fin n) (Fin n) k) (r m : ℕ) (g : GL (Ix n) k) :
    ∃ x : ℝ, 0 ≤ x ∧ (starRingEnd ℂ) (hC ψ₀ β r g) * hC ψ₀ β m g = x := by
  obtain ⟨Y₀, V, W, h⟩ := iD_card_sub g
  have key : ∀ a, hC ψ₀ β a (g * nU Y₀) =
      ∑ Y : Matrix (Fin n) (Fin n) k, (starRingEnd ℂ) (ψ₀ (Matrix.trace (Y * β))) * (Nat.card (sV V W Y) : ℂ) ^ a := by
    intro a
    unfold hC
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [← h Y, mul_comm a, pow_mul]
    push_cast
    rfl
  obtain ⟨x, hx, ex, -⟩ := fourier_nonneg ψ₀ β V W r
  obtain ⟨y, hy, ey, -⟩ := fourier_nonneg ψ₀ β V W m
  refine ⟨x * y, mul_nonneg hx hy, ?_⟩
  have e1 := key r
  have e2 := key m
  rw [ex, hC_shift] at e1
  rw [ey, hC_shift] at e2
  have hu : (starRingEnd ℂ) (ψ₀ (Matrix.trace (Y₀ * β))) * ψ₀ (Matrix.trace (Y₀ * β)) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, AddChar.norm_apply]
    simp
  have : ((x : ℂ)) * y = (starRingEnd ℂ) (hC ψ₀ β r g) * hC ψ₀ β m g := by
    have e1' := congrArg (starRingEnd ℂ) e1
    rw [Complex.conj_ofReal, map_mul] at e1'
    rw [← e1', ← e2]
    linear_combination ((starRingEnd ℂ) (hC ψ₀ β r g) * hC ψ₀ β m g) * hu
  push_cast
  exact this.symm

theorem hC_wM_pos (ψ₀ : AddChar k ℂ) (β : Matrix (Fin n) (Fin n) k) (a : ℕ) (h : β.rank ≤ a) :
    ∃ x : ℝ, 0 < x ∧ hC ψ₀ β a (wM : GL (Ix n) k) = x := by
  obtain ⟨x, -, ex, hx⟩ := fourier_nonneg ψ₀ β (⊤ : Submodule k (Fin n → k)) ⊥ a
  obtain ⟨c, hc⟩ := exists_rows β a h
  refine ⟨x, hx ⟨c, fun _ => trivial, fun Y hY => hc Y fun i => by simpa using hY i⟩, ?_⟩
  rw [← ex]
  unfold hC
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [← iD_card_wM Y, mul_comm a, pow_mul]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.Jp.Pos

open GlobalTheory.CompanionTheory.Jp.Pos in

theorem GlobalTheory.CompanionTheory.Jp.Pos.jpPos : GlobalTheory.CompanionTheory.Jp.JpPos := by
  intro k _ _ n r m ψ₀ _ β hr hm
  classical
  haveI : Fintype (GL (Ix n) k) := Fintype.ofFinite _
  rw [show (∃ x : ℝ, 0 < x ∧ _ = (x : ℂ)) ↔ _ from Iff.rfl, sum_eq]
  choose X hX0 hX using fun g : GL (Ix n) k => hC_real ψ₀ β r m g
  have hq : (0 : ℝ) < (Fintype.card k : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨x, hx, ex⟩ := hC_wM_pos ψ₀ β r hr.le
  obtain ⟨y, hy, ey⟩ := hC_wM_pos ψ₀ β m (hr.le.trans hm)
  have hw : 0 < X wM := by
    have := hX wM
    rw [ex, ey, Complex.conj_ofReal] at this
    have h2 : X wM = x * y := by exact_mod_cast this.symm
    rw [h2]; positivity
  refine ⟨((Fintype.card k : ℝ) ^ (n * n))⁻¹ ^ 2 * ∑ g, X g, ?_, ?_⟩
  · refine mul_pos (by positivity) ?_
    exact Finset.sum_pos' (fun g _ => hX0 g) ⟨wM, Finset.mem_univ _, hw⟩
  · unfold sumG
    rw [finsum_eq_sum_of_fintype]
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun g _ => hX g

end
