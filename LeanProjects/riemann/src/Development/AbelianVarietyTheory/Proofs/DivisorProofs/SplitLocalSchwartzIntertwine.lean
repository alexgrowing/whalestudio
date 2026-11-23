import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InsP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantOfClose

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone GlobalTheory.EvZeroStd
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EvZeroStd

section General

variable {X : Type} [TopologicalSpace X]

theorem mul_mem_SB {χ f : X → ℂ} (hχ : IsLocallyConstant χ) (hf : f ∈ SB X) : (fun x => χ x * f x) ∈ SB X :=
  ⟨hχ.mul hf.1, hf.2.mul_left (f := χ)⟩

theorem translate_mem_SB [AddGroup X] [IsTopologicalAddGroup X] {f : X → ℂ} (hf : f ∈ SB X) (A : X) :
    (fun x => f (x + A)) ∈ SB X :=
  ⟨hf.1.comp_continuous (continuous_add_right A), hf.2.comp_homeomorph (Homeomorph.addRight A)⟩

variable {L : (X → ℂ) → ℂ}

theorem lin_zero (hL : ∀ f ∈ SB X, ∀ g ∈ SB X, ∀ z : ℂ, L (z • f + g) = z * L f + L g) : L 0 = 0 := by
  have := hL 0 (zero_mem _) 0 (zero_mem _) 1
  simpa using this

theorem lin_sum (hL : ∀ f ∈ SB X, ∀ g ∈ SB X, ∀ z : ℂ, L (z • f + g) = z * L f + L g) {ι : Type} (t : Finset ι)
    (f : ι → X → ℂ) (hf : ∀ i, f i ∈ SB X) : L (∑ i ∈ t, f i) = ∑ i ∈ t, L (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using lin_zero hL
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    have := hL _ (hf a) _ (Submodule.sum_mem _ fun i (_ : i ∈ t) => hf i) 1
    simpa using this

theorem lin_eq_zero_of_support (hL : ∀ f ∈ SB X, ∀ g ∈ SB X, ∀ z : ℂ, L (z • f + g) = z * L f + L g) {ι : Type}
    (χ : ι → X → ℂ) (hχ : ∀ i, IsLocallyConstant (χ i)) (hinv : ∀ i, ∀ f ∈ SB X, L (fun x => χ i x * f x) = L f)
    (f : X → ℂ) (hf : f ∈ SB X) (hs : ∀ x, f x ≠ 0 → ∃ i, χ i x ≠ 1) : L f = 0 := by
  classical
  have key : ∀ t : Finset {p : ι × ℂ // p.2 ≠ 1}, ∀ f ∈ SB X, (∀ x, f x ≠ 0 → ∃ p ∈ t, χ p.1.1 x = p.1.2) → L f = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro f _ h
      have : f = 0 := funext fun x => by
        by_contra hx
        simpa using h x hx
      rw [this, lin_zero hL]
    | insert p t _ ih =>
      intro f hf h
      have hg := mul_mem_SB (hχ p.1.1) hf
      have h1 := ih _ (add_mem (Submodule.smul_mem _ (-p.1.2) hf) hg) fun x hx => by
        have hx' : (χ p.1.1 x - p.1.2) * f x ≠ 0 := by
          intro h0
          apply hx
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          linear_combination h0
        obtain ⟨q, hq, hq'⟩ := h x (right_ne_zero_of_mul hx')
        rcases Finset.mem_insert.1 hq with rfl | hq
        · exact absurd (sub_eq_zero.2 hq') (left_ne_zero_of_mul hx')
        · exact ⟨q, hq, hq'⟩
      rw [hL _ hf _ hg, hinv _ _ hf] at h1
      have h2 : (1 - p.1.2) * L f = 0 := by linear_combination h1
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 p.2.symm)
  have hK : IsCompact (Function.support f) :=
    hf.2.isCompact.of_isClosed_subset (hf.1.isClopen_fiber 0).isOpen.isClosed_compl subset_closure
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun p : {p : ι × ℂ // p.2 ≠ 1} => {x | χ p.1.1 x = p.1.2})
    (fun p => (hχ p.1.1).isOpen_fiber _) fun x hx => by
      obtain ⟨i, hi⟩ := hs x hx
      exact Set.mem_iUnion.2 ⟨⟨(i, χ i x), hi⟩, rfl⟩
  refine key t f hf fun x hx => ?_
  simpa using ht hx

end General

section Columns

variable {k : Type} [Field k] {b a' : ℕ}

def skipCol (b a' : ℕ) (j : Fin (b + a')) : Fin (b + 2 + a') :=
  ⟨skip 0 (b + 1) j, by have := j.2; unfold skip; split_ifs <;> omega⟩

theorem skipCol_injective : Function.Injective (skipCol b a') := by
  intro i j h
  have h' : skip 0 (b + 1) i = skip 0 (b + 1) j := congrArg Fin.val h
  apply Fin.ext
  unfold skip at h'
  split_ifs at h' <;> omega

theorem col_cases (j : Fin (b + 2 + a')) : (j : ℕ) = 0 ∨ (j : ℕ) = b + 1 ∨ ∃ j', j = skipCol b a' j' := by
  have := j.2
  by_cases h0 : (j : ℕ) = 0
  · exact Or.inl h0
  by_cases h1 : (j : ℕ) = b + 1
  · exact Or.inr (Or.inl h1)
  refine Or.inr (Or.inr ?_)
  by_cases h2 : (j : ℕ) ≤ b
  · refine ⟨⟨j - 1, by omega⟩, Fin.ext ?_⟩
    simp only [skipCol, skip]
    split_ifs <;> omega
  · refine ⟨⟨j - 2, by omega⟩, Fin.ext ?_⟩
    simp only [skipCol, skip]
    split_ifs <;> omega

theorem mul_insP_skipCol (Y : Matrix (Fin a') (Fin (b + a')) k) (i : Fin a') (j : Fin (b + a')) :
    (Y * (insP k b a')ᵀ) i (skipCol b a' j) = Y i j := by
  have : ∀ j' : Fin (b + a'), (((skipCol b a' j : Fin _) : ℕ) = skip 0 (b + 1) j') ↔ j = j' := fun j' =>
    ⟨fun h => skipCol_injective (Fin.ext h), fun h => h ▸ rfl⟩
  simp [Matrix.mul_apply, insP, this]

theorem mul_insP_other (Y : Matrix (Fin a') (Fin (b + a')) k) (i : Fin a') (j : Fin (b + 2 + a'))
    (hj : (j : ℕ) = 0 ∨ (j : ℕ) = b + 1) : (Y * (insP k b a')ᵀ) i j = 0 := by
  have : ∀ j' : Fin (b + a'), ¬ ((j : ℕ) = skip 0 (b + 1) j') := fun j' => by
    unfold skip
    split_ifs <;> omega
  simp [Matrix.mul_apply, insP, this]

theorem pairM_single {m n : ℕ} (Z : Matrix (Fin m) (Fin n) k) (i : Fin m) (j : Fin n) (t : k) :
    GlobalTheory.FlipMatch.pairM Z (Matrix.single i j t) = Z i j * t := by
  unfold GlobalTheory.FlipMatch.pairM
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro j' _ h
    simp [h.symm]
  · simp
  · intro i' _ h
    simp [h.symm]
  · simp

theorem single_mul_insP (i : Fin a') (j : Fin (b + a')) (t : k) :
    Matrix.single i j t * (insP k b a')ᵀ = Matrix.single i (skipCol b a' j) t := by
  ext i' j'
  rcases col_cases j' with h | h | ⟨j'', rfl⟩
  · rw [mul_insP_other _ _ _ (Or.inl h), Matrix.single_apply_of_col_ne]
    rintro rfl
    simp only [skipCol, skip] at h
    split_ifs at h <;> omega
  · rw [mul_insP_other _ _ _ (Or.inr h), Matrix.single_apply_of_col_ne]
    rintro rfl
    simp only [skipCol, skip] at h
    split_ifs at h <;> omega
  · rw [mul_insP_skipCol]
    simp [Matrix.single, skipCol_injective.eq_iff]

end Columns

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLocallyConstant_char (ψ₀ : AddChar k ℂ) (h : ∀ y ∈ 𝒪[k], ψ₀ y = 1) : IsLocallyConstant ψ₀ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : k => y - x := by fun_prop
  have ht := hc.tendsto x
  simp only [sub_self] at ht
  have := ht ((GlobalTheory.SplitWeil.isOpen_int k).mem_nhds (zero_mem 𝒪[k]))
  filter_upwards [this] with y hy
  have e : y = x + (y - x) := by ring
  rw [e, AddChar.map_add_eq_mul, h _ hy, mul_one]

open Classical in

def colInd {m n : ℕ} (s : kˣ) (j₀ : Fin n) (Z : Matrix (Fin m) (Fin n) k) : ℂ :=
  if (∀ i j, Z i j ∈ 𝒪[k]) ∧ ∀ i, Z i j₀ ∈ GlobalTheory.SplitWeil.cball s then 1 else 0

theorem colInd_mem_SB {m n : ℕ} {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (c : ℕ) (j₀ : Fin n) :
    colInd (ϖ ^ c) j₀ ∈ SB (Matrix (Fin m) (Fin n) k) := by
  have key : ∀ X Y : Matrix (Fin m) (Fin n) k,
      (∀ i j, valuation k (Y i j - X i j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k)) →
      ((∀ i j, X i j ∈ 𝒪[k]) ∧ ∀ i, X i j₀ ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) →
      ((∀ i j, Y i j ∈ 𝒪[k]) ∧ ∀ i, Y i j₀ ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) := fun X Y h hX => by
    refine ⟨fun i j => ?_, fun i => cball_stable hϖ (h i j₀) (hX.2 i)⟩
    have : Y i j = (Y i j - X i j) + X i j := by ring
    rw [this]
    exact add_mem (show valuation k (Y i j - X i j) ≤ 1 from (h i j).trans (unif_pow_facts hϖ c).1.le) (hX.1 i j)
  refine ⟨isLocallyConstant_of_close (ϖ ^ (c + 1)) _ fun X Y h => ?_, hasCompactSupport_of_int _ fun X hX => ?_⟩
  · classical
    unfold colInd
    refine if_congr ⟨key Y X fun i j => ?_, key X Y h⟩ rfl rfl
    rw [Valuation.map_sub_swap]
    exact h i j
  · unfold colInd at hX
    split_ifs at hX with h
    · exact h.1
    · exact absurd rfl hX

theorem sum_colInd {m n : ℕ} {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (c : ℕ) (j₀ : Fin n)
    [Fintype (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ c)] :
    (∑ ρ : Fin m → 𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ c, fun Z : Matrix (Fin m) (Fin n) k =>
      colInd (ϖ ^ c) j₀ (Z + Matrix.vecMulVec (fun i => ((Quotient.out (ρ i) : 𝒪[k]) : k)) (Pi.single j₀ 1))) =
      Set.indicator {Z | ∀ i j, Z i j ∈ 𝒪[k]} 1 := by
  classical
  have hI : ∀ x : 𝒪[k], x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c ↔ (x : k) ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := fun x => by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      ← (Valuation.integer.integers (valuation k)).le_iff_dvd]
    exact Iff.rfl
  have hint : ∀ (r : Fin m → 𝒪[k]) i j, Matrix.vecMulVec (fun i => (r i : k)) (Pi.single j₀ 1) i j ∈ 𝒪[k] := fun r i j => by
    rw [Matrix.vecMulVec_apply, Pi.single_apply]
    split_ifs <;> simp
  funext Z
  rw [Finset.sum_apply]
  by_cases hZ : ∀ i j, Z i j ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (by exact hZ), Pi.one_apply,
      Finset.sum_eq_single (fun i => -Ideal.Quotient.mk _ (⟨Z i j₀, hZ i j₀⟩ : 𝒪[k]))]
    · unfold colInd
      rw [if_pos]
      refine ⟨fun i j => add_mem (hZ i j) (hint _ i j), fun i => ?_⟩
      have := (hI (⟨Z i j₀, hZ i j₀⟩ + Quotient.out
        (-Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c) (⟨Z i j₀, hZ i j₀⟩ : 𝒪[k])))).1 (by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, Ideal.Quotient.mk_out, add_neg_cancel])
      simpa [Matrix.vecMulVec_apply] using this
    · intro ρ _ hρ
      unfold colInd
      rw [if_neg]
      rintro ⟨-, h⟩
      apply hρ
      funext i
      have := (hI (⟨Z i j₀, hZ i j₀⟩ + Quotient.out (ρ i))).2 (by simpa [Matrix.vecMulVec_apply] using h i)
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, Ideal.Quotient.mk_out] at this
      exact eq_neg_of_add_eq_zero_right this
    · simp
  · rw [Set.indicator_of_notMem (by exact hZ)]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    unfold colInd
    rw [if_neg]
    rintro ⟨h, -⟩
    apply hZ
    intro i j
    simpa using sub_mem (h i j) (hint (fun i => Quotient.out (ρ i)) i j)

theorem stdB_add_insP (ν : kˣ →* ℂˣ) {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (c b a' : ℕ)
    (Y : Matrix (Fin a') (Fin (b + a')) k) (Z : Matrix (Fin a') (Fin (b + 2 + a')) k)
    (hZ : ∀ i (j : Fin (b + 2 + a')), (j : ℕ) ≠ b + 1 → Z i j = 0) :
    stdB ν ϖ c (b + 2) a' (Z + Y * (insP k b a')ᵀ) =
      stdB ν ϖ c b a' Y * colInd (ϖ ^ c) (⟨b + 1, by omega⟩ : Fin (b + 2 + a')) Z := by
  have h2 : blk₂ (Z + Y * (insP k b a')ᵀ) = blk₂ Y := by
    ext i j
    have e : Fin.natAdd (b + 2) j = skipCol b a' (Fin.natAdd b j) := by
      apply Fin.ext
      simp only [skipCol, skip, Fin.val_natAdd]
      split_ifs <;> omega
    simp only [blk₂, Matrix.of_apply, Matrix.add_apply]
    rw [hZ i _ (by simp only [Fin.val_natAdd]; omega), e, mul_insP_skipCol, zero_add]
  have h0 : (0 : k) ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by simp [GlobalTheory.SplitWeil.cball]
  have h1 : (∀ i j, blk₁ (Z + Y * (insP k b a')ᵀ) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) ↔
      (∀ i j, blk₁ Y i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) ∧
        ((∀ i j, Z i j ∈ 𝒪[k]) ∧ ∀ i, Z i ⟨b + 1, by omega⟩ ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) := by
    simp only [blk₁, Matrix.of_apply, Matrix.add_apply]
    constructor
    · intro h
      have hc : ∀ i, Z i ⟨b + 1, by omega⟩ ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := fun i => by
        have := h i ⟨b + 1, by omega⟩
        rw [mul_insP_other _ _ _ (Or.inr rfl), add_zero] at this
        exact this
      refine ⟨fun i j => ?_, fun i j => ?_, hc⟩
      · have := h i ⟨j + 1, by omega⟩
        have e : Fin.castAdd a' (⟨j + 1, by omega⟩ : Fin (b + 2)) = skipCol b a' (Fin.castAdd a' j) := by
          apply Fin.ext
          have := j.2
          simp only [skipCol, skip, Fin.val_castAdd]
          split_ifs <;> omega
        rw [hZ i _ (by have := j.2; simp only [Fin.val_castAdd]; omega), e, mul_insP_skipCol, zero_add] at this
        exact this
      · by_cases hj : (j : ℕ) = b + 1
        · have e : j = ⟨b + 1, by omega⟩ := Fin.ext hj
          rw [e]
          exact (Valuation.mem_integer_iff _ _).2 (le_trans (hc i) (unif_pow_facts hϖ c).2.2)
        · rw [hZ i j hj]
          exact zero_mem _
    · rintro ⟨hY, -, hc⟩ i j
      have hj := j.2
      by_cases hj0 : (j : ℕ) = 0
      · rw [hZ i _ (by simp only [Fin.val_castAdd]; omega), mul_insP_other _ _ _ (Or.inl hj0), add_zero]
        exact h0
      by_cases hj1 : (j : ℕ) = b + 1
      · have e : Fin.castAdd a' j = ⟨b + 1, by omega⟩ := Fin.ext hj1
        rw [mul_insP_other _ _ _ (Or.inr hj1), add_zero, e]
        exact hc i
      · have e : Fin.castAdd a' j = skipCol b a' (Fin.castAdd a' ⟨j - 1, by omega⟩) := by
          apply Fin.ext
          simp only [skipCol, skip, Fin.val_castAdd]
          split_ifs <;> omega
        rw [hZ i _ (by simp only [Fin.val_castAdd]; omega), e, mul_insP_skipCol, zero_add]
        exact hY i _
  unfold stdB colInd
  by_cases hA : (∀ i j, Z i j ∈ 𝒪[k]) ∧ ∀ i, Z i ⟨b + 1, by omega⟩ ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
  · rw [if_pos hA, mul_one]
    by_cases hB : (blk₂ Y).det ≠ 0 ∧ IsGLO (blk₂ Y) ∧ ∀ i j, blk₁ Y i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
    · rw [dif_pos hB, dif_pos ⟨h2 ▸ hB.1, h2 ▸ hB.2.1, h1.2 ⟨hB.2.2, hA⟩⟩]
      simp only [h2]
    · rw [dif_neg hB, dif_neg fun h => hB ⟨h2 ▸ h.1, h2 ▸ h.2.1, (h1.1 h.2.2).1⟩]
  · rw [if_neg hA, mul_zero, dif_neg fun h => hA (h1.1 h.2.2).2]

end Local

theorem map_stdB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ₀ : AddChar k ℂ),
    (∀ x : k, (∀ y ∈ 𝒪[k], ψ₀ (x * y) = 1) ↔ x ∈ 𝒪[k]) →
    ∀ (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (c b a' : ℕ)
    (S : (Matrix (Fin a') (Fin (b + 2 + a')) k → ℂ) → Matrix (Fin a') (Fin (b + a')) k → ℂ),
    (∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k), ∀ g ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k), ∀ z : ℂ,
      S (z • f + g) = z • S f + S g) →
    (∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k), ∀ r : Fin a' → k,
      S (fun Z => f (Z + Matrix.vecMulVec r (Pi.single ⟨b + 1, by omega⟩ 1))) = S f) →
    (∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k), ∀ s : Fin a' → k,
      S (fun Z => ψ₀ (GlobalTheory.FlipMatch.pairM Z (Matrix.vecMulVec s (Pi.single 0 1))) * f Z) = S f) →
    (∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k), ∀ Y : Matrix (Fin a') (Fin (b + a')) k,
      S (fun Z => f (Z + Y * (insP k b a')ᵀ)) = fun Z => S f (Z + Y)) →
    (∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k), ∀ Y : Matrix (Fin a') (Fin (b + a')) k,
      S (fun Z => ψ₀ (GlobalTheory.FlipMatch.pairM Z (Y * (insP k b a')ᵀ)) * f Z) = fun Z => ψ₀ (GlobalTheory.FlipMatch.pairM Z Y) * S f Z) →
    S (Set.indicator {Z | ∀ i j, Z i j ∈ 𝒪[k]} 1) = Set.indicator {Z | ∀ i j, Z i j ∈ 𝒪[k]} 1 →
    stdB ν ϖ c (b + 2) a' ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k) →
    S (stdB ν ϖ c (b + 2) a') = ((Nat.card 𝓀[k] : ℂ) ^ (-((c * a' : ℕ) : ℤ))) • stdB ν ϖ c b a' := by
  intro k _ _ _ _ ψ₀ hψ ν ϖ hϖ c b a' S hlin htr hch hY hX hvac hSB
  classical
  have hL : ∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k), ∀ g ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k), ∀ z : ℂ,
      (fun f => S f 0) (z • f + g) = z * (fun f => S f 0) f + (fun f => S f 0) g := fun f hf g hg z => by
    simp [hlin f hf g hg z]
  have hψ1 : ∀ y ∈ 𝒪[k], ψ₀ y = 1 := fun y hy => by simpa using (hψ 1).2 (one_mem _) y hy
  have hψ2 : ∀ x : k, x ≠ 0 → ∃ t, ψ₀ (x * t) ≠ 1 := fun x hx => by
    have hn : (ϖ : k)⁻¹ ∉ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_inv₀, not_le, hϖ]
      exact one_lt_inv_iff₀.2 ⟨uniformizer_pos, uniformizer_lt_one⟩
    rw [← hψ] at hn
    push Not at hn
    obtain ⟨y, -, hy⟩ := hn
    exact ⟨x⁻¹ * ((ϖ : k)⁻¹ * y), by rwa [mul_inv_cancel_left₀ hx]⟩
  set j₀ : Fin (b + 2 + a') := ⟨b + 1, by omega⟩ with hj₀
  have hvan : ∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) k),
      (∀ Z : Matrix (Fin a') (Fin (b + 2 + a')) k, (∀ i (j : Fin (b + 2 + a')), (j : ℕ) ≠ b + 1 → Z i j = 0) → f Z = 0) →
      S f 0 = 0 := fun f hf h => by
    refine lin_eq_zero_of_support (L := fun f => S f 0) hL (ι := Fin a' × {j : Fin (b + 2 + a') // (j : ℕ) ≠ b + 1} × k)
      (fun p Z => ψ₀ (Z p.1 p.2.1 * p.2.2)) (fun p => ?_) ?_ f hf fun Z hZ => ?_
    · exact (isLocallyConstant_char ψ₀ hψ1).comp_continuous
        ((continuous_id.matrix_elem p.1 p.2.1.1).mul continuous_const)
    · rintro ⟨i, ⟨j, hj⟩, t⟩ f hf
      rcases col_cases j with h | h | ⟨j', rfl⟩
      · obtain rfl : j = 0 := Fin.ext h
        have := hch f hf (Pi.single i t)
        rw [show Matrix.vecMulVec (Pi.single i t) (Pi.single (0 : Fin (b + 2 + a')) (1 : k)) = Matrix.single i 0 t by
          ext i' j'
          simp only [Matrix.vecMulVec_apply, Pi.single_apply, Matrix.single, Matrix.of_apply, @eq_comm _ i i', @eq_comm _ 0 j']
          by_cases h1 : i' = i <;> by_cases h2 : j' = 0 <;> simp [h1, h2]] at this
        simp only [pairM_single] at this
        exact congrFun this 0
      · exact absurd h hj
      · have := congrFun (hX f hf (Matrix.single i j' t)) 0
        simp only [single_mul_insP, pairM_single] at this
        simpa using this
    · by_contra hc
      push Not at hc
      refine hZ (h Z fun i j hj => ?_)
      by_contra h0
      obtain ⟨t, ht⟩ := hψ2 _ h0
      exact ht (hc ⟨i, ⟨j, hj⟩, t⟩)
  have hg := colInd_mem_SB (m := a') hϖ c j₀
  have hcard : Nat.card (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ c) = Nat.card 𝓀[k] ^ c := by
    have hq := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[k]) (IsDiscreteValuationRing.not_a_field _) (i := c)
    rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
    exact hq
  have hq0 : Nat.card 𝓀[k] ≠ 0 := Nat.card_pos.ne'
  haveI : Finite (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ c) :=
    Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero _ hq0)
  haveI := Fintype.ofFinite (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ c)
  have hone : (Nat.card 𝓀[k] : ℂ) ^ (c * a') * S (colInd (ϖ ^ c) j₀) 0 = 1 := by
    have h1 := lin_sum (L := fun f => S f 0) hL Finset.univ (fun (ρ : Fin a' → 𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ c)
      (Z : Matrix (Fin a') (Fin (b + 2 + a')) k) =>
      colInd (ϖ ^ c) j₀ (Z + Matrix.vecMulVec (fun i => ((Quotient.out (ρ i) : 𝒪[k]) : k)) (Pi.single j₀ 1)))
      fun ρ => translate_mem_SB hg _
    rw [sum_colInd hϖ] at h1
    simp only [hvac, htr _ hg] at h1
    rw [Set.indicator_of_mem (by simp), Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      ← Nat.card_eq_fintype_card, hcard, ← pow_mul] at h1
    simpa using h1.symm
  funext Y
  have hf := translate_mem_SB hSB (Y * (insP k b a')ᵀ)
  have h1 := hvan _ (add_mem (Submodule.smul_mem _ (-stdB ν ϖ c b a' Y) hg) hf) fun Z hZ => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [stdB_add_insP ν hϖ c b a' Y Z hZ]
    ring
  rw [hlin _ hg _ hf, hY _ hSB] at h1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add] at h1 ⊢
  rw [zpow_neg, zpow_natCast, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 hq0))]
  linear_combination (Nat.card 𝓀[k] : ℂ) ^ (c * a') * h1 + stdB ν ϖ c b a' Y * hone

end GlobalTheory.EvZeroStd
