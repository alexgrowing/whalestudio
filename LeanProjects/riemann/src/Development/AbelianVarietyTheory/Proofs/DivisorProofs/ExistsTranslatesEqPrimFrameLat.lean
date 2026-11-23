import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {D : Type*}

theorem IsUnif.inv_notMem {ϖ : kˣ} (hϖ : IsUnif ϖ) : (ϖ : k)⁻¹ ∉ 𝒪[k] := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  rw [Valuation.mem_integer_iff, map_inv₀, not_le]
  exact (one_lt_inv₀ (zero_lt_iff.2 (by simp))).2 hlt

theorem IsUnif.inv_mul_inv_mem {ϖ : kˣ} (hϖ : IsUnif ϖ) {x : k} (hx : x ∉ 𝒪[k]) : (ϖ : k)⁻¹ * x⁻¹ ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, not_le] at hx
  have h : valuation k x⁻¹ ≤ valuation k (ϖ : k) := by
    rw [hϖ, le_uniformizer_iff, map_inv₀]; exact inv_lt_one_of_one_lt₀ hx
  rw [Valuation.mem_integer_iff, map_mul, map_inv₀ _ (ϖ : k), inv_mul_le_iff₀ (zero_lt_iff.2 (by simp)), mul_one]
  exact h

theorem IsUnif.residue_eq_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (x y : 𝒪[k]) :
    IsLocalRing.residue _ x = IsLocalRing.residue _ y ↔ (ϖ : k)⁻¹ * ((x : k) - y) ∈ 𝒪[k] := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← mem_cball_uniformiser hϖ.irreducible (x := ϖ) rfl, Valuation.mem_integer_iff, map_mul, map_inv₀,
    inv_mul_le_iff₀ (zero_lt_iff.2 (by simp)), mul_one]
  rfl

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem smul_mem_of_int {Λ : Submodule 𝒪[k] (D → k)} {c : k} (hc : c ∈ 𝒪[k]) {x : D → k} (hx : x ∈ Λ) :
    c • x ∈ Λ := Λ.smul_mem ⟨c, hc⟩ hx

theorem vecMul_mem_of_int {A : Type*} [Fintype A] {Λ : Submodule 𝒪[k] (D → k)} {Y : Matrix A D k}
    (hY : Y ∈ matLat A Λ) {c : A → k} (hc : ∀ i, c i ∈ 𝒪[k]) : c ᵥ* Y ∈ Λ := by
  rw [vecMul_eq_sum]
  exact Λ.sum_mem fun i _ => smul_mem_of_int (hc i) (hY i)

theorem isPrimFrame_iff [Fintype D] {A : Type*} [Fintype A] {Λ : Submodule 𝒪[k] (D → k)} {Y : Matrix A D k} :
    IsPrimFrame Λ Y ↔ Y ∈ matLat A Λ ∧ ∀ c : A → k, c ᵥ* Y ∈ Λ → ∀ i, c i ∈ 𝒪[k] := by
  have hli : Y.rank = Fintype.card A ↔ LinearIndependent k Y.row := by
    rw [rank_eq_finrank_span_row, linearIndependent_iff_card_eq_finrank_span, eq_comm]; rfl
  have hv : ∀ c : A → k, c ᵥ* Y = ∑ i, c i • Y.row i := fun c => vecMul_eq_sum _ _
  rw [IsPrimFrame, hli]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h2, fun c hc i => ?_⟩
    have h4 : c ᵥ* Y ∈ Submodule.span 𝒪[k] (Set.range Y.row) := by
      rw [h3]
      exact ⟨(Submodule.mem_span_range_iff_exists_fun k).2 ⟨c, (hv c).symm⟩, hc⟩
    obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h4
    have := Fintype.linearIndependent_iffₛ.1 h1 (fun i => (c' i : k)) c (by rw [← hv c, ← hc']; rfl) i
    exact this ▸ (c' i).2
  · rintro ⟨h2, h⟩
    obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
    refine ⟨Fintype.linearIndependent_iff.2 fun c hc i => ?_, h2, le_antisymm ?_ ?_⟩
    · by_contra hi
      have := h (((ϖ : k)⁻¹ * (c i)⁻¹) • c) (by rw [smul_vecMul, hv, hc, smul_zero]; exact Λ.zero_mem) i
      rw [Pi.smul_apply, smul_eq_mul, inv_mul_cancel_right₀ hi] at this
      exact hϖ.inv_notMem this
    · exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ⟨Submodule.subset_span ⟨i, rfl⟩, h2 i⟩)
    · rintro x ⟨hx, hx'⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
      exact Submodule.sum_mem _ fun i _ =>
        smul_mem_of_int (h c (by rw [hv]; exact hx') i) (Submodule.subset_span ⟨i, rfl⟩)

section Step
variable {n : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem cons_vecMul_rows (u : k) (c : Fin n → k) (Y : Matrix (Fin (n + 1)) D k) :
    (Fin.cons u c : Fin (n + 1) → k) ᵥ* Y = u • Y.row 0 + c ᵥ* Y.submatrix Fin.succ id := by
  funext j
  simp [vecMul, dotProduct, Fin.sum_univ_succ]

theorem isPrimFrame_succ_iff [Fintype D] {ϖ : kˣ} (hϖ : IsUnif ϖ) {Λ : Submodule 𝒪[k] (D → k)}
    (Y : Matrix (Fin (n + 1)) D k) :
    IsPrimFrame Λ Y ↔ IsPrimFrame Λ (Y.submatrix Fin.succ id) ∧ Y.row 0 ∈ Λ ∧
      ∀ c : Fin n → k, (∀ i, c i ∈ 𝒪[k]) → (ϖ : k)⁻¹ • (Y.row 0 + c ᵥ* Y.submatrix Fin.succ id) ∉ Λ := by
  rw [isPrimFrame_iff, isPrimFrame_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i => h1 i.succ, fun c hc i => ?_⟩, h1 0, fun c _ hc => hϖ.inv_notMem ?_⟩
    · exact h2 (Fin.cons 0 c) (by rwa [cons_vecMul_rows, zero_smul, zero_add]) i.succ
    · exact h2 (Fin.cons (ϖ : k)⁻¹ ((ϖ : k)⁻¹ • c)) (by rwa [cons_vecMul_rows, smul_vecMul, ← smul_add]) 0
  · rintro ⟨⟨h1, h2⟩, h0, h3⟩
    refine ⟨Fin.cases h0 h1, fun c hc => ?_⟩
    rw [← Fin.cons_self_tail c, cons_vecMul_rows] at hc
    have hc0 : c 0 ∈ 𝒪[k] := by
      by_contra hc0
      have hne : c 0 ≠ 0 := fun h => hc0 (h ▸ zero_mem _)
      have h4 := smul_mem_of_int (hϖ.inv_mul_inv_mem hc0) hc
      rw [mul_smul, smul_add, inv_smul_smul₀ hne, ← smul_vecMul] at h4
      refine h3 _ (h2 _ ?_) h4
      have h5 := smul_mem_of_int hϖ.mem h4
      rw [smul_inv_smul₀ ϖ.ne_zero] at h5
      exact (add_mem_cancel_left h0).1 h5
    exact Fin.cases hc0 (h2 _ ((add_mem_cancel_left (smul_mem_of_int hc0 h0)).1 hc))

open Classical in

theorem indicator_isPrimFrame_succ [Fintype D] [Fintype 𝓀[k]] {ϖ : kˣ} (hϖ : IsUnif ϖ)
    {Λ : Submodule 𝒪[k] (D → k)} (l : 𝓀[k] → 𝒪[k]) (hl : ∀ r, IsLocalRing.residue _ (l r) = r)
    (Y : Matrix (Fin (n + 1)) D k) :
    (if IsPrimFrame Λ Y then (1 : ℂ) else 0) = (if IsPrimFrame Λ (Y.submatrix Fin.succ id) then (1 : ℂ) else 0) *
      ((if Y.row 0 ∈ Λ then 1 else 0) - ∑ r : Fin n → 𝓀[k],
        if (ϖ : k)⁻¹ • (Y.row 0 + (fun i => (l (r i) : k)) ᵥ* Y.submatrix Fin.succ id) ∈ Λ then 1 else 0) := by
  rw [isPrimFrame_succ_iff hϖ]
  by_cases h : IsPrimFrame Λ (Y.submatrix Fin.succ id)
  swap
  · simp [h]
  obtain ⟨h1, h2⟩ := isPrimFrame_iff.1 h
  simp only [h, true_and, if_true, one_mul]
  generalize Y.submatrix Fin.succ id = Y' at *
  generalize Y.row 0 = y
  have key : ∀ c c' : Fin n → 𝒪[k], (ϖ : k)⁻¹ • (y + (fun i => (c i : k)) ᵥ* Y') ∈ Λ →
      ((ϖ : k)⁻¹ • (y + (fun i => (c' i : k)) ᵥ* Y') ∈ Λ ↔
        ∀ i, IsLocalRing.residue _ (c' i) = IsLocalRing.residue _ (c i)) := fun c c' hc => by
    have e : (ϖ : k)⁻¹ • (y + (fun i => (c' i : k)) ᵥ* Y') = (ϖ : k)⁻¹ • (y + (fun i => (c i : k)) ᵥ* Y') +
        ((ϖ : k)⁻¹ • ((fun i => (c' i : k)) - fun i => (c i : k))) ᵥ* Y' := by
      rw [smul_vecMul, sub_vecMul, ← smul_add]; congr 1; abel
    rw [e, add_mem_cancel_left hc]
    simp only [hϖ.residue_eq_iff]
    exact ⟨fun h => h2 _ h, fun h => vecMul_mem_of_int h1 h⟩
  by_cases h3 : ∀ c : Fin n → k, (∀ i, c i ∈ 𝒪[k]) → (ϖ : k)⁻¹ • (y + c ᵥ* Y') ∉ Λ
  · rw [Finset.sum_eq_zero fun r _ => if_neg (h3 _ fun i => (l (r i)).2), sub_zero]
    simp only [and_iff_left h3]
  · rw [if_neg fun h => h3 h.2]
    push Not at h3
    obtain ⟨c, hc, hc'⟩ := h3
    have hy : y ∈ Λ := by
      have h5 := smul_mem_of_int hϖ.mem hc'
      rw [smul_inv_smul₀ ϖ.ne_zero] at h5
      exact (add_mem_cancel_right (vecMul_mem_of_int h1 hc)).1 h5
    have h6 := fun r : Fin n → 𝓀[k] => key (fun i => ⟨c i, hc i⟩) (fun i => l (r i)) hc'
    simp only [hl, ← funext_iff] at h6
    simp only [h6]
    simp [hy]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def consBlock (u : k) (c : Fin n → k) (γ : Matrix (Fin n) (Fin n) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  Matrix.of (Fin.cons (Fin.cons u c) fun i => Fin.cons 0 (γ i))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_consBlock (u : k) (c : Fin n → k) (γ : Matrix (Fin n) (Fin n) k) :
    (consBlock u c γ).det = u * γ.det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  simp only [consBlock, of_apply, Fin.cons_succ, Fin.cons_zero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  rfl

theorem consBlock_mul_mem {Λ : Submodule 𝒪[k] (D → k)} (u : k) (c : Fin n → k) (γ : Matrix (Fin n) (Fin n) k)
    (Y : Matrix (Fin (n + 1)) D k) : consBlock u c γ * Y ∈ matLat _ Λ ↔
      γ * Y.submatrix Fin.succ id ∈ matLat _ Λ ∧ u • Y.row 0 + c ᵥ* Y.submatrix Fin.succ id ∈ Λ := by
  rw [mem_matLat, mem_matLat, Fin.forall_fin_succ, and_comm, ← cons_vecMul_rows]
  refine and_congr (forall_congr' fun i => ?_) Iff.rfl
  have : (consBlock u c γ * Y).row i.succ = (γ * Y.submatrix Fin.succ id).row i := by
    funext j; simp [consBlock, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [this]

end Step

open Classical in

theorem exists_comb_isPrimFrame.{u} {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Fintype D] {ϖ : kˣ} (hϖ : IsUnif ϖ) (Λ : Submodule 𝒪[k] (D → k)) (n : ℕ) :
    ∃ (ι : Type u) (_ : Fintype ι) (m : ι → ℂ) (γ : ι → Matrix (Fin n) (Fin n) k) (j : ι → ℕ),
      (∀ i, (γ i).det = ((ϖ : k)⁻¹) ^ j i) ∧
      (∀ Y : Matrix (Fin n) D k, ∑ i, m i * (if γ i * Y ∈ matLat _ Λ then 1 else 0) =
        if IsPrimFrame Λ Y then 1 else 0) ∧
      ∀ x : ℂ, ∑ i, m i * x ^ j i = ∏ i ∈ Finset.range n, (1 - (resCard k : ℂ) ^ i * x) := by
  induction n with
  | zero =>
    refine ⟨PUnit, inferInstance, 1, 1, 0, by simp, fun Y => ?_, by simp⟩
    simp [isPrimFrame_iff, mem_matLat]
  | succ n ih =>
    obtain ⟨ι, _, m, γ, j, h1, h2, h3⟩ := ih
    have : Fintype 𝓀[k] := Fintype.ofFinite _
    choose l hl using IsLocalRing.residue_surjective (R := 𝒪[k])
    refine ⟨ι ⊕ ι × (Fin n → 𝓀[k]), inferInstance, Sum.elim m fun p => -m p.1,
      Sum.elim (fun i => consBlock 1 0 (γ i))
        fun p => consBlock (ϖ : k)⁻¹ ((ϖ : k)⁻¹ • fun i => (l (p.2 i) : k)) (γ p.1),
      Sum.elim j fun p => j p.1 + 1, ?_, fun Y => ?_, fun x => ?_⟩
    · rintro (i | p) <;> simp [det_consBlock, h1, pow_succ']
    · rw [indicator_isPrimFrame_succ hϖ l hl, ← h2, Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp only [Sum.elim_inl, Sum.elim_inr, consBlock_mul_mem, smul_vecMul, ← smul_add, one_smul, zero_vecMul,
        add_zero, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : γ i * Y.submatrix Fin.succ id ∈ matLat _ Λ
      · simp only [h, true_and, if_true, mul_one, mul_sub, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
        ring
      · simp [h]
    · rw [Finset.prod_range_succ, ← h3, Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        resCard, Nat.card_eq_fintype_card, Finset.sum_mul, ← Finset.sum_add_distrib, nsmul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring

theorem IsUnif.apow_eq {ϖ : kˣ} (hϖ : IsUnif ϖ) (z : ℂ) : apow ϖ z = (resCard k : ℂ) ^ (-z) := by
  rw [apow, nabs_uniformiser hϖ.irreducible (x := ϖ) rfl, Complex.cpow_neg, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)]; exact Real.pi_ne_zero.symm),
    Complex.ofReal_natCast]

theorem apow_pow (x : kˣ) (j : ℕ) (z : ℂ) : apow (x ^ j) z = apow x z ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, apow_mul, ih, pow_succ]

theorem prod_primFactor_ne_zero {c : ℂ} (hc : ‖c‖ = 1) {a' d : ℕ} (h : (a' : ℝ) - 1 < (d : ℝ) / 2) :
    ∏ i ∈ Finset.range a', (1 - (resCard k : ℂ) ^ i * (c * (resCard k : ℂ) ^ (-(d : ℂ) / 2))) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i hi h0 => ?_
  have hq : 1 < resCard k := Finite.one_lt_card
  have hq' : (1 : ℝ) < resCard k := by exact_mod_cast hq
  have h1 := congrArg norm (sub_eq_zero.1 h0)
  rw [norm_mul, norm_mul, hc, one_mul, norm_one, norm_pow, Complex.norm_natCast,
    Complex.norm_natCast_cpow_of_pos (by omega), ← Real.rpow_natCast, ← Real.rpow_add (by linarith)] at h1
  refine (Real.rpow_lt_one_of_one_lt_of_neg hq' ?_).ne' h1
  have h2 : (i : ℝ) + 1 ≤ a' := by exact_mod_cast Finset.mem_range.1 hi
  have h3 : (-(d : ℂ) / 2).re = -(d : ℝ) / 2 := by simp
  rw [h3]; linarith

variable [Fintype D] [DecidableEq D]

theorem exists_translates_eq_primFrame_lat {ϖ : kˣ} (hϖ : IsUnif ϖ) (ν α : kˣ →* ℂˣ)
    (Λ : Submodule 𝒪[k] (D → k)) (a' : ℕ) :
    ∃ z : GL (Fin a') k →₀ ℂ,
      (z.sum fun g c => c • omB ν α g 1 ((matLat (Fin a') Λ : Set (Matrix (Fin a') D k)).indicator 1)) =
        {Y : Matrix (Fin a') D k | IsPrimFrame Λ Y}.indicator 1 ∧
      (z.sum fun _ c => c) = ∏ i ∈ Finset.range a',
        (1 - (resCard k : ℂ) ^ i * ((ν ϖ : ℂ) * (resCard k : ℂ) ^ (-(Fintype.card D : ℂ) / 2))) := by
  classical
  obtain ⟨ι, _, m, γ, j, h1, h2, h3⟩ := exists_comb_isPrimFrame hϖ Λ a'
  set x : ℂ := (ν ϖ : ℂ) * (resCard k : ℂ) ^ (-(Fintype.card D : ℂ) / 2) with hx
  let g : ι → GL (Fin a') k := fun i =>
    Matrix.GeneralLinearGroup.mkOfDetNeZero (γ i)ᵀ (by rw [det_transpose, h1]; simp)
  have hg : ∀ i, (g i).valᵀ = γ i := fun i => transpose_transpose _
  have hd : ∀ i, gdet (g i) = ϖ⁻¹ ^ j i := fun i => Units.ext (by
    show (γ i)ᵀ.det = _
    rw [det_transpose, h1]; simp)
  have hf : ∀ i, x ^ j i * ((ν (gdet (g i)) : ℂ) * apow (gdet (g i)) ((Fintype.card D : ℂ) / 2)) = 1 := fun i => by
    rw [hd, map_pow, apow_pow, Units.val_pow_eq_pow_val, ← mul_pow, ← mul_pow, hx, neg_div, ← hϖ.apow_eq,
      mul_mul_mul_comm, ← Units.val_mul, ← map_mul, ← apow_mul]
    simp
  refine ⟨∑ i, Finsupp.single (g i) (m i * x ^ j i), ?_, ?_⟩
  · rw [← Finsupp.linearCombination_apply ℂ, map_sum]
    funext Y
    rw [Finset.sum_apply, show {Y : Matrix (Fin a') D k | IsPrimFrame Λ Y}.indicator 1 Y =
      if IsPrimFrame Λ Y then (1 : ℂ) else 0 by simp [Set.indicator_apply], ← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finsupp.linearCombination_single, Pi.smul_apply, smul_eq_mul, omB, map_one, Units.val_one, apow_one,
      mul_one, Matrix.mul_one, hg, Set.indicator_apply, SetLike.mem_coe, Pi.one_apply]
    rw [mul_assoc, ← mul_assoc (x ^ j i), hf, one_mul]
  · rw [← Finsupp.sum_finsetSum_index (by simp) (by simp), ← h3]
    exact Finset.sum_congr rfl fun i _ => Finsupp.sum_single_index rfl

theorem exists_translates_eq_primFrame {ϖ : kˣ} (hϖ : IsUnif ϖ) (ν α : kˣ →* ℂˣ) (a' : ℕ) :
    ∃ z : GL (Fin a') k →₀ ℂ,
      (z.sum fun g c => c • omB ν α g 1 ((matLat (Fin a') (stdLat k D) : Set (Matrix (Fin a') D k)).indicator 1)) =
        {Y : Matrix (Fin a') D k | IsPrimFrame (stdLat k D) Y}.indicator 1 ∧
      (z.sum fun _ c => c) = ∏ i ∈ Finset.range a',
        (1 - (resCard k : ℂ) ^ i * ((ν ϖ : ℂ) * (resCard k : ℂ) ^ (-(Fintype.card D : ℂ) / 2))) ∧
      (‖(ν ϖ : ℂ)‖ = 1 → (a' : ℝ) - 1 < (Fintype.card D : ℝ) / 2 → (z.sum fun _ c => c) ≠ 0) := by
  obtain ⟨z, h1, h2⟩ := exists_translates_eq_primFrame_lat hϖ ν α (stdLat k D) a'
  exact ⟨z, h1, h2, fun hν h => h2 ▸ prod_primFactor_ne_zero hν h⟩

end GlobalTheory.SplitFlip
