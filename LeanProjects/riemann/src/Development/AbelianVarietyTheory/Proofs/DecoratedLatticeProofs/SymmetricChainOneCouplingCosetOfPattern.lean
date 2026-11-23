import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.SymChain
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

section SlopeTestRemainingChoices
variable {k : Type} [Field k] {ι ι' n n' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

omit [Fintype ι] [DecidableEq ι] in

theorem typeFrame_bas_zero (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin 0) : (typeFrame ϖ ord).bas = 1 := by
  apply Units.ext
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [typeFrame, embA, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in

theorem coords_withCol (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin 0) (ord' : ι' ≃ n' ⊕ Fin (0 + 1)) (x₀ : Matrix n n' k)
    (y : n → k) : (typeFrame ϖ ord).coords (typeFrame ϖ ord') (withCol x₀ y) =
      (withCol x₀ ((ϖ : k) • y)).submatrix ord ord' := by
  unfold LatFrame.coords
  rw [typeFrame_bas_zero]
  congr 1
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [withCol, typeFrame, embA, Matrix.fromBlocks_multiply]
    · simp [withCol, typeFrame, embA, Matrix.fromBlocks_multiply, Fin.eq_zero j, mul_comm]
  · exact i.elim0

variable [ValuativeRel k]

theorem unif_mul_lt_one_iff {ϖ : kˣ} (h : IsUnif ϖ) (z : k) :
    valuation k ((ϖ : k) * z) < 1 ↔ valuation k z ≤ 1 := by
  rw [h, map_mul]
  have h0 : 0 < valuation k (ϖ : k) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr (Units.ne_zero ϖ)
  exact mul_le_iff_le_one_right h0

end SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem SymData.Psi_one_eq (x₀ : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) (y : XIx (Fin κ) t (s + 1) → k) :
    (S.T t).Psi 1 x₀ y = (S.P.iter t S.μ S.tame s).Phi t (S.μ (s + 1))
      (((withCol x₀ ((S.ϖ : k) • y)).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl)
        (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id) := by
  simp only [Chain.Psi, om_one, SymData.T, typeChain, Chain.ofType, LatFrame.transport, coords_withCol,
    TypeDatum.iterPhi]

omit [Fintype t] [DecidableEq t] in

theorem not_freeIx_col (ρ : ℕ) {l j : ℕ} (a : Ix (Fin κ ⊕ Fin (l + 1)) t j) :
    ¬ FreeIx ρ a (.inl (.inr 0)) := by
  rcases a with (i | i) | p <;> simp [FreeIx, FreeTop]

omit [Fintype t] [DecidableEq t] in
theorem stdOrd_last (s : ℕ) : stdOrd (Fin κ) t (s + 1) 0 rfl (.inl (.inr 0)) = .inl (.inl (.inr 0)) := by
  simpa using stdOrd_f (Fin κ) t (s + 1) 0 rfl 0

omit [Fintype t] [DecidableEq t] in
theorem stdOrd_pen (s : ℕ) : stdOrd (Fin κ) t s (0 + 1) rfl (.inl (.inr 0)) = .inr 0 := by
  simpa using standardOrderExtendedBasis_apply_low_block (Fin κ) t s (0 + 1) rfl 0

omit [Fintype t] in
theorem SymData.symmetricChain_sub_base_mem_latticeBox_iff (y : XIx (Fin κ) t (s + 1) → k) :
    y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ) ↔ ∀ i, valuation k ((S.ϖ : k) * y i -
      (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i (Sum.inl (Sum.inr 0))) < 1 := by
  rw [mem_box]
  refine forall_congr' fun i => ?_
  have e : (S.ϖ : k) * y i - (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i (Sum.inl (Sum.inr 0)) =
      (S.ϖ : k) * (y - S.y0 t) i := by
    simp only [SymData.y0, Pi.sub_apply, Pi.single_apply, Matrix.one_apply, mul_sub]
    split_ifs <;> simp
  rw [e, unif_mul_lt_one_iff S.unif]
  simp

private theorem stdOrd_ixSucc_inl_inr_zero :
    stdOrd (Fin κ) t (s + 1) 0 rfl (ixSucc (Fin κ ⊕ Fin (s + 1)) t s (Sum.inl (Sum.inl (Sum.inr 0)))) =
      Sum.inl (Sum.inl (Sum.inr 0)) := by
  have h : ixSucc (Fin κ ⊕ Fin (s + 1)) t s (Sum.inl (Sum.inl (Sum.inr 0))) = Sum.inl (Sum.inr 0) := rfl
  rw [h, stdOrd_last]

private theorem submatrix_withCol_stdOrd_ixSucc_apply_eq (x₀ : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k)
    (w : XIx (Fin κ) t (s + 1) → k) (r : Ix (Fin κ ⊕ Fin (s + 1)) t s ⊕ t) (i : XIx (Fin κ) t (s + 1))
    (hr : stdOrd (Fin κ) t (s + 1) 0 rfl (ixSucc _ t s r) = Sum.inl i) :
    (((withCol x₀ w).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl) (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix
      (ixSucc _ t s) id) r (Sum.inl (Sum.inr 0)) = w i := by
  simp only [Matrix.submatrix_apply, id, hr, stdOrd_pen, withCol, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]

private theorem sub_y0_mem_box_of_psi_ne_zero (hP : S.Pattern t)
    (x₀ : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) (y : XIx (Fin κ) t (s + 1) → k)
    (h : (S.T t).Psi 1 x₀ y ≠ 0) : y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ) := by
  rw [S.Psi_one_eq t x₀ y] at h
  have hent := submatrix_withCol_stdOrd_ixSucc_apply_eq t x₀ ((S.ϖ : k) • y)
  generalize hX : ((withCol x₀ ((S.ϖ : k) • y)).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl)
    (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id = X at h hent
  obtain ⟨⟨g, hgJ, hg⟩, hmax⟩ := (TypeDatum.Phi_ne_zero_iff _ _).mp h
  rw [hP s g] at hgJ
  rw [S.symmetricChain_sub_base_mem_latticeBox_iff t y]
  intro i
  set b' : Ix (Fin κ ⊕ Fin (s + 1)) t s := Sum.inl (Sum.inr 0) with hb'
  set r := (ixSucc _ t s).symm ((stdOrd (Fin κ) t (s + 1) 0 rfl).symm (Sum.inl i)) with hrdef
  have hr : stdOrd (Fin κ) t (s + 1) 0 rfl (ixSucc _ t s r) = Sum.inl i := by simp [r]
  have hf := stdOrd_ixSucc_inl_inr_zero (κ := κ) t (s := s)
  have key : i = Sum.inl (Sum.inr 0) ↔ r = Sum.inl b' := by
    constructor
    · intro hi
      apply (ixSucc _ t s).injective
      apply (stdOrd (Fin κ) t (s + 1) 0 rfl).injective
      rw [hr, hf, hi]
    · intro hrb
      rw [hrb, hf] at hr
      exact (Sum.inl_injective hr).symm
  have hv := hent r i hr
  clear_value r
  rcases r with a | τ
  · have h1 := hgJ.2 a b' (not_freeIx_col t S.ρ a)
    have hga : g.val a b' = (S.ϖ : k) * y i := by
      rw [hg]
      exact hv
    rw [hga] at h1
    have h1' : (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t s) (Ix (Fin κ ⊕ Fin (s + 1)) t s) k) a b' =
        (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i (Sum.inl (Sum.inr 0)) := by
      simp only [Matrix.one_apply, key, Sum.inl.injEq]
    rwa [h1'] at h1
  · have h1 := hmax τ b'
    have hne : i ≠ Sum.inl (Sum.inr 0) := fun hi => by simpa using key.mp hi
    have hbot : X.toRows₂ τ b' = (S.ϖ : k) * y i := hv
    rw [hbot] at h1
    simpa [Matrix.one_apply, hne] using h1

private theorem psi_eq_psi_y0_of_sub_y0_mem_box (x₀ : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) (y : XIx (Fin κ) t (s + 1) → k)
    (hy : y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ)) :
    (S.T t).Psi 1 x₀ y = (S.T t).Psi 1 x₀ (S.y0 t) := by
  rw [S.Psi_one_eq t x₀ y, S.Psi_one_eq t x₀ (S.y0 t)]
  have hsplit : withCol x₀ ((S.ϖ : k) • y) =
      withCol x₀ ((S.ϖ : k) • S.y0 t) + withCol 0 ((S.ϖ : k) • (y - S.y0 t)) := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [withCol]
      · simp [withCol]
        ring
    · exact i.elim0
  have hw : ∀ a b, valuation k (withCol (0 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k)
      ((S.ϖ : k) • (y - S.y0 t)) a b) < 1 := by
    rintro (a | a) (b | b)
    · simp [withCol]
    · simp only [withCol, Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      exact (unif_mul_lt_one_iff S.unif _).mpr (by simpa using (mem_box.mp hy) a)
    · exact a.elim0
    · exact a.elim0
  rw [hsplit]
  have hsum : (((withCol x₀ ((S.ϖ : k) • S.y0 t) + withCol 0 ((S.ϖ : k) • (y - S.y0 t))).submatrix
      (stdOrd (Fin κ) t (s + 1) 0 rfl) (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id) =
      ((withCol x₀ ((S.ϖ : k) • S.y0 t)).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl)
        (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id +
      ((withCol 0 ((S.ϖ : k) • (y - S.y0 t))).submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl)
        (stdOrd (Fin κ) t s (0 + 1) rfl)).submatrix (ixSucc _ t s) id := by
    ext i j
    rfl
  rw [hsum]
  exact TypeDatum.Phi_add _ (S.tame (s + 1)) _ (fun i j => hw _ _)

private theorem mulVec_y0_sub_y0_mem_box_of_embX_mem_J (hP : S.Pattern t) (γ : GL (XIx (Fin κ) t (s + 1)) k)
    (hγ : embX 0 γ ∈ ((S.T t).lev (s + 1) 0 rfl).J) :
    γ.val *ᵥ S.y0 t - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ) := by
  have h1 : (typeFrame S.ϖ (stdOrd (Fin κ) t (s + 1) 0 rfl)).conj.symm (embX 0 γ) ∈
      (S.P.iter t S.μ S.tame (s + 1)).J := Level.mem_map.mp hγ
  rw [hP] at h1
  have hval : ((typeFrame S.ϖ (stdOrd (Fin κ) t (s + 1) 0 rfl)).conj.symm (embX 0 γ)).val =
      (embX 0 γ).val.submatrix (stdOrd (Fin κ) t (s + 1) 0 rfl) (stdOrd (Fin κ) t (s + 1) 0 rfl) := by
    rw [LatFrame.conj, MulEquiv.symm_trans_apply, typeFrame_bas_zero, MulAut.conj_symm_apply, inv_one, one_mul,
      mul_one, reGL_symm_val]
    rfl
  rw [mem_box]
  intro i
  set b' : Ix (Fin κ ⊕ Fin (s + 1)) t (s + 1) := Sum.inl (Sum.inr 0) with hb'
  have hb : stdOrd (Fin κ) t (s + 1) 0 rfl b' = Sum.inl (Sum.inl (Sum.inr 0)) := stdOrd_last t s
  set a := (stdOrd (Fin κ) t (s + 1) 0 rfl).symm (Sum.inl i) with ha
  have hai : stdOrd (Fin κ) t (s + 1) 0 rfl a = Sum.inl i := by simp [a]
  have h2 := h1.2 a b' (not_freeIx_col t S.ρ a)
  rw [hval, Matrix.submatrix_apply, hai, hb] at h2
  have hone : (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 1)) k) a b' =
      (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i (Sum.inl (Sum.inr 0)) := by
    have : a = b' ↔ i = Sum.inl (Sum.inr 0) := by
      rw [← (stdOrd (Fin κ) t (s + 1) 0 rfl).apply_eq_iff_eq, hai, hb, Sum.inl.injEq]
    simp only [Matrix.one_apply, this]
  rw [hone] at h2
  have hemb : (embX 0 γ).val (Sum.inl i) (Sum.inl (Sum.inl (Sum.inr 0))) = γ.val i (Sum.inl (Sum.inr 0)) := by
    simp [embX]
  rw [hemb] at h2
  have hvec : (γ.val *ᵥ S.y0 t - S.y0 t) i =
      (γ.val i (Sum.inl (Sum.inr 0)) - (1 : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t (s + 1)) k) i
        (Sum.inl (Sum.inr 0))) * ((S.ϖ⁻¹ : kˣ) : k) := by
    simp only [SymData.y0, Matrix.mulVec_single, Pi.sub_apply, Pi.single_apply, Matrix.one_apply, sub_mul]
    split_ifs <;> simp
  rw [hvec, map_mul, Units.val_one, map_one]
  have hu : valuation k ((S.ϖ⁻¹ : kˣ) : k) = (valuation k (S.ϖ : k))⁻¹ := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
  rw [hu, ← div_eq_mul_inv, div_le_one₀ (by
    rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr (Units.ne_zero S.ϖ))]
  exact (S.unif _).mp h2

theorem SymData.oneCoupling_of_pattern (hP : S.Pattern t) : S.OneCoupling t := by
  exact ⟨fun x₀ y h => sub_y0_mem_box_of_psi_ne_zero S t hP x₀ y h,
    fun x₀ y hy => psi_eq_psi_y0_of_sub_y0_mem_box S t x₀ y hy,
    fun γ hγ => mulVec_y0_sub_y0_mem_box_of_embX_mem_J S t hP γ hγ⟩

theorem oneCoupling : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.OneCoupling t := by
  intro k _ _ _ _ s κ S t _ _ hP
  exact S.oneCoupling_of_pattern t hP

end GlobalTheory.SymChain
