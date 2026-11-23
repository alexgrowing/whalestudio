import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.LayerIso

variable {n m d : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
  {U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ} {B : Fin d → Matrix (Fin n) (Fin n) ℂ} {deg : Fin d → ℕ}

theorem block_eq_zero (hU : Biorth r m U (fun b => (U b)ᴴ)) {t : ℕ} (ht : m ≤ t) : U t = 0 := by
  obtain ⟨-, h2, h3⟩ := hU
  have : U t = (∑ b ∈ range m, U b * (U b)ᴴ) * U t := by rw [h3, Matrix.one_mul]
  rw [this, Matrix.sum_mul]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hb' : b ≠ t := by have := Finset.mem_range.1 hb; omega
  rw [Matrix.mul_assoc, h2 b t hb', Matrix.mul_zero]

theorem mem_lowers_iff (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) (c : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y ∈ lowers W c ↔ ∀ s t, t ≤ s + c → (U s)ᴴ * Y * U t = 0 := by
  obtain ⟨-, h2, h3⟩ := hU
  rw [mem_lowers]
  constructor
  · intro h s t hst
    rw [Matrix.ext_iff_mulVec]
    intro x
    have hx : U t *ᵥ x ∈ W (s + c + 1) := by
      rw [hW]
      intro b hb
      rw [Matrix.mulVec_mulVec, h2 b t (by omega), Matrix.zero_mulVec]
    have := (hW _ _).1 (h s _ hx) s le_rfl
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    rw [this, Matrix.zero_mulVec]
  · intro h b y hy
    rw [hW] at hy ⊢
    intro s hs
    have : y = (∑ t ∈ range m, U t * (U t)ᴴ) *ᵥ y := by rw [h3, Matrix.one_mulVec]
    rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_sum, Matrix.sum_mulVec]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [← Matrix.mul_assoc]
    by_cases ht : t ≤ s + c
    · rw [h s t ht, Matrix.zero_mul, Matrix.zero_mulVec]
    · rw [← Matrix.mulVec_mulVec, hy t (by omega), Matrix.mulVec_zero]

theorem expand (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) (S : Set (Fin d))
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ Submodule.span ℂ (B '' S)) :
    Y = ∑ i, (Y * (B i)ᴴ).trace • B i ∧ ∀ i, i ∉ S → (Y * (B i)ᴴ).trace = 0 := by
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨by simp [hB], fun i hi => ?_⟩
    rw [hB, if_neg]
    rintro rfl
    exact hi hj
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [Matrix.add_mul, trace_add, add_smul, Finset.sum_add_distrib]
      rw [← hx.1, ← hy.1]
    · rw [Matrix.add_mul, trace_add, hx.2 i hi, hy.2 i hi, add_zero]
  | smul a x _ hx =>
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [Matrix.smul_mul, trace_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
      rw [← hx.1]
    · rw [Matrix.smul_mul, trace_smul, hx.2 i hi, smul_zero]

theorem trace_self {p q : Type} [Fintype p] [Fintype q] (A : Matrix p q ℂ) :
    (A * Aᴴ).trace = ((∑ s, ∑ t, ‖A s t‖ ^ 2 : ℝ) : ℂ) := by
  simp [Matrix.trace, Matrix.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem trace_blocks (hU : Biorth r m U (fun b => (U b)ᴴ)) (Y : Matrix (Fin n) (Fin n) ℂ) :
    (Y * Yᴴ).trace = ∑ s ∈ range m, ∑ t ∈ range m,
      (((U s)ᴴ * Y * U t) * ((U s)ᴴ * Y * U t)ᴴ).trace := by
  obtain ⟨-, -, h3⟩ := hU
  have : Y * Yᴴ = (∑ b ∈ range m, U b * (U b)ᴴ) * (Y * (∑ b ∈ range m, U b * (U b)ᴴ) * Yᴴ) := by
    rw [h3, Matrix.one_mul, Matrix.mul_one]
  rw [this, Matrix.sum_mul, trace_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.mul_assoc (U s), Matrix.trace_mul_comm]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem placed_block (hU : Biorth r m U (fun b => (U b)ᴴ)) {s t s' t' : ℕ}
    (Z : Matrix (Fin (r s)) (Fin (r t)) ℂ) (h : s' ≠ s ∨ t ≠ t') :
    (U s')ᴴ * (U s * Z * (U t)ᴴ) * U t' = 0 := by
  obtain ⟨-, h2, -⟩ := hU
  have : (U s')ᴴ * (U s * Z * (U t)ᴴ) * U t' = ((U s')ᴴ * U s) * Z * ((U t)ᴴ * U t') := by
    simp only [Matrix.mul_assoc]
  rw [this]
  rcases h with h | h
  · rw [h2 _ _ h]; simp
  · rw [h2 _ _ h]; simp

theorem placed_block_self (hU : Biorth r m U (fun b => (U b)ᴴ)) {s t : ℕ}
    (Z : Matrix (Fin (r s)) (Fin (r t)) ℂ) :
    (U s)ᴴ * (U s * Z * (U t)ᴴ) * U t = Z := by
  obtain ⟨h1, -, -⟩ := hU
  have : (U s)ᴴ * (U s * Z * (U t)ᴴ) * U t = ((U s)ᴴ * U s) * Z * ((U t)ᴴ * U t) := by
    simp only [Matrix.mul_assoc]
  rw [this, h1, h1]; simp

noncomputable def toBlocks (m : ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ)
    (B : Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ) (c : ℕ) :
    ({i : Fin d // deg i = c} → ℂ) →ₗ[ℂ] (∀ b : Fin m, Fin (r b) → Fin (r (b + c + 1)) → ℂ) where
  toFun z b s t := ((U b)ᴴ * (∑ i, z i • B i.1) * U (b + c + 1)) s t
  map_add' z w := by
    funext b s t
    simp [add_smul, Finset.sum_add_distrib, Matrix.mul_add, Matrix.add_mul]
  map_smul' a z := by
    funext b s t
    simp [mul_smul, ← Finset.smul_sum]

theorem of_toBlocks (c : ℕ) (z : {i : Fin d // deg i = c} → ℂ) (b : Fin m) :
    Matrix.of (toBlocks m U B deg c z b) = (U b)ᴴ * (∑ i, z i • B i.1) * U (b + c + 1) := rfl

theorem toBlocks_coords (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0)
    (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hL : ∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) (c : ℕ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y ∈ lowers W c) (b : Fin m) :
    Matrix.of (toBlocks m U B deg c (fun i => (Y * (B i.1)ᴴ).trace) b)
      = (U b)ᴴ * Y * U (b + c + 1) := by
  rw [of_toBlocks]
  rw [hL] at hY
  obtain ⟨h1, h2⟩ := expand hB _ hY
  conv_rhs => rw [h1]
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => deg i = c) (by simp)
    (fun i => (Y * (B i)ᴴ).trace • B i)]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  have hi' : deg i ≠ c := by simpa using hi
  by_cases hc : c ≤ deg i
  · have : B i ∈ lowers W (c + 1) := by
      rw [hL]
      exact Submodule.subset_span ⟨i, by show c + 1 ≤ deg i; omega, rfl⟩
    rw [Matrix.mul_smul, Matrix.smul_mul,
      (mem_lowers_iff hU hW _ _).1 this b (b + c + 1) (by omega), smul_zero]
  · rw [h2 i hc]; simp

theorem toBlocks_surjective (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0)
    (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hL : ∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) (c : ℕ) :
    Function.Surjective (toBlocks m U B deg c) := by
  intro Z
  set Y : Matrix (Fin n) (Fin n) ℂ :=
    ∑ b : Fin m, U b * Matrix.of (Z b) * (U (b + c + 1))ᴴ with hYdef
  have hY : Y ∈ lowers W c := by
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [mem_lowers_iff hU hW]
    intro s t hst
    exact placed_block hU _ (by omega)
  refine ⟨fun i => (Y * (B i.1)ᴴ).trace, funext fun b => ?_⟩
  apply Matrix.of.injective
  rw [toBlocks_coords hU hW hB hL c Y hY b, hYdef, Matrix.mul_sum, Matrix.sum_mul,
    Finset.sum_eq_single b]
  · exact placed_block_self hU _
  · intro b' _ hb
    exact placed_block hU _ (Or.inl fun h => hb (Fin.ext h.symm))
  · simp

theorem toBlocks_norm (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0)
    (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hL : ∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) (c : ℕ)
    (z : {i : Fin d // deg i = c} → ℂ) :
    ∑ b, ∑ s, ∑ t, ‖toBlocks m U B deg c z b s t‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  set Y : Matrix (Fin n) (Fin n) ℂ := ∑ i, z i • B i.1 with hYdef
  have hY : Y ∈ lowers W c := by
    rw [hL]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i.1, i.2.ge, rfl⟩)
  have h1 : (Y * Yᴴ).trace = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
    simp [hYdef, conjTranspose_sum, Matrix.mul_sum, Matrix.sum_mul, trace_sum, hB,
      Subtype.val_inj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.conj_mul']
  have horth : ∀ X ∈ lowers W (c + 1), (X * Yᴴ).trace = 0 := by
    intro X hX
    rw [hL] at hX
    have h2 := (expand hB _ hX).2
    rw [hYdef, conjTranspose_sum, Matrix.mul_sum, trace_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [conjTranspose_smul, Matrix.mul_smul, trace_smul, h2 i.1, smul_zero]
    have := i.2
    show ¬ (c + 1 ≤ deg i.1)
    omega
  have h2 : (Y * Yᴴ).trace = ∑ s ∈ range m,
      (((U s)ᴴ * Y * U (s + c + 1)) * ((U s)ᴴ * Y * U (s + c + 1))ᴴ).trace := by
    rw [trace_blocks hU]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_eq_single _ (fun t _ ht => ?_) (fun h => ?_)
    · by_cases hst : t ≤ s + c
      · rw [(mem_lowers_iff hU hW _ _).1 hY s t hst]; simp
      · have hX : U s * ((U s)ᴴ * Y * U t) * (U t)ᴴ ∈ lowers W (c + 1) := by
          rw [mem_lowers_iff hU hW]
          intro s' t' h'
          exact placed_block hU _ (by omega)
        rw [← horth _ hX, Matrix.mul_assoc (U s), Matrix.mul_assoc (U s), Matrix.trace_mul_comm (U s)]
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    · rw [block_eq_zero hU (t := s + c + 1) (by simpa using h)]; simp
  rw [h2, ← Fin.sum_univ_eq_sum_range
    (fun s => (((U s)ᴴ * Y * U (s + c + 1)) * ((U s)ᴴ * Y * U (s + c + 1))ᴴ).trace)] at h1
  simp only [trace_self] at h1
  rw [← Complex.ofReal_sum] at h1
  exact Complex.ofReal_injective h1

theorem exists_layerIso : ∀ (n m d : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (B : Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ), Biorth r m U (fun b => (U b)ᴴ) → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) → (∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) → (∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) → ∀ c : ℕ, ∃ Φ : ({i : Fin d // deg i = c} → ℂ) ≃ₗ[ℂ] (∀ b : Fin m, Fin (r b) → Fin (r (b + c + 1)) → ℂ), (∀ z, ∑ b, ∑ s, ∑ t, ‖Φ z b s t‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) ∧ ∀ Y ∈ lowers W c, ∀ b : Fin m, Matrix.of (Φ (fun i => (Y * (B i.1)ᴴ).trace) b) = (U b)ᴴ * Y * U (b + c + 1) := by
  intro n m d W r U B deg hU hW hB hL c
  have hinj : Function.Injective (toBlocks m U B deg c) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have h := toBlocks_norm hU hW hB hL c z
    rw [hz] at h
    have h0 : ∑ i, ‖z i‖ ^ 2 = 0 := by rw [← h]; simp
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)] at h0
    funext i
    simpa using h0 i (Finset.mem_univ i)
  exact ⟨LinearEquiv.ofBijective _ ⟨hinj, toBlocks_surjective hU hW hB hL c⟩,
    toBlocks_norm hU hW hB hL c, toBlocks_coords hU hW hB hL c⟩

end GlobalTheory.LayerIso
