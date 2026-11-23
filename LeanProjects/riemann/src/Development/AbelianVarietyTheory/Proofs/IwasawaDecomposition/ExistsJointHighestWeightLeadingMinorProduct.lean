import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.FischerSelfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe

noncomputable section

open MvPolynomial Matrix

namespace GlobalTheory.CompactHowe.Minors

variable {N n : ℕ}

def IsBorelVec (hn : n ≤ N) (ν : Fin N → ℕ) (Δ : MvPolynomial (Fin N × Fin n) ℂ) : Prop :=
  Δ ≠ 0 ∧ ∀ (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ),
    (∀ i j, j < i → h i j = 0) → (∀ i j, j < i → g i j = 0) →
      subst2 h g Δ = ((∏ b, h b b ^ ν b) * ∏ a, g a a ^ ν (Fin.castLE hn a)) • Δ

theorem isBorelVec_one (hn : n ≤ N) : IsBorelVec hn (fun _ => 0) 1 :=
  ⟨one_ne_zero, fun h g _ _ => by simp⟩

theorem IsBorelVec.mul {hn : n ≤ N} {ν μ : Fin N → ℕ} {Δ Γ : MvPolynomial (Fin N × Fin n) ℂ}
    (h1 : IsBorelVec hn ν Δ) (h2 : IsBorelVec hn μ Γ) : IsBorelVec hn (fun b => ν b + μ b) (Δ * Γ) := by
  refine ⟨mul_ne_zero h1.1 h2.1, fun h g hh hg => ?_⟩
  rw [map_mul, h1.2 h g hh hg, h2.2 h g hh hg, smul_mul_smul_comm]
  congr 1
  simp only [pow_add, Finset.prod_mul_distrib]
  ring

theorem not_range_castLE {k m : ℕ} (hk : k ≤ m) (i : Fin m) (hi : i ∉ Set.range (Fin.castLE hk)) : k ≤ (i : ℕ) := by
  by_contra hc
  exact hi ⟨⟨i, by omega⟩, Fin.ext rfl⟩

theorem sum_castLE {M : Type*} [AddCommMonoid M] {k m : ℕ} (hk : k ≤ m) (f : Fin m → M)
    (hf : ∀ i : Fin m, k ≤ (i : ℕ) → f i = 0) : ∑ i, f i = ∑ i : Fin k, f (Fin.castLE hk i) :=
  (Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ f
    (fun i hi => hf i (not_range_castLE hk i hi)) fun _ => rfl).symm

theorem prod_pow_ite {k m : ℕ} (hk : k ≤ m) (c : Fin m → ℂ) :
    ∏ i, c i ^ (if (i : ℕ) < k then 1 else 0) = ∏ i : Fin k, c (Fin.castLE hk i) :=
  (Fintype.prod_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _
    (fun i hi => by rw [if_neg (not_lt.2 (not_range_castLE hk i hi)), pow_zero])
    fun i => by simp).symm

def block (hn : n ≤ N) {k : ℕ} (hk : k ≤ n) : Matrix (Fin k) (Fin k) (MvPolynomial (Fin N × Fin n) ℂ) :=
  Matrix.of fun i j => X (Fin.castLE (hk.trans hn) i, Fin.castLE hk j)

theorem det_block_ne_zero (hn : n ≤ N) {k : ℕ} (hk : k ≤ n) : (block hn hk).det ≠ 0 := by
  intro h0
  have h1 := (eval (fun p : Fin N × Fin n => if (p.1 : ℕ) = (p.2 : ℕ) then (1 : ℂ) else 0)).map_det (block hn hk)
  have h2 : (eval (fun p : Fin N × Fin n => if (p.1 : ℕ) = (p.2 : ℕ) then (1 : ℂ) else 0)).mapMatrix (block hn hk) = 1 := by
    ext i j
    simp [block, Matrix.one_apply, Fin.ext_iff]
  rw [h2, h0] at h1
  simp at h1

theorem det_lead {k m : ℕ} (hk : k ≤ m) (g : Matrix (Fin m) (Fin m) ℂ) (hg : ∀ i j, j < i → g i j = 0) :
    (g.submatrix (Fin.castLE hk) (Fin.castLE hk)).det = ∏ i : Fin k, g (Fin.castLE hk i) (Fin.castLE hk i) := by
  rw [Matrix.det_of_upperTriangular]
  · rfl
  · intro i j hij
    exact hg _ _ hij

theorem isBorelVec_det (hn : n ≤ N) {k : ℕ} (hk : k ≤ n) :
    IsBorelVec hn (fun b => if (b : ℕ) < k then 1 else 0) (block hn hk).det := by
  refine ⟨det_block_ne_zero hn hk, fun h g hh hg => ?_⟩
  have key : (subst2 h g).mapMatrix (block hn hk) =
      ((C : ℂ →+* _).mapMatrix (h.submatrix (Fin.castLE (hk.trans hn)) (Fin.castLE (hk.trans hn))))ᵀ * block hn hk *
        (C : ℂ →+* _).mapMatrix (g.submatrix (Fin.castLE hk) (Fin.castLE hk)) := by
    ext1 i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, block, Matrix.of_apply, subst2_X, Matrix.mul_apply,
      Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.submatrix_apply, Finset.sum_mul]
    rw [sum_castLE (hk.trans hn), Finset.sum_comm]
    · rw [sum_castLE hk]
      · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
        rw [map_mul]; ring
      · intro l hl
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [hg l _ (by rw [Fin.lt_def]; have := j.2; simp only [Fin.val_castLE]; omega)]
        simp
    · intro l hl
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [hh l _ (by rw [Fin.lt_def]; have := i.2; simp only [Fin.val_castLE]; omega)]
      simp
  rw [AlgHom.map_det, key, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, ← RingHom.map_det,
    det_lead _ _ hh, det_lead _ _ hg, prod_pow_ite (hk.trans hn) (fun b => h b b)]
  simp only [Fin.val_castLE]
  rw [prod_pow_ite hk (fun b => g b b), smul_eq_C_mul, map_mul]
  ring

theorem exists_isBorelVec (hn : n ≤ N) (M : ℕ) : ∀ ν : Fin N → ℕ, (∀ b, ν b ≤ M) → Antitone ν →
    (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → ∃ Δ, IsBorelVec hn ν Δ := by
  classical
  induction M with
  | zero =>
    intro ν hM _ _
    obtain rfl : ν = fun _ => 0 := funext fun b => Nat.le_zero.1 (hM b)
    exact ⟨1, isBorelVec_one hn⟩
  | succ M ih =>
    intro ν hM ha h0
    obtain ⟨Γ, hΓ⟩ := ih (fun b => ν b - 1) (fun b => by have := hM b; omega)
      (fun a b hab => Nat.sub_le_sub_right (ha hab) 1) (fun b hb => by simp [h0 b hb])
    have hex : ∃ k : ℕ, ∀ b : Fin N, k ≤ (b : ℕ) → ν b = 0 := ⟨n, h0⟩
    have hk : Nat.find hex ≤ n := Nat.find_min' hex h0
    refine ⟨(block hn hk).det * Γ, ?_⟩
    have := (isBorelVec_det hn hk).mul hΓ
    convert this using 2 with b
    split_ifs with hb
    · have h1 := Nat.find_min hex hb
      push Not at h1
      obtain ⟨c, hc, hc0⟩ := h1
      have : ν c ≤ ν b := ha (Fin.le_def.2 hc)
      omega
    · have := Nat.find_spec hex b (not_lt.1 hb)
      omega

theorem exists_highestWeight (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (ha : Antitone ν)
    (h0 : ∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) :
    ∃ Δ : MvPolynomial (Fin N × Fin n) ℂ, Δ ≠ 0 ∧
      (∀ h g, ReciprocityTheory.PGsh.IsUpperUnitri h → ReciprocityTheory.PGsh.IsUpperUnitri g → subst2 h g Δ = Δ) ∧
      ∀ (d : Fin N → ℂ) (e : Fin n → ℂ), subst2 (Matrix.diagonal d) (Matrix.diagonal e) Δ =
        ((∏ b, d b ^ ν b) * ∏ a, e a ^ ν (Fin.castLE hn a)) • Δ := by
  obtain ⟨Δ, h1, h2⟩ := exists_isBorelVec hn (∑ b, ν b) ν
    (fun b => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)) ha h0
  refine ⟨Δ, h1, fun h g hh hg => ?_, fun d e => ?_⟩
  · rw [h2 h g hh.2 hg.2]
    simp [hh.1, hg.1]
  · rw [h2 _ _ (fun i j hij => Matrix.diagonal_apply_ne _ hij.ne') (fun i j hij => Matrix.diagonal_apply_ne _ hij.ne')]
    simp

end GlobalTheory.CompactHowe.Minors

end
