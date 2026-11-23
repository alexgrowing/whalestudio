import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry

open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore

noncomputable section
namespace GlobalTheory.NormalCore.Normalize

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Bdd {A B : Type} (c : ValueGroupWithZero k) (X : Matrix A B k) : Prop := ∀ i j, valuation k (X i j) ≤ c

theorem bdd_mul {A B C : Type} [Fintype B] {c c' : ValueGroupWithZero k} {X : Matrix A B k} {Y : Matrix B C k}
    (hX : Bdd c X) (hY : Bdd c' Y) : Bdd (c * c') (X * Y) := fun i j =>
  Valuation.map_sum_le _ fun l _ => by rw [map_mul]; exact mul_le_mul' (hX i l) (hY l j)

theorem bdd_add {A B : Type} {c : ValueGroupWithZero k} {X Y : Matrix A B k} (hX : Bdd c X) (hY : Bdd c Y) :
    Bdd c (X + Y) := fun i j => Valuation.map_add_le _ (hX i j) (hY i j)

theorem bdd_sub {A B : Type} {c : ValueGroupWithZero k} {X Y : Matrix A B k} (hX : Bdd c X) (hY : Bdd c Y) :
    Bdd c (X - Y) := fun i j => Valuation.map_sub_le _ (hX i j) (hY i j)

theorem bdd_mono {A B : Type} {c c' : ValueGroupWithZero k} {X : Matrix A B k} (hX : Bdd c X) (h : c ≤ c') :
    Bdd c' X := fun i j => (hX i j).trans h

theorem bdd_one {A : Type} [DecidableEq A] : Bdd (1 : ValueGroupWithZero k) (1 : Matrix A A k) := fun i j => by
  rw [one_apply]; split_ifs <;> simp

theorem bdd_vecMulVec {A B : Type} {c c' : ValueGroupWithZero k} {a : A → k} {b : B → k}
    (ha : ∀ i, valuation k (a i) ≤ c) (hb : ∀ j, valuation k (b j) ≤ c') : Bdd (c * c') (vecMulVec a b) :=
  fun i j => by rw [vecMulVec_apply, map_mul]; exact mul_le_mul' (ha i) (hb j)

theorem bdd_transpose {A B : Type} {c : ValueGroupWithZero k} {X : Matrix A B k} (hX : Bdd c X) : Bdd c Xᵀ :=
  fun i j => hX j i

theorem val_single_le_one {A : Type} [DecidableEq A] (a : A) (j : A) :
    valuation k ((Pi.single a (1 : k) : A → k) j) ≤ 1 := by
  by_cases h : j = a
  · subst h; simp
  · simp [h]

theorem exists_inv_of_bdd_sub_one {n : Type} [Fintype n] [DecidableEq n] {ϖ : kˣ} (hϖ : IsUnif ϖ)
    (M : Matrix n n k) (hM : Bdd (valuation k (ϖ : k)) (M - 1)) : ∃ N : Matrix n n k, Bdd 1 N ∧ M * N = 1 := by
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hint : ∀ i j, M i j ∈ 𝒪[k] := fun i j => by
    have := bdd_add (bdd_mono hM hlt.le) (bdd_one (k := k)) i j
    rw [sub_add_cancel] at this
    exact this
  let M' : Matrix n n 𝒪[k] := Matrix.of fun i j => ⟨M i j, hint i j⟩
  have hM' : (𝒪[k]).subtype.mapMatrix M' = M := by ext i j; rfl
  have hmem : ∀ i j, M' i j - (1 : Matrix n n 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := fun i j => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    have e : ((M' i j - (1 : Matrix n n 𝒪[k]) i j : 𝒪[k]) : k) = (M - 1) i j := by
      simp only [M', Matrix.sub_apply, one_apply, of_apply]; split_ifs <;> simp
    exact lt_of_le_of_lt (e ▸ hM i j) hlt
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix M' = 1 := by
    ext i j
    have := (IsLocalRing.residue_eq_zero_iff _).2 (hmem i j)
    rw [map_sub, sub_eq_zero] at this
    simp only [RingHom.mapMatrix_apply, map_apply, this]
    rw [one_apply, one_apply]; split_ifs <;> simp
  have hdet : IsUnit M'.det := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro h
    have h1 : IsLocalRing.residue 𝒪[k] M'.det = 1 := by rw [RingHom.map_det, hres, det_one]
    rw [(IsLocalRing.residue_eq_zero_iff _).2 h] at h1
    exact zero_ne_one h1
  obtain ⟨U, hU⟩ := (Matrix.isUnit_iff_isUnit_det M').2 hdet
  refine ⟨(𝒪[k]).subtype.mapMatrix (U⁻¹ : (Matrix n n 𝒪[k])ˣ).val, fun i j => ((U⁻¹).val i j).2, ?_⟩
  rw [← hM', ← hU, ← map_mul, Units.mul_inv, map_one]

theorem bdd_smul {k : Type} [Field k] [ValuativeRel k] {A B : Type} {c : ValueGroupWithZero k} {X : Matrix A B k} (hX : Bdd c X)
    {a : k} (ha : valuation k a ≤ 1) : Bdd c (a • X) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]; exact (mul_le_mul' ha (hX i j)).trans_eq (one_mul _)

theorem normalize (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (i₀ : Fin n) (j₀ : Fin d) (ϖ : kˣ) (hϖ : IsUnif ϖ) (p₁ p₂ : Matrix (Fin n) (Fin d) k)
    (hp₁ : ∀ i j, valuation k (p₁ i j) ≤ 1) (hr : ∀ j, p₁ i₀ j = if j = j₀ then 1 else 0)
    (hc : ∀ i, i ≠ i₀ → p₁ i j₀ = 0) (hp₂ : ∀ i, p₂ i j₀ = 0)
    (hS : ∃ S : Matrix (Fin d) (Fin n) k, (∀ j i, valuation k (S j i) ≤ 1) ∧ (∀ i, S j₀ i = 0) ∧ p₂ * S = 1) :
    ∀ Z₁ ∈ box ϖ p₁ (fun _ => 1), ∀ Z₂ ∈ box ϖ p₂ (fun _ => 1), ∃ (g : GL (Fin n) k) (h : GL (Fin d) k),
      (∀ i j, valuation k (g.1 i j) ≤ 1) ∧ (∀ i j, valuation k ((g⁻¹).1 i j) ≤ 1) ∧
      (∀ i j, valuation k (h.1 i j) ≤ 1) ∧ (∀ i j, valuation k ((h⁻¹).1 i j) ≤ 1) ∧
      (∀ i j, valuation k (((g.1)ᵀ * Z₁ * h.1) i j) ≤ 1) ∧
      (∀ j, ((g.1)ᵀ * Z₁ * h.1) i₀ j = if j = j₀ then 1 else 0) ∧
      (∀ i, i ≠ i₀ → ((g.1)ᵀ * Z₁ * h.1) i j₀ = 0) ∧ (∀ i, (Z₂ * h.1) i j₀ = 0) ∧
      ∃ S' : Matrix (Fin d) (Fin n) k, (∀ j i, valuation k (S' j i) ≤ 1) ∧ (∀ i, S' j₀ i = 0) ∧
        Z₂ * h.1 * S' = 1 := by
  intro Z₁ hZ₁ Z₂ hZ₂
  obtain ⟨S, hSi, hS0, hpS⟩ := hS
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hZ₁' : Bdd (valuation k (ϖ : k)) (Z₁ - p₁) := fun i j => by simpa using hZ₁ i j
  have hZ₂' : Bdd (valuation k (ϖ : k)) (Z₂ - p₂) := fun i j => by simpa using hZ₂ i j
  have hZ₁i : Bdd 1 Z₁ := by
    have := bdd_add (bdd_mono hZ₁' hlt.le) hp₁; rwa [sub_add_cancel] at this

  obtain ⟨e, he⟩ : ∃ e : Fin d → k, e = Pi.single j₀ 1 := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : Fin d → k, ε = fun b => Z₁ i₀ b - p₁ i₀ b := ⟨_, rfl⟩
  have hεb : ∀ b, valuation k (ε b) ≤ valuation k (ϖ : k) := fun b => by rw [hε]; exact hZ₁' i₀ b
  have hz : Z₁ i₀ = e + ε := by
    funext b; rw [he, hε]; simp only [Pi.add_apply, hr, Pi.single_apply]; ring
  have hej : ∀ b, valuation k (e b) ≤ 1 := fun b => he ▸ val_single_le_one j₀ b
  obtain ⟨u, hu⟩ : ∃ u, u = Z₁ i₀ j₀ := ⟨_, rfl⟩
  have hεj : ε j₀ = u - 1 := by rw [hε, hu]; simp [hr]
  have hv : valuation k u = 1 := by
    rw [← map_one (valuation k)]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [map_one, ← hεj]; exact (hεb j₀).trans_lt hlt
  have hu0 : u ≠ 0 := fun h => by simp [h] at hv
  have hvi : valuation k u⁻¹ = 1 := by rw [map_inv₀, hv, inv_one]

  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin d) (Fin d) k, X = vecMulVec e ε := ⟨_, rfl⟩
  have hXX : X * X = (u - 1) • X := by
    rw [hX, vecMulVec_mul_vecMulVec, he, dotProduct_single, mul_one, ← he, hεj]
    ext a b; simp [vecMulVec_apply]; ring
  have hXb : Bdd 1 X := by
    have := bdd_vecMulVec hej (fun b => (hεb b).trans hlt.le); rw [mul_one] at this; rwa [hX]
  have h1m : (1 - u⁻¹ • X) * (1 + X) = 1 := by
    have e1 : (1 : k) - u⁻¹ - u⁻¹ * (u - 1) = 0 := by field_simp; ring
    have key : (1 - u⁻¹ • X) * (1 + X) = 1 + ((1 : k) - u⁻¹ - u⁻¹ * (u - 1)) • X := by
      simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_assoc, hXX, smul_smul]; module
    rw [key, e1, zero_smul, add_zero]
  have hzH1 : Z₁ i₀ ᵥ* (1 - u⁻¹ • X) = e := by
    rw [vecMul_sub, vecMul_one, vecMul_smul, hX, vecMul_vecMulVec, he, dotProduct_single, mul_one, ← hu,
      smul_smul, inv_mul_cancel₀ hu0, one_smul, hz, ← he]; abel

  obtain ⟨A, hA⟩ : ∃ A, A = Z₂ * (1 - u⁻¹ • X) := ⟨_, rfl⟩
  have hAZ : A - Z₂ = -(u⁻¹ • vecMulVec (Z₂ *ᵥ e) ε) := by
    rw [hA, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hX, mul_vecMulVec]; abel
  have hZ₂c : ∀ i, valuation k (Z₂ i j₀) ≤ valuation k (ϖ : k) := fun i => by
    simpa [hp₂] using hZ₂' i j₀
  have hAZb : Bdd (valuation k (ϖ : k)) (A - Z₂) := fun i b => by
    rw [hAZ, Matrix.neg_apply, Valuation.map_neg, Matrix.smul_apply, smul_eq_mul, map_mul, hvi, one_mul, vecMulVec_apply,
      map_mul, he, mulVec_single_one, col_apply]
    exact (mul_le_mul' (hZ₂c i) ((hεb b).trans hlt.le)).trans_eq (mul_one _)
  have hAp : Bdd (valuation k (ϖ : k)) (A - p₂) := by
    have := bdd_add hAZb hZ₂'; rwa [sub_add_sub_cancel] at this
  have hAc : ∀ i, valuation k (A i j₀) ≤ valuation k (ϖ : k) := fun i => by
    simpa [hp₂] using hAp i j₀

  have hM : Bdd (valuation k (ϖ : k)) (A * S - 1) := by
    have := bdd_mul hAp (c' := 1) hSi; rw [mul_one, Matrix.sub_mul, hpS] at this; exact this
  obtain ⟨N, hNb, hMN⟩ := exists_inv_of_bdd_sub_one hϖ _ hM
  obtain ⟨S', hS'⟩ : ∃ S', S' = S * N := ⟨_, rfl⟩
  have hS'b : Bdd 1 S' := by have := bdd_mul (c := 1) hSi hNb; rw [mul_one] at this; rwa [hS']
  have hS'0 : ∀ i, S' j₀ i = 0 := fun i => by rw [hS', mul_apply]; simp [hS0]
  have hS'r : S'.row j₀ = 0 := funext hS'0
  have hAS : A * S' = 1 := by rw [hS', ← Matrix.mul_assoc, hMN]

  obtain ⟨s, hs⟩ : ∃ s, s = S' *ᵥ (A *ᵥ e) := ⟨_, rfl⟩
  have hs0 : s j₀ = 0 := by rw [hs]; show ∑ l, S' j₀ l * (A *ᵥ e) l = 0; simp [hS'0]
  have hsb : ∀ j, valuation k (s j) ≤ 1 := fun j => by
    rw [hs]; show valuation k (∑ l, S' j l * (A *ᵥ e) l) ≤ 1
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul, he, mulVec_single_one, col_apply]
    exact (mul_le_mul' (hS'b j l) ((hAc l).trans hlt.le)).trans_eq (one_mul _)
  obtain ⟨Y2, hY2⟩ : ∃ Y2 : Matrix (Fin d) (Fin d) k, Y2 = vecMulVec s e := ⟨_, rfl⟩
  have hes : e ⬝ᵥ s = 0 := by rw [he, single_dotProduct, one_mul, hs0]
  have hYY : Y2 * Y2 = 0 := by
    rw [hY2, vecMulVec_mul_vecMulVec, hes, zero_smul]; ext a b; simp [vecMulVec_apply]
  have h2m : (1 - Y2) * (1 + Y2) = 1 := by simp [sub_mul, mul_add, hYY]
  have hY2b : Bdd 1 Y2 := by
    have := bdd_vecMulVec hsb hej; rw [mul_one] at this; rwa [hY2]
  have hAs : A *ᵥ s = A *ᵥ e := by rw [hs, mulVec_mulVec, hAS, one_mulVec]
  have hAH2 : ∀ i, (A * (1 - Y2 : Matrix (Fin d) (Fin d) k)) i j₀ = 0 := fun i => by
    rw [Matrix.mul_sub, Matrix.mul_one, hY2, mul_vecMulVec, hAs, Matrix.sub_apply, vecMulVec_apply, he,
      mulVec_single_one, col_apply]
    simp
  have hH2S : (1 - Y2) * S' = S' := by
    have h0 : e ᵥ* S' = 0 := by rw [he, single_one_vecMul, hS'r]
    rw [Matrix.sub_mul, Matrix.one_mul, hY2, vecMulVec_mul, h0]
    ext a b; simp [vecMulVec_apply]
  have hzh : Z₁ i₀ ᵥ* ((1 - u⁻¹ • X) * (1 - Y2)) = e := by
    rw [← vecMul_vecMul, hzH1, vecMul_sub, vecMul_one, hY2, vecMul_vecMulVec, hes, zero_smul, sub_zero]

  have hH1b : Bdd 1 (1 - u⁻¹ • X) := bdd_sub bdd_one (bdd_smul hXb hvi.le)
  have hH1ib : Bdd 1 (1 + X) := bdd_add bdd_one hXb
  have hH2b : Bdd 1 (1 - Y2) := bdd_sub bdd_one hY2b
  have hH2ib : Bdd 1 (1 + Y2) := bdd_add bdd_one hY2b
  have hhm : (1 - u⁻¹ • X) * (1 - Y2) * ((1 + Y2) * (1 + X)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Y2), h2m, Matrix.one_mul, h1m]
  let hG : GL (Fin d) k := ⟨(1 - u⁻¹ • X) * (1 - Y2), (1 + Y2) * (1 + X), hhm, mul_eq_one_comm.1 hhm⟩
  have hGb : Bdd 1 hG.1 := by have := bdd_mul hH1b hH2b; rwa [mul_one] at this
  have hGib : Bdd 1 (hG⁻¹).1 := by have := bdd_mul hH2ib hH1ib; rwa [mul_one] at this

  obtain ⟨Y, hY⟩ : ∃ Y, Y = Z₁ * hG.1 := ⟨_, rfl⟩
  have hYb : Bdd 1 Y := by have := bdd_mul hZ₁i hGb; rw [mul_one] at this; rwa [hY]
  have hYr : ∀ j, Y i₀ j = e j := fun j => by rw [← hzh, hY]; rfl
  obtain ⟨c, hc'⟩ : ∃ c : Fin n → k, c = fun i => if i = i₀ then 0 else Y i j₀ := ⟨_, rfl⟩
  have hcb : ∀ i, valuation k (c i) ≤ 1 := fun i => by
    rw [hc']; dsimp only; split_ifs
    · simp
    · exact hYb i j₀
  obtain ⟨ei, hei⟩ : ∃ ei : Fin n → k, ei = Pi.single i₀ 1 := ⟨_, rfl⟩
  have heib : ∀ i, valuation k (ei i) ≤ 1 := fun i => hei ▸ val_single_le_one i₀ i
  obtain ⟨Xg, hXg⟩ : ∃ Xg : Matrix (Fin n) (Fin n) k, Xg = vecMulVec ei c := ⟨_, rfl⟩
  have hce : c ⬝ᵥ ei = 0 := by rw [hei, dotProduct_single, mul_one, hc']; simp
  have hXgg : Xg * Xg = 0 := by
    rw [hXg, vecMulVec_mul_vecMulVec, hce, zero_smul]; ext a b; simp [vecMulVec_apply]
  have hgm : (1 - Xg) * (1 + Xg) = 1 := by simp [sub_mul, mul_add, hXgg]
  have hXgb : Bdd 1 Xg := by
    have := bdd_vecMulVec heib hcb; rw [mul_one] at this; rwa [hXg]
  let gG : GL (Fin n) k := ⟨1 - Xg, 1 + Xg, hgm, mul_eq_one_comm.1 hgm⟩
  have hF : (gG.1)ᵀ * Z₁ * hG.1 = Y - vecMulVec c e := by
    have h0 : ei ᵥ* Y = e := by rw [hei, single_one_vecMul]; funext j; exact hYr j
    show (1 - Xg)ᵀ * Z₁ * hG.1 = _
    rw [Matrix.mul_assoc, ← hY, transpose_sub, transpose_one, hXg, transpose_vecMulVec, Matrix.sub_mul,
      Matrix.one_mul, vecMulVec_mul, h0]
  refine ⟨gG, hG, bdd_sub bdd_one hXgb, bdd_add bdd_one hXgb, hGb, hGib, ?_, ?_, ?_, ?_, S', hS'b, hS'0, ?_⟩
  · have := bdd_mul (bdd_mul (bdd_transpose (bdd_sub bdd_one hXgb)) hZ₁i) hGb
    rw [mul_one, mul_one] at this; exact this
  · intro j
    rw [hF, Matrix.sub_apply, vecMulVec_apply, hYr, hc', he]
    simp [Pi.single_apply]
  · intro i hi
    rw [hF, Matrix.sub_apply, vecMulVec_apply, hc', he]
    simp [hi]
  · intro i
    show ((Z₂ * ((1 - u⁻¹ • X) * (1 - Y2)) : Matrix (Fin n) (Fin d) k)) i j₀ = 0
    rw [← Matrix.mul_assoc, ← hA]; exact hAH2 i
  · show Z₂ * ((1 - u⁻¹ • X) * (1 - Y2)) * S' = 1
    rw [← Matrix.mul_assoc, ← hA, Matrix.mul_assoc, hH2S, hAS]

end GlobalTheory.NormalCore.Normalize
