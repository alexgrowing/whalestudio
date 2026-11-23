import Mathlib
import Development.WeilBound.ThetaLifts.LocalTheory.ConeShifts.ExistsPowIdem

noncomputable section

namespace GlobalTheory.ThK.Dbl.Vf2

open Matrix GlobalTheory.WeilM PositivityTheory.ThKG.Loc.Cone.Vf

section Skew

variable {A K β : Type} [CommRing A] [Field K] [Fintype β] [DecidableEq β]

omit [DecidableEq β] in
theorem rank_lt {M : Matrix β β K} {y w φ : β → K} (hy : M *ᵥ y = 0) (hw : w ∉ LinearMap.range M.mulVecLin) (hφ : φ ⬝ᵥ y ≠ 0) :
    M.rank < (M + vecMulVec w φ).rank := by
  have e : ∀ x, (M + vecMulVec w φ) *ᵥ x = M *ᵥ x + (φ ⬝ᵥ x) • w := fun x => by
    rw [add_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  have h1 : w ∈ LinearMap.range (M + vecMulVec w φ).mulVecLin := ⟨(φ ⬝ᵥ y)⁻¹ • y, by
    rw [mulVecLin_apply, mulVec_smul, e, hy, zero_add, smul_smul, inv_mul_cancel₀ hφ, one_smul]⟩
  refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne ?_ fun h => hw (h ▸ h1))
  rintro _ ⟨x, rfl⟩
  rw [mulVecLin_apply, eq_sub_of_add_eq (e x).symm]
  exact sub_mem ⟨x, rfl⟩ (Submodule.smul_mem _ _ h1)

variable {c : A →+* A} {r : A →+* K} {G G' M m P Q : Matrix β β A}

omit [DecidableEq β] in
theorem skew_two (hc : ∀ z, c (c z) = z) (hG : ∀ i j, c (G j i) = G i j) (u w : β → A) :
    (vecMulVec u (G *ᵥ c ∘ w) - vecMulVec w (G *ᵥ c ∘ u))ᵀ * G +
      G * (vecMulVec u (G *ᵥ c ∘ w) - vecMulVec w (G *ᵥ c ∘ u)).map c = 0 := by
  have k : ∀ u w : β → A, (vecMulVec u (G *ᵥ c ∘ w))ᵀ * G = G * (vecMulVec w (G *ᵥ c ∘ u)).map c := fun u w => by
    ext i j
    simp only [mul_apply, transpose_apply, vecMulVec_apply, map_apply, map_mul, mulVec, dotProduct, map_sum, hc, hG,
      Function.comp_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [transpose_sub, Matrix.sub_mul, Matrix.map_sub _ (map_sub c), Matrix.mul_sub, k, k]
  abel

theorem step (hc : ∀ z, c (c z) = z) (hr : Function.Surjective r) (hG : ∀ i j, c (G j i) = G i j) (hG' : G * G' = 1)
    (hcase : ((∀ z, r z = 0 → r (c z) = 0) ∧ ∃ κ, r (κ - c κ) ≠ 0) ∨ ∃ η, r η = 1 ∧ r (c η) = 0)
    (lag : Mᵀ * G * m.map c + mᵀ * G * M.map c = 0) (inj : P * M + Q * m = 1) (h0 : (M.map r).det = 0) :
    ∃ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 ∧ (M.map r).rank < ((M + S * m).map r).rank := by
  have mv : ∀ (N : Matrix β β A) x, N.map r *ᵥ r ∘ x = r ∘ (N *ᵥ x) := fun N x => funext fun i => (r.map_mulVec N x i).symm
  have mc : ∀ (N : Matrix β β A) x, N.map c *ᵥ c ∘ x = c ∘ (N *ᵥ x) := fun N x => funext fun i => (c.map_mulVec N x i).symm
  obtain ⟨y₀, hy0, hy⟩ := exists_mulVec_eq_zero_iff.2 h0
  obtain ⟨y, rfl⟩ := hr.comp_left y₀
  obtain ⟨i, hi⟩ : ∃ i, r ((m *ᵥ y) i) ≠ 0 := by
    by_contra h
    push Not at h
    have := congrArg (fun N : Matrix β β A => N.map r *ᵥ r ∘ y) inj
    simp only [Matrix.map_add _ (map_add r), Matrix.map_mul, add_mulVec, ← mulVec_mulVec, hy, mulVec_zero,
      Matrix.map_one _ (map_zero r) (map_one r), one_mulVec] at this
    rw [mv m, show r ∘ (m *ᵥ y) = 0 from funext h, mulVec_zero, add_zero] at this
    exact hy0 this.symm
  let w : β → A := c ∘ (G' *ᵥ Pi.single i 1)
  have hw : G *ᵥ c ∘ w = Pi.single i 1 := by
    rw [show c ∘ w = G' *ᵥ Pi.single i 1 from funext fun _ => hc _, mulVec_mulVec, hG', one_mulVec]
  have fin : ∀ (u : β → A) (z : β → K), (∀ a b, r (u a * (Pi.single i 1 : β → A) b - w a * (G *ᵥ c ∘ u) b) =
      z a * (Pi.single i 1 : β → K) b) → z ∉ LinearMap.range (M.map r).mulVecLin → ∃ S : Matrix β β A,
      Sᵀ * G + G * S.map c = 0 ∧ (M.map r).rank < ((M + S * m).map r).rank := fun u z h1 h2 => by
    refine ⟨_, skew_two hc hG u w, ?_⟩
    rw [Matrix.map_add _ (map_add r), Matrix.map_mul, hw, show (vecMulVec u (Pi.single i 1) - vecMulVec w (G *ᵥ c ∘ u)).map r =
      vecMulVec z (Pi.single i 1) from Matrix.ext h1, vecMulVec_mul]
    refine rank_lt hy h2 ?_
    rwa [← dotProduct_mulVec, mv, single_dotProduct, one_mul]
  have sg : ∀ b, r ((Pi.single i 1 : β → A) b) = (Pi.single i 1 : β → K) b := fun b => by
    simp [Pi.single_apply, apply_ite r]
  rcases hcase with ⟨h1, κ, hκ⟩ | ⟨η, h1, h2⟩
  · refine fin (κ • w) (r (κ - c κ) • r ∘ w) (fun a b => ?_) fun h => ?_
    · rw [show c ∘ (κ • w) = c κ • c ∘ w from funext fun _ => map_mul c _ _, mulVec_smul, hw]
      simp only [Pi.smul_apply, smul_eq_mul, map_sub, map_mul, sg, Function.comp_apply]
      ring
    · obtain ⟨x₀, hx⟩ := (Submodule.smul_mem_iff _ hκ).1 h
      obtain ⟨x, rfl⟩ := hr.comp_left x₀
      rw [mulVecLin_apply, mv] at hx
      have l := congrArg (fun N => y ⬝ᵥ N *ᵥ c ∘ x) lag
      simp only [add_mulVec, dotProduct_add, ← mulVec_mulVec, mc, zero_mulVec, dotProduct_zero] at l
      rw [dotProduct_mulVec y, dotProduct_mulVec y mᵀ, vecMul_transpose, vecMul_transpose] at l
      have e : (m *ᵥ y) i = (m *ᵥ y) ⬝ᵥ G *ᵥ c ∘ (w - M *ᵥ x) - (M *ᵥ y) ⬝ᵥ G *ᵥ c ∘ (m *ᵥ x) := by
        rw [show c ∘ (w - M *ᵥ x) = c ∘ w - c ∘ (M *ᵥ x) from funext fun _ => map_sub c _ _, mulVec_sub, dotProduct_sub, hw,
          dotProduct_single, mul_one]
        linear_combination l
      refine hi ?_
      rw [mv] at hy
      rw [e, map_sub, r.map_dotProduct, r.map_dotProduct, hy, zero_dotProduct, ← mv G, show r ∘ c ∘ (w - M *ᵥ x) = 0 from
        funext fun a => h1 _ (by rw [Pi.sub_apply, map_sub]; exact sub_eq_zero.2 (congrFun hx a).symm), mulVec_zero,
        dotProduct_zero, sub_zero]
  · obtain ⟨z₀, hz⟩ : ∃ z, z ∉ LinearMap.range (M.map r).mulVecLin := by
      by_contra h
      push Not at h
      exact ((isUnit_iff_isUnit_det _).1 (mulVec_surjective_iff_isUnit.1 h)).ne_zero h0
    obtain ⟨z, rfl⟩ := hr.comp_left z₀
    refine fin (η • z) _ (fun a b => ?_) hz
    rw [show c ∘ (η • z) = c η • c ∘ z from funext fun _ => map_mul c _ _, mulVec_smul]
    simp only [Pi.smul_apply, smul_eq_mul, map_sub, map_mul, sg, Function.comp_apply, h1, h2]
    ring

theorem exists_skew (hc : ∀ z, c (c z) = z) (hr : Function.Surjective r) (hG : ∀ i j, c (G j i) = G i j) (hG' : G * G' = 1)
    (hcase : ((∀ z, r z = 0 → r (c z) = 0) ∧ ∃ κ, r (κ - c κ) ≠ 0) ∨ ∃ η, r η = 1 ∧ r (c η) = 0)
    (hu : ∀ z, r z ≠ 0 → r (c z) ≠ 0 → IsUnit z)
    (lag : Mᵀ * G * m.map c + mᵀ * G * M.map c = 0) (inj : P * M + Q * m = 1) :
    ∃ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 ∧ IsUnit (M + S * m).det := by
  have l2 : ∀ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 →
      (M + S * m)ᵀ * G * m.map c + mᵀ * G * (M + S * m).map c = 0 := fun S hS => by
    rw [transpose_add, transpose_mul, Matrix.map_add _ (map_add c), Matrix.map_mul]
    linear_combination (norm := noncomm_ring) lag + mᵀ * hS * m.map c
  have i2 : ∀ S : Matrix β β A, P * (M + S * m) + (Q - P * S) * m = 1 := fun S => by
    linear_combination (norm := noncomm_ring) inj
  have ind : ∀ k : ℕ, ∃ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 ∧
      (((M + S * m).map r).det ≠ 0 ∨ k ≤ ((M + S * m).map r).rank) := fun k => by
    induction k with
    | zero => exact ⟨0, by simp, .inr (Nat.zero_le _)⟩
    | succ k ih =>
      obtain ⟨S, h1, h2⟩ := ih
      by_cases h0 : ((M + S * m).map r).det = 0
      · obtain ⟨S', h3, h4⟩ := step hc hr hG hG' hcase (l2 S h1) (i2 S) h0
        refine ⟨S + S', ?_, .inr ?_⟩
        · rw [transpose_add, Matrix.map_add _ (map_add c)]
          linear_combination (norm := noncomm_ring) h1 + h3
        · rw [Matrix.add_mul, ← add_assoc]
          exact (h2.resolve_left (not_not.2 h0)).trans_lt h4
      · exact ⟨S, h1, .inl h0⟩
  obtain ⟨S, h1, h2⟩ := ind (Fintype.card β + 1)
  have h3 := h2.resolve_right (not_le.2 (Nat.lt_succ_of_le (rank_le_card_width _)))
  refine ⟨S, h1, hu _ (by rwa [r.map_det]) fun h4 => ?_⟩
  rw [c.map_det, r.map_det] at h4
  obtain ⟨y, hy0, hy⟩ := exists_mulVec_eq_zero_iff.2 h4
  have l := congrArg (fun N : Matrix β β A => N.map r *ᵥ y) (l2 S h1)
  have j := congrArg (fun N : Matrix β β A => (N.map c).map r *ᵥ y) (i2 S)
  generalize M + S * m = t at *
  change (t.map c).map r *ᵥ y = 0 at hy
  simp only [Matrix.map_add _ (map_add r), Matrix.map_add _ (map_add c), Matrix.map_mul, add_mulVec, ← mulVec_mulVec, hy,
    mulVec_zero, add_zero, zero_add, Matrix.map_zero _ (map_zero r), zero_mulVec, Matrix.map_one _ (map_zero r) (map_one r),
    Matrix.map_one _ (map_zero c) (map_one c), one_mulVec] at l j
  have g0 : (G.map r).det ≠ 0 := fun h => by
    have := congrArg (fun N : Matrix β β A => (N.map r).det) hG'
    simp only [Matrix.map_mul, det_mul, h, zero_mul, Matrix.map_one _ (map_zero r) (map_one r), det_one] at this
    exact zero_ne_one this
  rw [eq_zero_of_mulVec_eq_zero g0 (eq_zero_of_mulVec_eq_zero (by rwa [transpose_map, det_transpose]) l), mulVec_zero] at j
  exact hy0 j.symm

end Skew

variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] {c : A →ₐ[R] A} [Fintype β] [DecidableEq β] {J : Matrix β β A}

theorem lag_of {b b' x y : Matrix β β A} (b1 : Adj c J b b') (hb : b + b' = -1) (g : UG c (dbl J))
    (hg : g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = fromRows x y) :
    (y + b * (y - x))ᵀ * J * (y - x).map c + (y - x)ᵀ * J * (y + b * (y - x)).map c = 0 := by
  have h1 : g.1.1ᵀ * dbl J * g.1.1.map c = dbl J := g.2
  have h2 : (fromRows x y)ᵀ * dbl J * (fromRows x y).map c = 0 := by
    rw [← hg, transpose_mul, mapc_mul]
    calc _ = (diagCols β : Matrix (β ⊕ β) β A)ᵀ * (g.1.1ᵀ * dbl J * g.1.1.map c) * (diagCols β : Matrix (β ⊕ β) β A).map c := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
        rw [h1]; simp [diagCols, dbl, fromRows_map, mapc_one, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  have e : b'.map c = -1 - b.map c := by
    rw [← mapc_one (c := c), ← mapc_neg, ← mapc_sub, ← hb]; congr 1; abel
  have b2 : bᵀ * J = -J - J * b.map c := by rw [b1, e]; noncomm_ring
  rw [transpose_fromRows, dbl, fromCols_mul_fromBlocks, fromRows_map, fromCols_mul_fromRows] at h2
  rw [transpose_add, transpose_mul, mapc_add, mapc_mul, mapc_sub, transpose_sub]
  linear_combination (norm := noncomm_ring) (yᵀ - xᵀ) * b2 * (y.map c - x.map c) - h2

theorem exists_decomp {b b' x y t' : Matrix β β A} (b1 : Adj c J b b') (hb : b + b' = -1) (g : UG c (dbl J))
    (hg : g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = fromRows x y) (ht : (y + b * (y - x)) * t' = 1) {ε : A} (he : ε * ε = ε)
    (hc : c ε = ε) (hm : ε • (y - x) = y - x) :
    ∃ (s n p : UG c (dbl J)) (t : GL β A), s * s = 1 ∧ g = s * n * s * p ∧ s.1.1 = CC b * SS ε * Ci b ∧
      n.1.1 = CC b * fromBlocks 1 (-((y - x) * t')) 0 1 * Ci b ∧ (n⁻¹).1.1 = CC b * fromBlocks 1 ((y - x) * t') 0 1 * Ci b ∧
      n.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * (1 : GL β A).1 ∧
      p.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * t.1 ∧
      t.1 = y + b * (y - x) ∧ (t⁻¹).1 = t' := by
  have lag := lag_of b1 hb g hg
  set m : Matrix β β A := y - x with hmd
  set t₀ := y + b * m with ht₀
  set T := -(m * t') with hT
  have ht' : t' * t₀ = 1 := mul_eq_one_comm.1 ht
  have sk : Tᵀ * J + J * T.map c = 0 := by
    have a1 : t'ᵀ * t₀ᵀ = 1 := by rw [← transpose_mul, ht, transpose_one]
    have a2 : t₀.map c * t'.map c = 1 := by rw [← mapc_mul, ht, mapc_one]
    rw [hT, transpose_neg, transpose_mul, mapc_neg, mapc_mul]
    linear_combination (norm := noncomm_ring) -(t'ᵀ * lag * t'.map c) + a1 * J * m.map c * t'.map c + t'ᵀ * mᵀ * J * a2
  have e0 : ε * (1 - ε) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have e0' : (1 - ε) * ε = 0 := by rw [mul_comm, e0]
  have e1 : (1 - ε) * (1 - ε) = 1 - ε := by rw [sub_mul, one_mul, e0, sub_zero]
  have hS : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A) * SS ε = 1 := by
    rw [SS, fromBlocks_multiply, ← fromBlocks_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, e0, e0', e1, he, ← add_smul]
    simp
  have hSu : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * fromBlocks 0 J J 0 * (SS ε : Matrix (β ⊕ β) (β ⊕ β) A).map c =
      fromBlocks 0 J J 0 := by
    rw [SS, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp only [mapc_smul, mapc_one, map_sub, map_one, hc, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, smul_zero, zero_add, add_zero, smul_smul, e0, e0', e1, he, ← add_smul]
    simp
  have hU : (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks 1 (m * t') 0 1 = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one, hT]; simp
  have hUu : (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * fromBlocks 0 J J 0 *
      (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A).map c = fromBlocks 0 J J 0 := by
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, mapc_one, mapc_zero]
    simp only [transpose_one, transpose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
    rw [add_comm (J * _), sk]
  have hTt : T * t₀ = -m := by rw [hT, Matrix.neg_mul, Matrix.mul_assoc, ht', Matrix.mul_one]
  let s := mkU b1 hb _ _ hS hSu
  let n := mkU b1 hb _ _ hU hUu
  have hs : s.1.1 = CC b * SS ε * Ci b := rfl
  have hn : n.1.1 = CC b * fromBlocks 1 T 0 1 * Ci b := rfl
  have hεT : ε • T = T := by rw [hT, smul_neg, ← Matrix.smul_mul, hm]
  have hεT' : (1 - ε) • T = 0 := by rw [sub_smul, one_smul, hεT, sub_self]
  have hL : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks 1 T 0 1 * SS ε = fromBlocks 1 0 T 1 := by
    rw [SS, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, smul_zero, add_zero, hεT, hεT',
      zero_add, Matrix.add_mul, smul_add, smul_smul, e0, e0', e1, he, zero_smul, ← add_smul]
    simp
  have hD : Ci b * (diagCols β : Matrix (β ⊕ β) β A) = (fromRows 1 0 : Matrix (β ⊕ β) β A) := by
    rw [Ci, diagCols, fromBlocks_mul_fromRows]; simp
  have hD' : CC b * (fromRows 1 0 : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) := by
    rw [CC, diagCols, fromBlocks_mul_fromRows]; simp
  refine ⟨s, n, (s * n * s)⁻¹ * g, ⟨t₀, t', ht, ht'⟩, Subtype.ext (Units.ext s.1.mul_inv), by group, hs, hn, rfl, ?_, ?_, rfl, rfl⟩
  · rw [hn, Matrix.mul_assoc _ (Ci b), hD, Matrix.mul_assoc (CC b), fromBlocks_mul_fromRows]
    simpa using hD'
  · have e : (s * n * s).1.1 = CC b * fromBlocks 1 0 T 1 * Ci b := by
      change s.1.1 * n.1.1 * s.1.1 = _
      rw [hs, hn, ← hL]
      calc CC b * SS ε * Ci b * (CC b * fromBlocks 1 T 0 1 * Ci b) * (CC b * SS ε * Ci b)
          = CC b * (SS ε * (Ci b * CC b) * fromBlocks 1 T 0 1 * (Ci b * CC b) * SS ε) * Ci b := by noncomm_ring
        _ = _ := by rw [Ci_CC, Matrix.mul_one, Matrix.mul_one]
    have e2 : g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (s * n * s).1.1 * ((diagCols β : Matrix (β ⊕ β) β A) * t₀) := by
      rw [e, hg, ← Matrix.mul_assoc _ (diagCols β : Matrix (β ⊕ β) β A), Matrix.mul_assoc _ (Ci b), hD, Matrix.mul_assoc (CC b),
        fromBlocks_mul_fromRows, CC, fromBlocks_mul_fromRows, fromRows_mul]
      congr 1
      · linear_combination (norm := noncomm_ring) -((1 + b) * hTt) - ht₀ + hmd
      · linear_combination (norm := noncomm_ring) -(b * hTt) - ht₀
    change ((s * n * s)⁻¹).1.1 * g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * t₀
    rw [Matrix.mul_assoc _ g.1.1, e2, ← Matrix.mul_assoc, show ((s * n * s)⁻¹).1.1 * (s * n * s).1.1 = 1 from (s * n * s).1.inv_mul,
      Matrix.one_mul]

end GlobalTheory.ThK.Dbl.Vf2

end
