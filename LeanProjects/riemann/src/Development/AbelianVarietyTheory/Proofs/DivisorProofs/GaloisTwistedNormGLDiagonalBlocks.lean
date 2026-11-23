import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.ShinBlock

open GlobalTheory.Shin

variable {K : Type} [Field K]

theorem tl_eq {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) K) :
    tl a M = M.submatrix (Fin.castAdd b) (Fin.castAdd b) := by
  ext i j
  simp only [tl, ent, Matrix.submatrix_apply]
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

theorem br_eq {a b : ℕ} (M : Matrix (Fin (a + b)) (Fin (a + b)) K) :
    br a b M = M.submatrix (Fin.natAdd a) (Fin.natAdd a) := by
  ext i j
  simp only [br, ent, Matrix.submatrix_apply]
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

theorem inPar_mul {a n : ℕ} {x y : GL (Fin n) K} (hx : InPar a x) (hy : InPar a y) :
    InPar a (x * y) := by
  intro i j hj hi
  rw [Units.val_mul, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : (k : ℕ) < a
  · rw [hx i k hk hi, zero_mul]
  · rw [hy k j hj (by omega), mul_zero]

theorem inPar_one {a n : ℕ} : InPar a (1 : GL (Fin n) K) := by
  intro i j hj hi
  rw [Units.val_one, Matrix.one_apply_ne]
  intro h; subst h; omega

theorem inPar_inv {a n : ℕ} {x : GL (Fin n) K} (hx : InPar a x) : InPar a x⁻¹ := by
  have hB : Matrix.BlockTriangular (x : Matrix (Fin n) (Fin n) K)
      (fun i : Fin n => if a ≤ (i : ℕ) then 1 else 0) := by
    intro i j hij
    simp only at hij
    split_ifs at hij with h1 h2 <;> first | omega | exact hx i j (by omega) (by omega)
  haveI : Invertible (x : Matrix (Fin n) (Fin n) K) := x.invertible
  have := Matrix.blockTriangular_inv_of_blockTriangular hB
  intro i j hj hi
  rw [Matrix.coe_units_inv]
  exact this (by simp only; rw [if_pos hi, if_neg (by omega)]; exact Nat.zero_lt_one)

theorem tl_mul {a b : ℕ} {x y : GL (Fin (a + b)) K} (hy : InPar a y) :
    tl a (x * y).val = tl a x.val * tl a y.val := by
  rw [tl_eq, tl_eq, tl_eq]
  ext i j
  simp only [Matrix.submatrix_apply, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  have : ∑ k : Fin b, x.val (Fin.castAdd b i) (Fin.natAdd a k) *
      y.val (Fin.natAdd a k) (Fin.castAdd b j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [hy _ _ (by simp) (by simp), mul_zero]
  rw [this, add_zero]

theorem br_mul {a b : ℕ} {x y : GL (Fin (a + b)) K} (hx : InPar a x) :
    br a b (x * y).val = br a b x.val * br a b y.val := by
  rw [br_eq, br_eq, br_eq]
  ext i j
  simp only [Matrix.submatrix_apply, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  have : ∑ k : Fin a, x.val (Fin.natAdd a i) (Fin.castAdd b k) *
      y.val (Fin.castAdd b k) (Fin.natAdd a j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [hx _ _ (by simp) (by simp), zero_mul]
  rw [this, zero_add]

theorem tl_one {a b : ℕ} : tl a (1 : GL (Fin (a + b)) K).val = 1 := by
  rw [tl_eq, Units.val_one]
  exact Matrix.submatrix_one _ (Fin.castAdd_injective a b)

theorem br_one {a b : ℕ} : br a b (1 : GL (Fin (a + b)) K).val = 1 := by
  rw [br_eq, Units.val_one]
  exact Matrix.submatrix_one _ (Fin.natAdd_injective b a)

theorem isUnit_tl {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) : IsUnit (tl a x.val) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply Matrix.isUnit_det_of_right_inverse (B := tl a x⁻¹.val)
  rw [← tl_mul (inPar_inv hx), mul_inv_cancel, tl_one]

theorem isUnit_br {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) : IsUnit (br a b x.val) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply Matrix.isUnit_det_of_right_inverse (B := br a b x⁻¹.val)
  rw [← br_mul hx, mul_inv_cancel, br_one]

theorem coe_tlG {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) :
    (tlG a x).val = tl a x.val := by
  unfold tlG toG
  rw [dif_pos (isUnit_tl hx)]
  rfl

theorem coe_brG {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) :
    (brG a b x).val = br a b x.val := by
  unfold brG toG
  rw [dif_pos (isUnit_br hx)]
  rfl

theorem gal_val {K' : Type} [Field K'] (t : K →+* K') {n : ℕ} (x : GL (Fin n) K) :
    (gal t n x).val = x.val.map t := rfl

theorem inPar_gal {K' : Type} [Field K'] (t : K →+* K') {a n : ℕ} {x : GL (Fin n) K} (hx : InPar a x) :
    InPar a (gal t n x) := by
  intro i j hj hi
  rw [gal_val, Matrix.map_apply, hx i j hj hi, map_zero]

theorem tl_map {K' : Type} [Field K'] (t : K →+* K') (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    tl a (M.map t) = (tl a M).map t := by
  ext i j
  simp only [tl, ent, Matrix.map_apply]
  split_ifs <;> simp

theorem br_map {K' : Type} [Field K'] (t : K →+* K') (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    br a b (M.map t) = (br a b M).map t := by
  ext i j
  simp only [br, ent, Matrix.map_apply]
  split_ifs <;> simp

theorem tlG_gal {K' : Type} [Field K'] (t : K →+* K') {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) :
    tlG a (gal t (a + b) x) = gal t a (tlG a x) := by
  ext1
  rw [coe_tlG (inPar_gal t hx), gal_val, gal_val, coe_tlG hx, tl_map]

theorem brG_gal {K' : Type} [Field K'] (t : K →+* K') {a b : ℕ} {x : GL (Fin (a + b)) K} (hx : InPar a x) :
    brG a b (gal t (a + b) x) = gal t b (brG a b x) := by
  ext1
  rw [coe_brG (inPar_gal t hx), gal_val, gal_val, coe_brG hx, br_map]

theorem tlG_mul {a b : ℕ} {x y : GL (Fin (a + b)) K} (hx : InPar a x) (hy : InPar a y) :
    tlG a (x * y) = tlG a x * tlG a y := by
  ext1
  rw [coe_tlG (inPar_mul hx hy), tl_mul hy, Units.val_mul, coe_tlG hx, coe_tlG hy]

theorem brG_mul {a b : ℕ} {x y : GL (Fin (a + b)) K} (hx : InPar a x) (hy : InPar a y) :
    brG a b (x * y) = brG a b x * brG a b y := by
  ext1
  rw [coe_brG (inPar_mul hx hy), br_mul hx, Units.val_mul, coe_brG hx, coe_brG hy]

theorem tlG_one {a b : ℕ} : tlG a (1 : GL (Fin (a + b)) K) = 1 := by
  ext1
  rw [coe_tlG inPar_one, tl_one, Units.val_one]

theorem brG_one {a b : ℕ} : brG a b (1 : GL (Fin (a + b)) K) = 1 := by
  ext1
  rw [coe_brG inPar_one, br_one, Units.val_one]

theorem prod_blocks {a b : ℕ} (l : List (GL (Fin (a + b)) K)) (hl : ∀ x ∈ l, InPar a x) :
    InPar a l.prod ∧ tlG a l.prod = (l.map (tlG a)).prod ∧ brG a b l.prod = (l.map (brG a b)).prod := by
  induction l with
  | nil => exact ⟨inPar_one, tlG_one, brG_one⟩
  | cons x l ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
    have hx := hl x List.mem_cons_self
    simp only [List.prod_cons, List.map_cons]
    exact ⟨inPar_mul hx h1, by rw [tlG_mul hx h1, h2], by rw [brG_mul hx h1, h3]⟩

theorem nrm_blocks : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a b n : ℕ), n = a + b →
    ∀ (γ : GL (Fin n) F) (δ : GL (Fin n) F'), InPar a γ → InPar a δ → nrm s δ = incl F F' n γ →
    nrm s (tlG a δ) = incl F F' a (tlG a γ) ∧ nrm s (brG a b δ) = incl F F' b (brG a b γ) := by
  intro F F' _ _ _ _ s _ a b n hn γ δ hγ hδ h
  subst hn
  have hall : ∀ x ∈ (List.range (Module.finrank F F')).map (fun i => galAct F F' (a + b) (s ^ i) δ), InPar a x := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact inPar_gal _ hδ
  obtain ⟨-, h2, h3⟩ := prod_blocks _ hall
  have hn : nrm s δ = ((List.range (Module.finrank F F')).map (fun i => galAct F F' (a + b) (s ^ i) δ)).prod := rfl
  refine ⟨?_, ?_⟩
  · have e : nrm s (tlG a δ) = (((List.range (Module.finrank F F')).map
        (fun i => galAct F F' (a + b) (s ^ i) δ)).map (tlG a)).prod := by
      unfold nrm nrmG
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, galAct_apply]
      exact (tlG_gal _ hδ).symm
    rw [e, ← h2, ← hn, h]
    exact tlG_gal _ hγ
  · have e : nrm s (brG a b δ) = (((List.range (Module.finrank F F')).map
        (fun i => galAct F F' (a + b) (s ^ i) δ)).map (brG a b)).prod := by
      unfold nrm nrmG
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, galAct_apply]
      exact (brG_gal _ hδ).symm
    rw [e, ← h3, ← hn, h]
    exact brG_gal _ hγ

end GlobalTheory.ShinBlock
