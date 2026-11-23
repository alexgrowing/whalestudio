import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

noncomputable section

namespace GlobalTheory.UnimodTransvect

variable {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m]

theorem vecMulVec_zero' (a : m → R) : vecMulVec a (0 : m → R) = 0 := by
  ext i j
  simp [vecMulVec]

def tv (a b : m → R) (h : b ⬝ᵥ a = 0) : GL m R where
  val := 1 + vecMulVec a b
  inv := 1 - vecMulVec a b
  val_inv := by
    rw [mul_sub, mul_one, add_mul, one_mul, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero']; abel
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero']; abel

theorem tv_mulVec (a b : m → R) (h : b ⬝ᵥ a = 0) (v : m → R) :
    ((tv a b h : GL m R) : Matrix m m R) *ᵥ v = v + (b ⬝ᵥ v) • a := by
  change (1 + vecMulVec a b) *ᵥ v = _
  rw [add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem vecMul_tv_inv (a b : m → R) (h : b ⬝ᵥ a = 0) (f : m → R) :
    f ᵥ* (((tv a b h)⁻¹ : GL m R) : Matrix m m R) = f - (f ⬝ᵥ a) • b := by
  change f ᵥ* (1 - vecMulVec a b) = _
  rw [vecMul_sub, vecMul_one, vecMul_vecMulVec]

theorem reach_trans {v w u : m → R} (h1 : ∃ g : GL m R, (g : Matrix m m R) *ᵥ v = w)
    (h2 : ∃ g : GL m R, (g : Matrix m m R) *ᵥ w = u) : ∃ g : GL m R, (g : Matrix m m R) *ᵥ v = u := by
  obtain ⟨g1, hg1⟩ := h1
  obtain ⟨g2, hg2⟩ := h2
  refine ⟨g2 * g1, ?_⟩
  rw [Units.val_mul, ← mulVec_mulVec, hg1, hg2]

variable {n : ℕ}

theorem reach_of_last_one (u : Fin (n + 1) → R) (hu : u (Fin.last n) = 1) :
    ∃ g : GL (Fin (n + 1)) R, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ u = Pi.single (Fin.last n) 1 := by
  refine ⟨tv (Pi.single (Fin.last n) 1 - u) (Pi.single (Fin.last n) 1) ?_, ?_⟩
  · rw [single_dotProduct, Pi.sub_apply, Pi.single_eq_same, hu]
    ring
  · rw [tv_mulVec, single_dotProduct, hu, one_mul, one_smul]
    abel

theorem reach_last_one (w : Fin (n + 1) → R) (c : Fin n → R)
    (hc : ∑ i, c i * w i.castSucc = 1) :
    ∃ g : GL (Fin (n + 1)) R, ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ w) (Fin.last n) = 1 := by
  obtain ⟨c', hc'⟩ : ∃ c' : Fin (n + 1) → R, c' = Fin.snoc c 0 := ⟨_, rfl⟩
  have hcl : c' (Fin.last n) = 0 := by simp [hc']
  have hcw : c' ⬝ᵥ w = 1 := by
    rw [dotProduct, Fin.sum_univ_castSucc, hcl, zero_mul, add_zero]
    simpa [hc'] using hc
  refine ⟨tv (Pi.single (Fin.last n) 1) ((1 - w (Fin.last n)) • c') ?_, ?_⟩
  · rw [dotProduct_single, Pi.smul_apply, hcl, smul_zero, zero_mul]
  · rw [tv_mulVec, smul_dotProduct, hcw, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
    simp only [smul_eq_mul]
    ring

theorem reach_first_unimod {s : ℕ} (hS : StableRangeLe R s) (hn : s ≤ n) (v f : Fin (n + 1) → R)
    (hfv : f ⬝ᵥ v = 1) :
    ∃ g : GL (Fin (n + 1)) R, ∃ c : Fin n → R, ∑ i, c i * ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ v) i.castSucc = 1 := by
  have hU : Unimodular R v := by
    unfold Unimodular
    rw [Ideal.eq_top_iff_one, ← hfv, Ideal.mem_span_range_iff_exists_fun]
    exact ⟨f, rfl⟩
  obtain ⟨t, ht⟩ := hS n hn v hU
  unfold Unimodular at ht
  have h1 : (1 : R) ∈ Ideal.span (Set.range fun i => v i.castSucc + t i * v (Fin.last n)) := by
    rw [ht]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  obtain ⟨a, ha⟩ : ∃ a : Fin (n + 1) → R, a = Fin.snoc t 0 := ⟨_, rfl⟩
  have hal : a (Fin.last n) = 0 := by simp [ha]
  refine ⟨tv a (Pi.single (Fin.last n) 1) (by rw [single_dotProduct, hal, mul_zero]), c, ?_⟩
  refine (Finset.sum_congr rfl fun i _ => ?_).trans hc
  rw [tv_mulVec, single_dotProduct, one_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [ha, Fin.snoc_castSucc]
  ring

theorem main : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ), s ≤ n → ∀ v f : Fin (n + 1) → R, f ⬝ᵥ v = 1 → ∃ g : GL (Fin (n + 1)) R, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ v = Pi.single (Fin.last n) 1 ∧ f ᵥ* ((g⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = Pi.single (Fin.last n) 1 := by
  intro R _ s hS n hn v f hfv
  obtain ⟨g1, c, hc⟩ := reach_first_unimod hS hn v f hfv
  obtain ⟨g2, hg2⟩ := reach_last_one _ c hc
  obtain ⟨g3, hg3⟩ := reach_of_last_one _ hg2
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin (n + 1)) R, g = g3 * g2 * g1 := ⟨_, rfl⟩
  have hgv : (g : Matrix _ _ R) *ᵥ v = Pi.single (Fin.last n) 1 := by
    rw [hg, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    exact hg3
  obtain ⟨f', hf'⟩ : ∃ f' : Fin (n + 1) → R, f' = f ᵥ* ((g⁻¹ : GL _ R) : Matrix _ _ R) := ⟨_, rfl⟩
  have hfl : f' (Fin.last n) = 1 := by
    have : f' ⬝ᵥ ((g : Matrix _ _ R) *ᵥ v) = 1 := by
      rw [hf', ← dotProduct_mulVec, mulVec_mulVec, Units.inv_mul, one_mulVec, hfv]
    rwa [hgv, dotProduct_single, mul_one] at this
  have hb : (f' - Pi.single (Fin.last n) 1) ⬝ᵥ Pi.single (Fin.last n) (1 : R) = 0 := by
    rw [dotProduct_single, Pi.sub_apply, hfl, Pi.single_eq_same]
    ring
  refine ⟨tv (Pi.single (Fin.last n) 1) (f' - Pi.single (Fin.last n) 1) hb * g, ?_, ?_⟩
  · rw [Units.val_mul, ← mulVec_mulVec, hgv, tv_mulVec, hb, zero_smul, add_zero]
  · rw [_root_.mul_inv_rev, Units.val_mul, ← vecMul_vecMul, ← hf', vecMul_tv_inv, dotProduct_single,
      hfl, mul_one, one_smul]
    abel

end GlobalTheory.UnimodTransvect

end

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
theorem _root_.GlobalTheory.T.exists_GL_moving_unimodular_pair_to_last_basis : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ (n : ℕ), s ≤ n → ∀ v f : Fin (n + 1) → R, f ⬝ᵥ v = 1 → ∃ g : GL (Fin (n + 1)) R, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ v = Pi.single (Fin.last n) 1 ∧ f ᵥ* ((g⁻¹ : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = Pi.single (Fin.last n) 1 := by
  first
  | exact @GlobalTheory.UnimodTransvect.main
  | exact @GlobalTheory.UnimodTransvect.reach_first_unimod
  | exact @GlobalTheory.UnimodTransvect.reach_last_one
  | exact @GlobalTheory.UnimodTransvect.reach_of_last_one
  | exact @GlobalTheory.UnimodTransvect.reach_trans
  | exact @GlobalTheory.UnimodTransvect.vecMul_tv_inv
  | exact @GlobalTheory.UnimodTransvect.tv_mulVec
  | exact @GlobalTheory.UnimodTransvect.vecMulVec_zero'
end
