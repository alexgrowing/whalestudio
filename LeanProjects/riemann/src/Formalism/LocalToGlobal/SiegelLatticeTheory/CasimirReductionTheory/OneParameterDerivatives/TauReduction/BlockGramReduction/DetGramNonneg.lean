import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow

set_option autoImplicit false

noncomputable section

open NumberField Matrix

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

variable (I : AutInst)

def cmat (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) :
    Matrix (Fin I.n) (Fin j) ℂ :=
  Matrix.of fun i a => coordV I x v (b a) i

theorem gramV_eq (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) :
    gramV I x v b = (cmat I x v b)ᴴ * cmat I x v b := by
  ext a c
  simp [gramV, cmat, Matrix.mul_apply, Matrix.conjTranspose_apply]

def subOfEq {x x' : I.GA} (h : latSet I x' = latSet I x) (s : Sub I x) : Sub I x' where
  j := s.j
  j_pos := s.j_pos
  b := s.b
  b_ind := s.b_ind
  B := s.B
  B_lat := by rw [h]; exact s.B_lat
  b_mem := s.b_mem
  B_span := s.B_span

theorem det_gram_nonneg (h5 : GramDistortionBound) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (hj : 1 ≤ j)
    (b : Fin j → Fin I.n → I.E) : 0 ≤ (gramV I x v b).det.re := by
  rw [gramV_eq]
  open scoped ComplexOrder in
  exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self _).det_nonneg).1

theorem ht_nonneg (h5 : GramDistortionBound) {x : I.GA} (s : Sub I x) : 0 ≤ ht I s := by
  unfold ht
  exact div_nonneg (Finset.prod_nonneg fun v _ => det_gram_nonneg I h5 x v s.j_pos s.b) (Nat.cast_nonneg _)

theorem size_nonneg (h5 : GramDistortionBound) {x : I.GA} (s : Sub I x) : 0 ≤ size I s := by
  unfold Size.size
  exact Real.rpow_nonneg (ht_nonneg I h5 s) _

theorem size_subOfEq_le (h5 : GramDistortionBound) {x x' : I.GA} (hlat : latSet I x' = latSet I x)
    (Y : InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ)
    (hY : ∀ v u, coordV I x' v u = Y v *ᵥ coordV I x v u) {c : ℝ} (hc : 1 ≤ c)
    (hb : ∀ v (w : Fin I.n → ℂ), ∑ i, ‖(Y v *ᵥ w) i‖ ^ 2 ≤ c * ∑ i, ‖w i‖ ^ 2) (s : Sub I x) :
    size I (subOfEq I hlat s) ≤ c ^ Fintype.card (InfinitePlace I.F) * size I s := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hcm : ∀ v, cmat I x' v s.b = Y v * cmat I x v s.b := by
    intro v
    ext i a
    simp [cmat, hY, Matrix.mulVec, Matrix.mul_apply, dotProduct]
  have hdet : ∀ v, (gramV I x' v s.b).det.re ≤ c ^ s.j * (gramV I x v s.b).det.re := by
    intro v
    rw [gramV_eq, gramV_eq, hcm]
    refine (h5 I.n s.j (Y v) (cmat I x v s.b) 0 c le_rfl (fun w => ⟨?_, hb v w⟩)).2
    rw [zero_mul]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hht : ht I (subOfEq I hlat s) ≤ (c ^ s.j) ^ Fintype.card (InfinitePlace I.F) * ht I s := by
    unfold ht
    rw [mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    calc ∏ v, (gramV I x' v (subOfEq I hlat s).b).det.re
        ≤ ∏ v : InfinitePlace I.F, c ^ s.j * (gramV I x v s.b).det.re :=
          Finset.prod_le_prod (fun v _ => det_gram_nonneg I h5 x' v s.j_pos s.b) (fun v _ => hdet v)
      _ = (c ^ s.j) ^ Fintype.card (InfinitePlace I.F) * ∏ v, (gramV I x v s.b).det.re := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have he : 0 ≤ 1 / (2 * (I.f : ℝ) * (s.j : ℝ)) := by positivity
  have hexp : ((s.j * Fintype.card (InfinitePlace I.F) : ℕ) : ℝ) * (1 / (2 * (I.f : ℝ) * (s.j : ℝ)))
      ≤ (Fintype.card (InfinitePlace I.F) : ℝ) := by
    have hj : (1 : ℝ) ≤ s.j := by exact_mod_cast s.j_pos
    rcases Nat.eq_zero_or_pos I.f with hf | hf
    · simp [hf]
    · have hf' : (1 : ℝ) ≤ I.f := by exact_mod_cast hf
      rw [Nat.cast_mul, mul_one_div, div_le_iff₀ (by positivity)]
      have hP : (0 : ℝ) ≤ Fintype.card (InfinitePlace I.F) := Nat.cast_nonneg _
      nlinarith [mul_nonneg (mul_nonneg hP (by linarith : (0 : ℝ) ≤ s.j)) (by linarith : (0 : ℝ) ≤ 2 * (I.f : ℝ) - 1)]
  unfold Size.size
  show ht I (subOfEq I hlat s) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) ≤ _
  calc ht I (subOfEq I hlat s) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ)))
      ≤ ((c ^ s.j) ^ Fintype.card (InfinitePlace I.F) * ht I s) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) :=
        Real.rpow_le_rpow (ht_nonneg I h5 _) hht he
    _ = ((c ^ s.j) ^ Fintype.card (InfinitePlace I.F)) ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) *
          ht I s ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) :=
        Real.mul_rpow (by positivity) (ht_nonneg I h5 s)
    _ ≤ c ^ Fintype.card (InfinitePlace I.F) * ht I s ^ (1 / (2 * (I.f : ℝ) * (s.j : ℝ))) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (ht_nonneg I h5 s) _)
        rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hc0, ← Real.rpow_natCast c]
        exact Real.rpow_le_rpow_of_exponent_le hc hexp

end Formalism.L2.SG.Pf.Tau
