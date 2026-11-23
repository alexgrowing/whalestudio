import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

section Core

variable {n r : ℕ} (ε : Fin n → Bool)

theorem witt_of_gram' {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → Fin n → ℂ)
    (hG : ∀ i j, hJ ε (x i) (x j) = hJ ε (y i) (y j))
    (hnd : (Matrix.of fun i j => hJ ε (x i) (x j)).det ≠ 0) :
    ∃ g : Formalism.REAL.UJ ε, ∀ i, Formalism.MainNotions.S.uMat g *ᵥ x i = y i := by
  let e := Fintype.equivFin ι
  have hdet : (Matrix.of fun i j : Fin (Fintype.card ι) => hJ ε (x (e.symm i)) (x (e.symm j))).det ≠ 0 := by
    have hs : (Matrix.of fun i j : Fin (Fintype.card ι) => hJ ε (x (e.symm i)) (x (e.symm j))) =
        (Matrix.of fun i j => hJ ε (x i) (x j)).submatrix e.symm e.symm := rfl
    rw [hs, Matrix.det_submatrix_equiv_self]
    exact hnd
  obtain ⟨g, hg⟩ := witt_of_gram ε (fun k => x (e.symm k)) (fun k => y (e.symm k)) (fun i j => hG _ _) hdet
  refine ⟨g, fun i => ?_⟩
  have := hg (e i)
  simpa using this

theorem hJ_zero_left (y : Fin n → ℂ) : hJ ε 0 y = 0 := by
  simp [hJ]

theorem isIsom_uMat (g : Formalism.REAL.UJ ε) : IsIsom ε (Formalism.MainNotions.S.uMat g) := by
  intro x y
  have hg : (Formalism.MainNotions.S.uMat g)ᴴ * (Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat g) = Formalism.REAL.Jm ε := by
    rw [← Matrix.mul_assoc]
    exact g.2
  simp only [hJ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hg]

theorem famSc_castSucc (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (a : Fin r) :
    famSc sc e z (Fin.castSucc a) = (((sc : ℂ) ^ (r - a.1))⁻¹) • e a := by
  simp only [famSc, fam, Fin.snoc_castSucc, Fin.coe_castSucc]

theorem famSc_last' (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc sc e z (Fin.last r) = z := by
  simp only [famSc, fam, Fin.snoc_last, Fin.val_last, Nat.sub_self, pow_zero, inv_one, one_smul]

private theorem hJ_smul_left_eq_conj_mul (a : ℂ) (x y : Fin n → ℂ) : hJ ε (a • x) y = conj a * hJ ε x y := by
  simp only [hJ, star_smul, smul_dotProduct, smul_eq_mul, Complex.star_def]

private theorem hJ_smul_right_eq_mul (a : ℂ) (x y : Fin n → ℂ) : hJ ε x (a • y) = a * hJ ε x y := by
  simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem hJ_eq_conj_hJ_swap (x y : Fin n → ℂ) : hJ ε x y = conj (hJ ε y x) := by
  simp only [hJ, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, map_sum, map_mul,
    Complex.star_def, Complex.conj_conj]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ε i <;> simp [h] <;> ring

theorem hJ_famSc (sc : ℝ) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (T : ℂ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hez : ∀ a, hJ ε (e a) z = 0) (hzz : hJ ε z z = -T)
    (a b : Fin (r + 1)) :
    hJ ε (famSc sc e z a) (famSc sc e z b) = if a = Fin.last r ∧ b = Fin.last r then -T else 0 := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last =>
      rw [famSc_last', if_pos ⟨rfl, rfl⟩, hzz]
    | cast b' =>
      rw [famSc_last', famSc_castSucc, hJ_smul_right_eq_mul, hJ_eq_conj_hJ_swap, hez, map_zero, mul_zero,
        if_neg (fun h => (Fin.castSucc_lt_last b').ne h.2)]
  | cast a' =>
    rw [famSc_castSucc, hJ_smul_left_eq_conj_mul, if_neg (fun h => (Fin.castSucc_lt_last a').ne h.1)]
    induction b using Fin.lastCases with
    | last => rw [famSc_last', hez, mul_zero]
    | cast b' => rw [famSc_castSucc, hJ_smul_right_eq_mul, hee, mul_zero, mul_zero]

theorem dl_diag_last (c : Fin (r + 1) → ℂ) :
    Dl (Matrix.diagonal c) (r + 1) = (∏ i : Fin r, c (Fin.castSucc i)) * c (Fin.last r) := by
  unfold Dl
  rw [dif_pos le_rfl, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal,
    Fin.prod_univ_castSucc]
  rfl

theorem dl_diag_r (c : Fin (r + 1) → ℂ) :
    Dl (Matrix.diagonal c) r = ∏ i : Fin r, c (Fin.castSucc i) := by
  unfold Dl
  rw [dif_pos (Nat.le_succ r), Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  rfl

theorem normSq_last_gt (T T' : ℝ) (c : Fin (r + 1) → ℂ) (hG : 0 < Gv T T' (Matrix.diagonal c)) :
    T * T' < ‖c (Fin.last r)‖ ^ 2 := by
  have key : Gv T T' (Matrix.diagonal c) =
      ‖∏ i : Fin r, c i.castSucc‖ ^ 2 * (‖c (Fin.last r)‖ ^ 2 - T * T') := by
    unfold Gv
    rw [dl_diag_last, dl_diag_r, norm_mul, mul_pow]
    ring
  rw [key] at hG
  have := pos_of_mul_pos_right hG (sq_nonneg _)
  linarith

theorem diagDC_core (sc : ℝ) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hez : ∀ a, hJ ε (e a) z = 0) (hez' : ∀ a, hJ ε (e a) z' = 0)
    (hzz : hJ ε z z = -(T : ℂ)) (hzz' : hJ ε z' z' = -(T' : ℂ))
    (c : Fin (r + 1) → ℂ) (hc : ∀ l, c l ≠ 0) (hG : 0 < Gv T T' (Matrix.diagonal c))
    (g g' : Formalism.REAL.UJ ε)
    (h1 : Zhat ε (famSc sc e z) (famSc sc e z') (Formalism.MainNotions.S.uMat g) = Matrix.diagonal c)
    (h2 : Zhat ε (famSc sc e z) (famSc sc e z') (Formalism.MainNotions.S.uMat g') = Matrix.diagonal c) :
    ∃ s : Formalism.REAL.UJ ε, (∀ a, Formalism.MainNotions.S.uMat s *ᵥ e a = e a) ∧ Formalism.MainNotions.S.uMat s *ᵥ z = z ∧
      ∀ b, Formalism.MainNotions.S.uMat s *ᵥ (Formalism.MainNotions.S.uMat g *ᵥ famSc sc e z' b) = Formalism.MainNotions.S.uMat g' *ᵥ famSc sc e z' b := by
  have hlt := normSq_last_gt T T' c hG
  obtain ⟨α, hα⟩ : ∃ α : Fin (r + 1) → ℂ, ∀ i, α i = if i = Fin.last r then -(T : ℂ) else 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin (r + 1) → ℂ, ∀ i, γ i = if i = Fin.last r then -(T' : ℂ) else 0 :=
    ⟨_, fun _ => rfl⟩
  have hdiag : ∀ (U : ℂ) (δ : Fin (r + 1) → ℂ), (∀ i, δ i = if i = Fin.last r then -U else 0) →
      ∀ a b : Fin (r + 1), (if a = Fin.last r ∧ b = Fin.last r then -U else 0) = Matrix.diagonal δ a b := by
    intro U δ hδ a b
    rw [Matrix.diagonal_apply, hδ]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, if_neg (fun h => hab (h.1.trans h.2.symm))]
  have hA : ∀ a b, hJ ε (famSc sc e z a) (famSc sc e z b) = Matrix.diagonal α a b := fun a b => by
    rw [hJ_famSc ε sc e z (T : ℂ) hee hez hzz a b]
    exact hdiag _ α hα a b
  have hC : ∀ a b, hJ ε (Formalism.MainNotions.S.uMat g *ᵥ famSc sc e z' a) (Formalism.MainNotions.S.uMat g *ᵥ famSc sc e z' b) =
      Matrix.diagonal γ a b := fun a b => by
    rw [isIsom_uMat ε g (famSc sc e z' a) (famSc sc e z' b), hJ_famSc ε sc e z' (T' : ℂ) hee hez' hzz' a b]
    exact hdiag _ γ hγ a b
  have hB : ∀ g0 : Formalism.REAL.UJ ε, Zhat ε (famSc sc e z) (famSc sc e z') (Formalism.MainNotions.S.uMat g0) = Matrix.diagonal c →
      ∀ a b, hJ ε (famSc sc e z a) (Formalism.MainNotions.S.uMat g0 *ᵥ famSc sc e z' b) = Matrix.diagonal c a b :=
    fun g0 h a b => congrFun (congrFun h a) b
  have hBt : ∀ a b, hJ ε (Formalism.MainNotions.S.uMat g *ᵥ famSc sc e z' a) (famSc sc e z b) =
      Matrix.diagonal (fun i => conj (c i)) a b := fun a b => by
    rw [hJ_eq_conj_hJ_swap ε, hB g h1 b a, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]

  have hcc : ∀ i, c i * conj (c i) = (‖c i‖ : ℂ) ^ 2 := fun i => by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    norm_cast
  have hΔ : ∀ i, α i * γ i - c i * conj (c i) ≠ 0 := by
    intro i
    rw [hcc, hα, hγ]
    by_cases hi : i = Fin.last r
    · rw [if_pos hi, if_pos hi, hi]
      intro h0
      have h1' : ((T * T' - ‖c (Fin.last r)‖ ^ 2 : ℝ) : ℂ) = 0 := by
        push_cast
        linear_combination h0
      have := Complex.ofReal_eq_zero.mp h1'
      linarith
    · rw [if_neg hi, if_neg hi, zero_mul, zero_sub, neg_ne_zero]
      exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hc i)))
  have hΔi : ∀ i, (α i * γ i - c i * conj (c i)) * (α i * γ i - c i * conj (c i))⁻¹ = 1 :=
    fun i => mul_inv_cancel₀ (hΔ i)
  have hinv : Matrix.fromBlocks (Matrix.diagonal α) (Matrix.diagonal c) (Matrix.diagonal fun i => conj (c i))
      (Matrix.diagonal γ) *
      Matrix.fromBlocks (Matrix.diagonal fun i => γ i * (α i * γ i - c i * conj (c i))⁻¹)
        (Matrix.diagonal fun i => -c i * (α i * γ i - c i * conj (c i))⁻¹)
        (Matrix.diagonal fun i => -conj (c i) * (α i * γ i - c i * conj (c i))⁻¹)
        (Matrix.diagonal fun i => α i * (α i * γ i - c i * conj (c i))⁻¹) = 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
    rw [← Matrix.fromBlocks_one, ← Matrix.diagonal_one, ← Matrix.diagonal_zero]
    congr 1 <;> congr 1 <;> funext i
    · linear_combination hΔi i
    · ring
    · ring
    · linear_combination hΔi i
  let x : Fin (r + 1) ⊕ Fin (r + 1) → Fin n → ℂ :=
    Sum.elim (famSc sc e z) (fun b => Formalism.MainNotions.S.uMat g *ᵥ famSc sc e z' b)
  let y : Fin (r + 1) ⊕ Fin (r + 1) → Fin n → ℂ :=
    Sum.elim (famSc sc e z) (fun b => Formalism.MainNotions.S.uMat g' *ᵥ famSc sc e z' b)
  have hM : (Matrix.of fun i j => hJ ε (x i) (x j)) = Matrix.fromBlocks (Matrix.diagonal α) (Matrix.diagonal c)
      (Matrix.diagonal fun i => conj (c i)) (Matrix.diagonal γ) := by
    ext i j
    rcases i with a | a <;> rcases j with b | b
    · exact hA a b
    · exact hB g h1 a b
    · exact hBt a b
    · exact hC a b
  have hdet : (Matrix.of fun i j => hJ ε (x i) (x j)).det ≠ 0 := by
    rw [hM]
    exact Matrix.det_ne_zero_of_right_inverse hinv
  have hGram : ∀ i j, hJ ε (x i) (x j) = hJ ε (y i) (y j) := by
    intro i j
    rcases i with a | a <;> rcases j with b | b
    · rfl
    · show hJ ε (famSc sc e z a) (Formalism.MainNotions.S.uMat g *ᵥ famSc sc e z' b) =
        hJ ε (famSc sc e z a) (Formalism.MainNotions.S.uMat g' *ᵥ famSc sc e z' b)
      rw [hB g h1, hB g' h2]
    · show hJ ε (Formalism.MainNotions.S.uMat g *ᵥ famSc sc e z' a) (famSc sc e z b) =
        hJ ε (Formalism.MainNotions.S.uMat g' *ᵥ famSc sc e z' a) (famSc sc e z b)
      rw [hJ_eq_conj_hJ_swap ε (Formalism.MainNotions.S.uMat g *ᵥ _), hB g h1, hJ_eq_conj_hJ_swap ε (Formalism.MainNotions.S.uMat g' *ᵥ _), hB g' h2]
    · show hJ ε (Formalism.MainNotions.S.uMat g *ᵥ famSc sc e z' a) (Formalism.MainNotions.S.uMat g *ᵥ famSc sc e z' b) =
        hJ ε (Formalism.MainNotions.S.uMat g' *ᵥ famSc sc e z' a) (Formalism.MainNotions.S.uMat g' *ᵥ famSc sc e z' b)
      rw [isIsom_uMat ε g, isIsom_uMat ε g']
  obtain ⟨s, hs⟩ := witt_of_gram' ε x y hGram hdet
  refine ⟨s, fun a => ?_, ?_, fun b => hs (.inr b)⟩
  · have hs0 : ((sc : ℂ) ^ (r - a.1))⁻¹ ≠ 0 := by
      intro h0
      have h5 := hB g h1 a.castSucc a.castSucc
      rw [Matrix.diagonal_apply_eq, famSc_castSucc, h0, zero_smul, hJ_zero_left] at h5
      exact hc _ h5.symm
    have h4 : Formalism.MainNotions.S.uMat s *ᵥ famSc sc e z a.castSucc = famSc sc e z a.castSucc := hs (.inl a.castSucc)
    rw [famSc_castSucc, Matrix.mulVec_smul] at h4
    exact smul_right_injective _ hs0 h4
  · have h4 : Formalism.MainNotions.S.uMat s *ᵥ famSc sc e z (Fin.last r) = famSc sc e z (Fin.last r) := hs (.inl (Fin.last r))
    rwa [famSc_last'] at h4

theorem inS_of_fix {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (he : ∀ a, g *ᵥ e a = e a) (hz : g *ᵥ z = z) : InS e z g := by
  refine ⟨fun a => ?_, ?_⟩
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, he, sub_self]
    first | exact Submodule.zero_mem _ | exact zero_mem _
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, hz, sub_self]
    first | exact Submodule.zero_mem _ | exact zero_mem _

theorem diagDC_pair (sc : ℝ) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hez : ∀ a, hJ ε (e a) z = 0) (hez' : ∀ a, hJ ε (e a) z' = 0)
    (hzz : hJ ε z z = -(T : ℂ)) (hzz' : hJ ε z' z' = -(T' : ℂ))
    (c : Fin (r + 1) → ℂ) (hc : ∀ l, c l ≠ 0) (hG : 0 < Gv T T' (Matrix.diagonal c))
    (g g' : Formalism.REAL.UJ ε)
    (h1 : Zhat ε (famSc sc e z) (famSc sc e z') (Formalism.MainNotions.S.uMat g) = Matrix.diagonal c)
    (h2 : Zhat ε (famSc sc e z) (famSc sc e z') (Formalism.MainNotions.S.uMat g') = Matrix.diagonal c) :
    ∃ s s' : Formalism.REAL.UJ ε, InS e z (Formalism.MainNotions.S.uMat s) ∧ InS e z' (Formalism.MainNotions.S.uMat s') ∧ g' = s * g * s'⁻¹ := by
  obtain ⟨s, hse, hsz, hsg⟩ := diagDC_core ε sc e z z' T T' hee hez hez' hzz hzz' c hc hG g g' h1 h2
  have hmul : ∀ a b : Formalism.REAL.UJ ε, Formalism.MainNotions.S.uMat (a * b) = Formalism.MainNotions.S.uMat a * Formalism.MainNotions.S.uMat b :=
    fun _ _ => rfl
  have hinv : Formalism.MainNotions.S.uMat g'⁻¹ * Formalism.MainNotions.S.uMat g' = 1 := by
    rw [← hmul, inv_mul_cancel]
    rfl
  have hfix : ∀ b, Formalism.MainNotions.S.uMat (g'⁻¹ * s * g) *ᵥ famSc sc e z' b = famSc sc e z' b := by
    intro b
    rw [hmul, hmul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hsg b, Matrix.mulVec_mulVec, hinv,
      Matrix.one_mulVec]
  have he' : ∀ a, Formalism.MainNotions.S.uMat (g'⁻¹ * s * g) *ᵥ e a = e a := by
    intro a
    have hs0 : ((sc : ℂ) ^ (r - a.1))⁻¹ ≠ 0 := by
      intro h0
      have h5 := congrFun (congrFun h1 a.castSucc) a.castSucc
      rw [Matrix.diagonal_apply_eq] at h5
      have h3 : Zhat ε (famSc sc e z) (famSc sc e z') (Formalism.MainNotions.S.uMat g) a.castSucc a.castSucc = 0 := by
        show hJ ε (famSc sc e z a.castSucc) _ = 0
        rw [famSc_castSucc, h0, zero_smul, hJ_zero_left]
      exact hc _ (h5.symm.trans h3)
    have h4 := hfix a.castSucc
    rw [famSc_castSucc, Matrix.mulVec_smul] at h4
    exact smul_right_injective _ hs0 h4
  have hz' : Formalism.MainNotions.S.uMat (g'⁻¹ * s * g) *ᵥ z' = z' := by
    have h4 := hfix (Fin.last r)
    rwa [famSc_last'] at h4
  exact ⟨s, g'⁻¹ * s * g, inS_of_fix hse hsz, inS_of_fix he' hz', by group⟩

end Core

theorem DiagDCLoc_holds : JacobianCoordinates.DiagDCLoc := by
  intro n r k ε e z z' T T' sc hF c hc g g' h1 h2
  obtain ⟨s, s', hs, hs', hg⟩ :=
    diagDC_pair ε sc e z z' T T' hF.ee hF.ez hF.ez' hF.zz hF.zz' c hc.1 hc.2 g g' h1 h2
  exact ⟨s, hs, s', hs', hg⟩

section Glob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hJ_rvX (v : InfinitePlace X.B.I.F) (p q : (VS D).V) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (rv X.B.I v (X.crd q)) = embS D (X.pl v) ((VS D).hT p q) :=
  Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p q

theorem hermitian_z_z_eq_neg (v : InfinitePlace X.B.I.F) (u : D.what₂.Word) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -((Tw u : ℝ) : ℂ) := by
  rw [HidaSetting.zR, hJ_rvX X v, X.zu_norm u, map_neg, map_natCast]
  simp [Tw]

end Glob

theorem StepDiagDC_holds : StepDiagDC := by
  intro D X u u' sc c hc γ γ' h1 h2
  have key : ∀ v, ∃ s s' : Formalism.REAL.UJ (X.B.I.ε v),
      InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (Formalism.MainNotions.S.uMat s) ∧
      InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (Formalism.MainNotions.S.uMat s') ∧
      γ' v = s * γ v * s'⁻¹ := by
    intro v
    have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
      rw [show X.eR a = X.crd (X.eX a) from rfl, show X.eR b = X.crd (X.eX b) from rfl, hJ_rvX, X.ee, map_zero]
    have hez : ∀ (w : D.what₂.Word) a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) = 0 :=
      fun w a => by
        rw [show X.eR a = X.crd (X.eX a) from rfl, show X.zR w = X.crd (X.zu w) from rfl, hJ_rvX,
          (X.zu_orth w a).1, map_zero]
    exact diagDC_pair (X.B.I.ε v) sc _ _ _ (Tw u) (Tw u') hee (hez u) (hez u') (hermitian_z_z_eq_neg X v u) (hermitian_z_z_eq_neg X v u')
      (c v) (hc v).1 (hc v).2 (γ v) (γ' v) (h1 v) (h2 v)
  choose s s' hs hs' heq using key
  refine ⟨s, fun v => hs v, s', fun v => hs' v, ?_⟩
  funext v
  exact heq v

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries
