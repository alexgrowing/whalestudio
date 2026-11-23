import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKtypeKilledByCompactRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKtypeHolomorphicKilledByLoweringRootsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.VKill

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem conj_exp {P : Mt n} (hP : IsUnit P) (X : Mt n) (t : ℝ) :
    P * NormedSpace.exp (t • X) * P⁻¹ = NormedSpace.exp (t • (P * X * P⁻¹)) := by
  rw [← Matrix.exp_conj P _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem dRep_conj {P : Mt n} (hP : IsUnit P) (σ : Mt n → (H →L[ℂ] H)) (X : Mt n) (v : H) :
    dRep (fun g => σ (P * g * P⁻¹)) X v = dRep σ (P * X * P⁻¹) v := by
  unfold dRep
  simp only [conj_exp hP]

theorem conjH_conj {P : Mt n} (hP : IsUnit P) (J Z : Mt n) :
    conjH (Pᴴ * J * P) (P⁻¹ * Z * P) = P⁻¹ * conjH J Z * P := by
  have hd : IsUnit Pᴴ.det := by
    rw [det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hP).star
  have h1 : (Pᴴ)⁻¹ * Pᴴ = 1 := Matrix.nonsing_inv_mul _ hd
  have h2 : ∀ Y : Mt n, (Pᴴ)⁻¹ * (Pᴴ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  unfold conjH
  simp only [Matrix.mul_inv_rev, conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc, h2, Matrix.mul_neg,
    Matrix.neg_mul]

theorem dRepC_conj {P : Mt n} (hP : IsUnit P) (J : Mt n) (σ : Mt n → (H →L[ℂ] H)) (Z : Mt n) (v : H) :
    dRepC (Pᴴ * J * P) (fun g => σ (P * g * P⁻¹)) (P⁻¹ * Z * P) v = dRepC J σ Z v := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : ∀ (c : ℂ) (Y : Mt n), P * (c • (P⁻¹ * Y * P)) * P⁻¹ = c • Y := fun c Y => by
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1,
      Matrix.mul_one]
  unfold dRepC
  rw [dRep_conj hP, dRep_conj hP, conjH_conj hP, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.sub_mul, ← Matrix.mul_sub,
    h2, h2]

theorem conj_prod {P : Mt n} (hP : IsUnit P) (l : List (Mt n)) :
    P * l.prod * P⁻¹ = (l.map fun g => P * g * P⁻¹).prod := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  induction l with
  | nil => simp [Matrix.mul_nonsing_inv _ hd]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P⁻¹ P, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]

theorem smooth_conj {P : Mt n} (hP : IsUnit P) (J : Mt n) (σ : Mt n → (H →L[ℂ] H)) (v : H)
    (h : SmoothVec (lieH (Pᴴ * J * P)) (fun g => σ (P * g * P⁻¹)) v) : SmoothVec (lieH J) σ v := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : ∀ Y : Mt n, P * (P⁻¹ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hd : IsUnit Pᴴ.det := by
    rw [det_conjTranspose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 hP).star
  have h3 : (Pᴴ)⁻¹ * Pᴴ = 1 := Matrix.nonsing_inv_mul _ hd
  have h4 : ∀ Y : Mt n, (Pᴴ)⁻¹ * (Pᴴ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  intro k Xs hX
  have := h k (fun i => P⁻¹ * Xs i * P) (fun i => by
    have e : (Xs i)ᴴ * J + J * Xs i = 0 := hX i
    show (P⁻¹ * Xs i * P)ᴴ * (Pᴴ * J * P) + (Pᴴ * J * P) * (P⁻¹ * Xs i * P) = 0
    have e2 : (P⁻¹ * Xs i * P)ᴴ * (Pᴴ * J * P) + (Pᴴ * J * P) * (P⁻¹ * Xs i * P) =
        Pᴴ * ((Xs i)ᴴ * J + J * Xs i) * P := by
      simp only [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc, h2, h4, Matrix.mul_add, Matrix.add_mul]
    rw [e2, e, Matrix.mul_zero, Matrix.zero_mul])
  simp only [conj_prod hP, List.map_ofFn, Function.comp_def, conj_exp hP] at this
  simp only [Matrix.mul_assoc, h2, h1, Matrix.mul_one] at this
  exact this

theorem jm_herm (ε : Fin n → Bool) : (Formalism.REAL.Jm ε).IsHermitian := by
  unfold Formalism.REAL.Jm
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  funext a
  by_cases h : ε a <;> simp [h]

theorem jm_det (ε : Fin n → Bool) : (Formalism.REAL.Jm ε).det ≠ 0 := by
  unfold Formalism.REAL.Jm
  rw [det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  by_cases h : ε a <;> simp [h]

theorem borel_extVec (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec) (_hθ : IsInfFam θ) (hM : HolShape M) (hw : WtIs M w) (hv : IsExtVec M v)
    (τ : D.what₂.Tau) :
    SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) ∧ ∀ a c : Fin V.rank, a ≤ c →
      dRepC (gramAt D V τ) (M.rep τ) (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (v τ : M.H τ) =
        if a = c then (w τ a : ℂ) • (v τ : M.H τ) else 0 := by
  obtain ⟨hc, hU, -, hx⟩ := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ
  obtain ⟨-, hx⟩ := hx hM
  obtain ⟨hHC, p, hp, hε⟩ := hM τ
  obtain ⟨-, hlow, hwt⟩ := hv τ
  have hP := M.fr_unit τ
  have hPd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hG := M.fr_gram τ
  have hH : (gramAt D V τ).IsHermitian := by
    rw [← hG]; exact Matrix.isHermitian_conjTranspose_mul_mul _ (jm_herm _)
  have hD : (gramAt D V τ).det ≠ 0 := by
    rw [← hG, det_mul, det_mul, det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero hPd.star.ne_zero (jm_det _)) hPd.ne_zero
  have hs : SmoothVec (lieH (gramAt D V τ)) (M.rep τ) (v τ : M.H τ) :=
    (GlobalTheory.UnitarySmVec.smoothVec_basic _ _ _ _ hH hD hU).1 _ (v τ).2
  refine ⟨hs, fun a c hac => ?_⟩
  have hs' : SmoothVec (lieH (Formalism.REAL.Jm (M.ε τ))) (M.σ τ) (v τ : M.H τ) := by
    refine smooth_conj hP _ _ _ ?_
    rw [hG]; exact hs
  have hl : (v τ : M.H τ) ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) := hlow
  have hB := GlobalTheory.T.extremal_lowest_Ktype_killed_by_compact_roots _ _ _ _ _ (M.ds τ) _ hl hs' hwt
  have hm := GlobalTheory.T.lowest_Ktype_holomorphic_killed_by_lowering_roots _ p _ _ _ _ hHC hε (M.ds τ) _ hl hs'
  have e : dRepC (gramAt D V τ) (M.rep τ) (x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹) (v τ : M.H τ) =
      dRepC (Formalism.REAL.Jm (M.ε τ)) (M.σ τ)
        (Matrix.single (arr (nNeg (M.ε τ)) a) (arr (nNeg (M.ε τ)) c) 1) (v τ : M.H τ) := by
    rw [hx a c, ← hG]
    exact dRepC_conj hP _ _ _ _
  rw [e]
  split_ifs with h
  · subst h
    rw [hB.1]
    have := hw τ a
    unfold extWt at this
    rw [← this]
    simp
  · have hlt : (a : ℕ) < c := lt_of_le_of_ne hac fun h' => h (Fin.ext h')
    have hq := nNeg_shape hp hε
    have hcn := c.2
    have hsg : ∀ b : Fin V.rank, M.ε τ (arr (nNeg (M.ε τ)) b) = decide (¬ (b : ℕ) < V.rank - p) := by
      intro b
      have := b.2
      rw [hε, hq]
      unfold arr
      split_ifs with hb
      · simp only [hb, not_true_eq_false, decide_false, decide_eq_false_iff_not]; omega
      · simp only [hb, not_false_eq_true, decide_true, decide_eq_true_eq]; omega
    by_cases ha : (a : ℕ) < V.rank - p
    · by_cases hc' : (c : ℕ) < V.rank - p
      · refine hB.2 _ _ (by rw [hsg, hsg]; simp [ha, hc']) ?_
        rw [Fin.lt_def, revNeg_arr hp hε, revNeg_arr hp hε, if_pos ha, if_pos hc']
        omega
      · exact hm _ _ (by rw [hsg]; simp [hc']) (by rw [hsg]; simp [ha])
    · have hc' : ¬ (c : ℕ) < V.rank - p := by omega
      refine hB.2 _ _ (by rw [hsg, hsg]; simp [ha, hc']) ?_
      rw [Fin.lt_def, revNeg_arr hp hε, revNeg_arr hp hε, if_neg ha, if_neg hc']
      omega

end GlobalTheory.HolDict.VKill
