import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongrOfSignatureOfAdelicNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneTmulSmulEqAddOfAlgebraMapEqAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StandardGramVectors

open GlobalTheory.FrameComplement GlobalTheory.DetNorm

def stdGram (K : Type) [Field K] (ρ ε : ℕ) (t : K) :
    Matrix ((Fin ρ ⊕ Fin ρ) ⊕ Fin ε) ((Fin ρ ⊕ Fin ρ) ⊕ Fin ε) K :=
  fromBlocks (fromBlocks 0 1 1 0) 0 0 ((-t) • 1)

theorem hasSignature_submatrix {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {J : Matrix n n ℂ} {p q : ℕ} (h : Formalism.UG.HasSignature J p q) (e : m ≃ n) :
    Formalism.UG.HasSignature (J.submatrix e e) p q := by
  obtain ⟨c, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ h
  refine hasSignature_of_frame (by rw [Fintype.card_congr e, c]) (Q.submatrix e id) ?_
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id, hQ]

theorem hasSignature_stdGram (ρ ε : ℕ) {T : ℕ} (hT : 0 < T) :
    Formalism.UG.HasSignature (stdGram ℂ ρ ε (T : ℂ)) (ρ + 0) (ρ + ε) := by
  refine hasSignature_fromBlocks ?_ ?_
  · refine hasSignature_of_frame (by simp) (fromBlocks 1 1 ((1 / 2 : ℂ) • 1) ((-1 / 2 : ℂ) • 1)) ?_
    simp only [fromBlocks_conjTranspose, fromBlocks_multiply, Formalism.UG.Jpq, conjTranspose_smul, conjTranspose_one]
    ext (r | r) (s | s) <;> by_cases h : r = s <;> simp [h] <;> norm_num
  · have h1 : ((√(T : ℝ) : ℝ) : ℂ) * ((√(T : ℝ) : ℝ) : ℂ) = T := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg T)]; simp
    have h2 : ((√(T : ℝ) : ℝ) : ℂ) ≠ 0 := fun h => by
      rw [h, mul_zero] at h1
      exact hT.ne' (by exact_mod_cast h1.symm)
    refine hasSignature_of_frame (by simp) (fromCols 0 ((((√(T : ℝ) : ℝ) : ℂ))⁻¹ • 1)) ?_
    ext (r | r) (s | s)
    · exact r.elim0
    · exact r.elim0
    · exact s.elim0
    · rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols]
      by_cases h : r = s
      · simp [h, Formalism.UG.Jpq]
        rw [← h1]; field_simp
      · simp [h, Formalism.UG.Jpq]

theorem det_stdGram (K : Type) [Field K] (ρ ε : ℕ) (t : K) :
    ∃ s : K, s * s = 1 ∧ (stdGram K ρ ε t).det = s * (-t) ^ ε := by
  refine ⟨(fromBlocks 0 1 1 0 : Matrix (Fin ρ ⊕ Fin ρ) (Fin ρ ⊕ Fin ρ) K).det, ?_, ?_⟩
  · rw [← Matrix.det_mul, Matrix.fromBlocks_multiply]
    simp
  · rw [stdGram, det_fromBlocks_zero₂₁, det_smul, det_one, mul_one, Fintype.card_fin]

theorem gram_comb {E : Type} [Field E] [NumberField E] [StarRing E] (Y : HSpace E) {c : ℕ} (b : Fin c → Y.V)
    (P : Matrix (Fin c) (Fin c) E) (k l : Fin c) :
    Y.hT (∑ i, P i k • b i) (∑ i, P i l • b i) = (Pᴴ * (Matrix.of fun i l => Y.hT (b i) (b l)) * P) k l := by
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_smul,
    LinearMap.map_smulₛₗ₂, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem isN_pow {D : D7} {x : D.host.E} (h : IsN D x) (n : ℕ) : IsN D (x ^ n) := by
  induction n with
  | zero => simpa using isN_star (D := D) 1
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem exists_std (D : D7) (j : ℕ) (hj : j < D.R.m) :
    ∃ w : (Fin ((D.R.m - 1 - j) / 2) ⊕ Fin ((D.R.m - 1 - j) / 2)) ⊕ Fin ((D.R.m - 1 - j) % 2) → (D.sp.Y j).V,
      (∀ k x, (D.sp.Y j).hT (D.sp.iXY j x) (w k) = 0) ∧
      ∀ k l, (D.sp.Y j).hT (w k) (w l) = stdGram D.host.E _ _ (D.sp.T : D.host.E) k l := by
  obtain ⟨b, hb, hd, hs, a, ha, hdet⟩ := exists_complement_XY D j hj
  generalize D.R.m - 1 - j = c at *
  have hT : 0 < D.sp.T := D.sp.T_prime.pos
  obtain ⟨e⟩ : Nonempty (Fin c ≃ (Fin (c / 2) ⊕ Fin (c / 2)) ⊕ Fin (c % 2)) :=
    Fintype.card_eq.1 (by simp; omega)
  obtain ⟨s, hs1, hs2⟩ := det_stdGram D.host.E (c / 2) (c % 2) (D.sp.T : D.host.E)
  have hsN : IsN D s ∧ star s = s := by
    rcases mul_self_eq_one_iff.1 hs1 with h | h
    · rw [h]; exact ⟨by simpa using isN_star (D := D) 1, star_one _⟩
    · rw [h]; exact ⟨isN_neg_one, by simp⟩
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs1
  have hT0 : (D.sp.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT.ne'
  have hX := GlobalTheory.FrameComplement.gram_det_ne (D.sp.X j)
  obtain ⟨P, -, hP⟩ := GlobalTheory.HermAdelicNorm.congr_of_signature_of_adelic_norm D.host.F D.host.E D.sp.cm c
    (Matrix.of fun i l => (D.sp.Y j).hT (b i) (b l))
    ((stdGram D.host.E (c / 2) (c % 2) (D.sp.T : D.host.E)).submatrix e e)
    (Matrix.ext fun i l => (D.sp.Y j).herm.eq _ _)
    (by simp [stdGram, conjTranspose_submatrix, fromBlocks_conjTranspose]) hd
    (by rw [det_submatrix_equiv_self, hs2]; exact mul_ne_zero hs0 (pow_ne_zero _ (neg_ne_zero.2 hT0)))
    (fun τ => ⟨_, _, hs τ, by
      have h1 : ((stdGram D.host.E (c / 2) (c % 2) (D.sp.T : D.host.E)).submatrix e e).map τ =
          (stdGram ℂ (c / 2) (c % 2) (D.sp.T : ℂ)).submatrix e e := by
        ext r t
        simp only [map_apply, submatrix_apply]
        rcases e r with (r | r) | r <;> rcases e t with (t | t) | t <;>
          simp [stdGram, Matrix.one_apply, apply_ite τ]
      rw [h1]
      convert hasSignature_submatrix (hasSignature_stdGram (c / 2) (c % 2) hT) e using 1 <;> omega⟩)
    (by
      have h1 : IsN D (-(D.sp.T : D.host.E)) := by simpa using (isN_neg_one (D := D)).mul isNormFromTensorFiniteAdele_levelNormT
      have h2 := (((isN_det (D.sp.Y j)).mul ((isN_det (D.sp.X j)).inv (star_det _))).mul (isN_star a⁻¹)).mul
        ((hsN.1.mul (isN_pow h1 (c % 2))).inv (by simp [hsN.2]))
      have ha' : star a ≠ 0 := star_ne_zero.2 ha
      have h3 : ∀ x g u : D.host.E, x ≠ 0 → star a * a * x * g * x⁻¹ * (star a⁻¹ * a⁻¹) * u⁻¹ = g / u :=
        fun x g u hx => by rw [star_inv₀, div_eq_mul_inv]; field_simp
      rw [hdet, h3 _ _ _ hX] at h2
      rw [det_submatrix_equiv_self, hs2]
      exact h2)
  refine ⟨fun k => ∑ i, P i (e.symm k) • b i, fun k x => ?_, fun k l => ?_⟩
  · simp [hb]
  · rw [gram_comb, hP, submatrix_apply, e.apply_symm_apply, e.apply_symm_apply]

theorem exists_auxiliaryHyperbolicVectors : ∀ (D : D7) (j : ℕ), j < D.R.m → ∃ (E Ev : ℕ → (D.sp.Y j).V) (z : (D.sp.Y j).V), GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.IsAuxiliaryHeckeCharacter D j E Ev z := by
  intro D j hj
  obtain ⟨w, h0, hw⟩ := exists_std D j hj
  refine ⟨fun i => if h : i < (D.R.m - 1 - j) / 2 then w (.inl (.inl ⟨i, h⟩)) else 0,
    fun i => if h : i < (D.R.m - 1 - j) / 2 then w (.inl (.inr ⟨i, h⟩)) else 0,
    if h : 0 < (D.R.m - 1 - j) % 2 then w (.inr ⟨0, h⟩) else 0, ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.IsAuxiliaryHeckeCharacter GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.nAux HSpace.hD
  refine ⟨fun i hi l hl => ?_, fun i hi x => ?_, fun he => ?_⟩
  · simp only [dif_pos hi, dif_pos hl, hw]
    simp [stdGram, Matrix.one_apply, Fin.ext_iff, eq_comm]
  · simp only [dif_pos hi, h0, and_self]
  · have h : 0 < (D.R.m - 1 - j) % 2 := by
      obtain ⟨a, ha⟩ := D.R.m_even
      obtain ⟨b, hb⟩ := he
      omega
    refine ⟨?_, fun x => ?_, fun i hi => ?_⟩
    · simp only [dif_pos h, hw]; simp [stdGram]
    · simp only [dif_pos h, h0]
    · simp only [dif_pos h, dif_pos hi, hw]; simp [stdGram]

end GlobalTheory.StandardGramVectors
