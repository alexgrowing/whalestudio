import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.Frame

section Generic
variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

theorem submatrix_fromBlocks_mul (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrixTwoByTwoFin_smul (r : R) (a b c d : Matrix (Fin n) (Fin n) R) :
    r • blk4 a b c d = blk4 (r • a) (r • b) (r • c) (r • d) := by
  unfold blk4
  rw [← Matrix.fromBlocks_smul]; rfl

theorem block_matrix_map (f : R → S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4
  rw [← Matrix.fromBlocks_map]; rfl

theorem blockMatrixTwoByTwoFin_transpose (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d)ᵀ = blk4 aᵀ cᵀ bᵀ dᵀ := by
  unfold blk4
  rw [← Matrix.fromBlocks_transpose]; rfl

theorem blockMatrixTwoByTwoFin_forall_entries (p : R → Prop) {a b c d : Matrix (Fin n) (Fin n) R} (ha : ∀ i j, p (a i j)) (hb : ∀ i j, p (b i j))
    (hc : ∀ i j, p (c i j)) (hd : ∀ i j, p (d i j)) (i j : Fin (n + n)) : p (blk4 a b c d i j) := by
  unfold blk4
  rw [Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
  exacts [ha i j, hb i j, hc i j, hd i j]

theorem map_smul_hom (f : R →+* S) {m : Type} (r : R) (a : Matrix m m R) : (r • a).map f = f r • a.map f := by
  ext i j; simp

def frm (K : Matrix (Fin n) (Fin n) R) (e t t' : R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  blk4 1 ((e * t) • K) 1 ((-(e * t')) • K)

def frmInv (H : Matrix (Fin n) (Fin n) R) (e' t t' : R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  blk4 (t' • 1) (t • 1) (e' • H) ((-e') • H)

variable {H K : Matrix (Fin n) (Fin n) R} {e e' t t' : R}

theorem frm_mul_inv (hKH : K * H = 1) (he : e * e' = 1) (ht : t + t' = 1) :
    frm K e t t' * frmInv H e' t t' = 1 := by
  unfold frm frmInv
  rw [submatrix_fromBlocks_mul, ← block_matrix_one]
  simp only [Matrix.smul_mul, Matrix.mul_smul, hKH, Matrix.one_mul, smul_smul, ← add_smul]
  congr 1
  · rw [show t' + e' * (e * t) = 1 by linear_combination ht + t * he, one_smul]
  · rw [show t + -e' * (e * t) = 0 by linear_combination (-t) * he, zero_smul]
  · rw [show t' + e' * (-(e * t')) = 0 by linear_combination (-t') * he, zero_smul]
  · rw [show t + -e' * (-(e * t')) = 1 by linear_combination ht + t' * he, one_smul]

theorem adj_frm (c : R →+* R) (hK : (K.map c)ᵀ = K) (hct : c t = t') (hct' : c t' = t) :
    ((frm K e t t').map c)ᵀ = blk4 1 1 ((c e * t') • K) ((-(c e * t)) • K) := by
  unfold frm
  rw [block_matrix_map, blockMatrixTwoByTwoFin_transpose, map_smul_hom, map_smul_hom, Matrix.transpose_smul, Matrix.transpose_smul, hK,
    Matrix.map_one _ c.map_zero c.map_one, Matrix.transpose_one, map_neg, map_mul, map_mul, hct, hct']

theorem gram_frm (ce : R) (hKH : K * H = 1) (hHK : H * K = 1) (ht : t + t' = 1) :
    blk4 1 1 ((ce * t') • K) ((-(ce * t)) • K) * blk4 H 0 0 (-H) * frm K e t t' = blk4 0 (e • 1) (ce • 1) 0 := by
  unfold frm
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, hKH, hHK, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, smul_neg, ← neg_smul, smul_smul, ← add_smul]
  congr 1
  · simp
  · congr 1; linear_combination e * ht
  · congr 1; linear_combination ce * ht
  · convert zero_smul R K using 2; ring

theorem norm_frm (ce : R) (f : R →+* S) (hK : (K * K).map f = 1) (ht : t + t' = 1) (h2 : f (2 * t) = 1)
    (h4 : f (e * ce) = 4) :
    (blk4 1 1 ((ce * t') • K) ((-(ce * t)) • K) * frm K e t t').map f = (2 : S) • 1 := by
  unfold frm
  have ht' : f t + f t' = 1 := by rw [← map_add, ht, map_one]
  have h2' : 2 * f t = 1 := by rw [← h2, map_mul, map_ofNat]
  rw [map_mul] at h4
  rw [submatrix_fromBlocks_mul, ← block_matrix_one, blockMatrixTwoByTwoFin_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, ← add_smul]
  rw [block_matrix_map, map_smul_hom, map_smul_hom, map_smul_hom, hK, smul_zero]
  congr 1
  · rw [← two_smul R, map_smul_hom, Matrix.map_one _ f.map_zero f.map_one, map_ofNat]
  · convert zero_smul S _ using 2
    simp only [map_add, map_neg, map_mul]
    linear_combination f e * h2' - f e * ht'
  · convert zero_smul S _ using 2
    simp only [map_add, map_neg, map_mul]
    linear_combination f ce * ht' - f ce * h2'
  · congr 1
    simp only [map_add, map_neg, map_mul]
    linear_combination (2 * f t * f t') * h4 + (8 * f t) * ht' + (2 - 4 * f t) * h2'

theorem exists_frame_ring (c : R →+* R) (hc : ∀ x, c (c x) = x) (p : R → Prop) (p0 : p 0) (p1 : p 1)
    (pmul : ∀ {x y}, p x → p y → p (x * y)) (pneg : ∀ {x}, p x → p (-x)) (pc : ∀ {x}, p x → p (c x))
    (Hm : GL (Fin n) R) (hH' : (Hm.1.map c)ᵀ = Hm.1) (hI1 : ∀ i j, p (Hm.1 i j)) (hI2 : ∀ i j, p ((Hm⁻¹).1 i j))
    (m : R) (hm : c m = -m) (u ε : Rˣ) (t : R) (hs1 : (ε : R) * u * c u = m) (hs2 : p ε) (hs3 : p (ε⁻¹ : Rˣ))
    (ht1 : t + c t = 1) (ht2 : p t) :
    ∃ M M' : GL (Fin (n + n)) R, (M.1.map c)ᵀ * blk4 Hm.1 0 0 (-Hm.1) * M.1 = m • blk4 0 1 (-1) 0 ∧
      (∀ i j : Fin n, M.1 (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)) =
        M.1 (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n))) ∧
      ((∀ i j, p (M'.1 i j)) ∧ ∀ i j, p ((M'⁻¹).1 i j)) ∧ M.1 = (u : R) • M'.1 ∧
      ∀ (S : Type) [CommRing S] (f : R →+* S), (Hm.1 * Hm.1).map f = 1 → f (ε * c ε) = 4 → f (2 * t) = 1 →
        ((M.1.map c)ᵀ * M.1).map f = f (2 * u * c u) • 1 := by
  have hKH : (Hm⁻¹).1 * Hm.1 = 1 := Units.inv_mul Hm
  have hHK : Hm.1 * (Hm⁻¹).1 = 1 := Units.mul_inv Hm
  generalize (Hm⁻¹).1 = K at hKH hHK hI2
  have pone : ∀ i j : Fin n, p ((1 : Matrix (Fin n) (Fin n) R) i j) := fun i j => by
    rw [Matrix.one_apply]
    split_ifs
    exacts [p1, p0]
  have hK : (K.map c)ᵀ = K := by
    have h1 : Hm.1 * (K.map c)ᵀ = 1 := by
      conv_lhs => rw [← hH']
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hKH, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    calc (K.map c)ᵀ = K * (Hm.1 * (K.map c)ᵀ) := by rw [← Matrix.mul_assoc, hKH, Matrix.one_mul]
      _ = K := by rw [h1, Matrix.mul_one]
  have hinv := frm_mul_inv (e := (ε : R)) (e' := ((ε⁻¹ : Rˣ) : R)) hKH (Units.mul_inv ε) ht1
  have hadj := adj_frm (e := (ε : R)) c hK rfl (hc t)
  let M' : GL (Fin (n + n)) R := ⟨_, _, hinv, mul_eq_one_comm.1 hinv⟩
  let M : GL (Fin (n + n)) R := ⟨(u : R) • M'.1, ((u⁻¹ : Rˣ) : R) • (M'⁻¹).1,
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.mul_inv, Units.mul_inv, one_smul],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.inv_mul, Units.inv_mul, one_smul]⟩
  have hM : M.1 = (u : R) • frm K (ε : R) t (c t) := rfl
  have hadjM : (M.1.map c)ᵀ = c u • blk4 1 1 ((c ε * c t) • K) ((-(c ε * t)) • K) := by
    rw [← hadj, hM, ← Matrix.transpose_smul, ← map_smul_hom]
  have hcε : c ε * u * c u = -m := by
    have h := congrArg c hs1
    rw [map_mul, map_mul, hc, hm] at h
    linear_combination h
  refine ⟨M, M', ?_, ?_, ⟨?_, ?_⟩, rfl, fun S _ f hR h4 h2 => ?_⟩
  · rw [hadjM, hM, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, gram_frm _ hKH hHK ht1, smul_smul,
      blockMatrixTwoByTwoFin_smul, blockMatrixTwoByTwoFin_smul, smul_zero, smul_zero, smul_smul, smul_smul, smul_neg, ← neg_smul, ← hcε, ← hs1]
    congr 2 <;> ring
  · intro i j
    rw [hM]
    simp only [frm, blk4, Matrix.smul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]
  · exact blockMatrixTwoByTwoFin_forall_entries p pone (fun i j => pmul (pmul hs2 ht2) (hI2 i j)) pone
      (fun i j => pmul (pneg (pmul hs2 (pc ht2))) (hI2 i j))
  · exact blockMatrixTwoByTwoFin_forall_entries p (fun i j => pmul (pc ht2) (pone i j))
      (fun i j => pmul ht2 (pone i j)) (fun i j => pmul hs3 (hI1 i j))
      (fun i j => pmul (pneg hs3) (hI1 i j))
  · have hKK : (K * K).map f = 1 := by
      have h1 : K * K * (Hm.1 * Hm.1) = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc K Hm.1, hKH, Matrix.one_mul, hKH]
      have h3 : (K * K * (Hm.1 * Hm.1)).map f = (1 : Matrix (Fin n) (Fin n) R).map f := by rw [h1]
      rwa [Matrix.map_mul, hR, Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h3
    rw [hadjM, hM, Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_smul_hom,
      norm_frm _ _ hKK ht1 h2 h4, smul_smul]
    congr 1
    simp only [map_mul, map_ofNat]
    ring

theorem blockMatrixTwoByTwoFin_standardSkew_map (f : R →+* S) :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0).map f = blk4 0 1 (-1) 0 := by
  rw [block_matrix_map, Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _),
    Matrix.map_one _ (map_zero _) (map_one _)]

end Generic

variable {D : D7}

theorem compFin_cA (v : HeightOneSpectrum (𝓞 D.host.F)) (z : AE D) :
    compFin D.host.F D.host.E v (cA D z) = sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

theorem intA_cA {z : AE D} (h : IntA z) : IntA (cA D z) := fun v => by
  rw [compFin_cA]; exact sigR_mem_intLoc _ (h v)

theorem intA_mul {x y : AE D} (hx : IntA x) (hy : IntA y) : IntA (x * y) := fun v => by
  rw [map_mul]; exact Subring.mul_mem _ (hx v) (hy v)

theorem intA_neg {x : AE D} (hx : IntA x) : IntA (-x) := fun v => by
  rw [map_neg]; exact Subring.neg_mem _ (hx v)

theorem intA_zero : IntA (0 : AE D) := fun v => by
  rw [map_zero]; exact Subring.zero_mem _

theorem intA_one : IntA (1 : AE D) := fun v => by
  rw [map_one]; exact Subring.one_mem _

theorem cA_incA_skew {μ : D.host.E} (h : IsSkew μ) : cA D (incA D μ) = -incA D μ := by
  rw [show cA D (incA D μ) = incA D (star μ) from rfl, h.2, map_neg]

theorem rat_Jst (n : ℕ) : (rat (Jst D n) : Mx D (n + n) (n + n)) = blk4 0 1 (-1) 0 := blockMatrixTwoByTwoFin_standardSkew_map (incA D)

theorem exists_frame : ∀ (D : D7) (n : ℕ) (Hm : GL (Fin n) (AE D)), adj Hm.1 = Hm.1 → IntGL Hm → (∀ w, (Hm.1 * Hm.1).map (compInf D.host.F D.host.E w) = 1) → ∀ (μ : D.host.E) (u ε : (AE D)ˣ) (t : AE D), IsSkew μ → ScalData μ u ε → HalfData t → ∃ M M' : GL (Fin (n + n)) (AE D), adj M.1 * dblGram finSumFinEquiv Hm.1 * M.1 = incA D μ • rat (Jst D n) ∧ (∀ i j : Fin n, M.1 (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)) = M.1 (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n))) ∧ IntGL M' ∧ M.1 = (u : AE D) • M'.1 ∧ ∀ w, (adj M.1 * M.1).map (compInf D.host.F D.host.E w) = compInf D.host.F D.host.E w (2 * u * cA D u) • 1 := by
  intro D n Hm hH hI hR μ u ε t hμ hs ht
  obtain ⟨M, M', h1, h2, h3, h4, h5⟩ := exists_frame_ring (cA D) Formalism.L2.Theta.cA_cA IntA intA_zero intA_one
    intA_mul intA_neg intA_cA Hm hH hI.1 hI.2 (incA D μ) (cA_incA_skew hμ) u ε t hs.1 hs.2.1 hs.2.2.1 ht.1 ht.2.1
  refine ⟨M, M', ?_, h2, h3, h4, fun w => h5 _ _ (hR w) (hs.2.2.2 w) (ht.2.2 w)⟩
  rw [rat_Jst]
  exact h1

end GlobalTheory.StdUnn.Frame

end
