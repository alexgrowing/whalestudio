import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentIdealPowers

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gram_comb {K V ι κ : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [Fintype ι]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (v : ι → V) (A : Matrix ι κ K) (x : κ → V)
    (hx : ∀ j, x j = ∑ i, A i j • v i) : gram h x = A.conjTranspose * gram h v * A := by
  ext i j
  simp only [gram, Matrix.of_apply, hx, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
    LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem linearIndependent_of_det_gram {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K) (x : ι → V) (hd : (gram h x).det ≠ 0) :
    LinearIndependent K x := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hv : Matrix.mulVec (gram h x) c = 0 := by
    funext j
    have hj := congrArg (h (x j)) hc
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hj
    simp only [Matrix.mulVec, dotProduct, gram, Matrix.of_apply, Pi.zero_apply]
    rw [← hj]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hd hv
  intro i
  exact congrFun h0 i

variable {D : Formalism.BasicNotions.D7}

theorem flag_gram {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec a) (F.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T else 0 := by
  have hs : ∀ x y, (VS D).hT y x = star ((VS D).hT x y) := fun x y => ((VS D).herm.eq x y).symm
  rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last b with ⟨j, rfl⟩ | rfl
  · simp [FlagG.fvec, F.e_iso, Fin.castSucc_ne_last]
  · simp [FlagG.fvec, F.z_orth, Fin.castSucc_ne_last]
  · simp [FlagG.fvec, Fin.castSucc_ne_last]
    rw [hs (F.e j) F.z, F.z_orth j, star_zero]
  · simp [FlagG.fvec, F.z_norm]

theorem gram_pair {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (Z : MatZ D) (hZ : ZhatL (lf D F0) F' = Z) :
    gram (VS D).hT (Sum.elim F0.fvec F'.fl.fvec) = Ga T T' Z := by
  have hs : ∀ x y, (VS D).hT y x = star ((VS D).hT x y) := fun x y => ((VS D).herm.eq x y).symm
  subst hZ
  ext (a | a) (b | b)
  · simp [gram, Ga, flag_gram]
  · simp [gram, Ga, ZhatL, Zhat, brS]
  · simp [gram, Ga, ZhatL, Zhat, brS, Matrix.conjTranspose_apply, hs (F'.fl.fvec a)]
  · simp [gram, Ga, flag_gram]

def flagDifferenceMatrix (D : Formalism.BasicNotions.D7) :
    Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) D.host.E :=
  Matrix.fromBlocks 1 (-(((gS D : D.host.E))⁻¹ • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E))) 0
    (((gS D : D.host.E))⁻¹ • (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E))

theorem flagDifference_comb {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    ∀ j, flagDifferenceVectors D F0 F' j = ∑ i, flagDifferenceMatrix D i j • Sum.elim F0.fvec F'.fl.fvec i := by
  intro j
  rcases j with b | b
  · simp [flagDifferenceVectors, flagDifferenceMatrix, Fintype.sum_sum_type, Matrix.one_apply]
  · simp [flagDifferenceVectors, flagDifferenceMatrix, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, add_comm]

theorem det_flagDifference_matrix (D : Formalism.BasicNotions.D7) : (flagDifferenceMatrix D).det = ((gS D : D.host.E))⁻¹ ^ (D.R.rS + 1) := by
  rw [flagDifferenceMatrix, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_smul, Matrix.det_one,
    mul_one, Fintype.card_fin]

theorem star_gS (D : Formalism.BasicNotions.D7) : star ((gS D : D.host.E))⁻¹ = ((gS D : D.host.E))⁻¹ := by
  rw [star_inv₀, star_natCast]

theorem det_gram_flagDifference {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (Z : MatZ D) (hZ : ZhatL (lf D F0) F' = Z) :
    (gram (VS D).hT (flagDifferenceVectors D F0 F')).det = ((gS D : D.host.E))⁻¹ ^ (2 * (D.R.rS + 1)) * (Ga T T' Z).det := by
  rw [gram_comb (VS D).hT _ (flagDifferenceMatrix D) _ (flagDifference_comb F0 F'), gram_pair F0 F' Z hZ, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_conjTranspose, det_flagDifference_matrix, star_pow, star_gS]
  ring

theorem span_flagDifferenceBasis {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Submodule.span D.host.E (Set.range (flagDifferenceVectors D F0 F')) = UPair D F0 F' := by
  have hg : ((gS D : D.host.E)) ≠ 0 := by
    have h0 := (D.host.g_prime 0).ne_zero
    have h1 := (D.host.g_prime 1).ne_zero
    rw [gS]
    exact_mod_cast mul_ne_zero h0 h1
  unfold UPair
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with b | b
    · exact Submodule.subset_span (Or.inl ⟨b, rfl⟩)
    · simp only [flagDifferenceVectors, Sum.elim_inr]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _
        (Submodule.subset_span (Or.inr ⟨b, rfl⟩)) (Submodule.subset_span (Or.inl ⟨b, rfl⟩)))
  · rw [Submodule.span_le]
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact Submodule.subset_span ⟨Sum.inl b, rfl⟩
    · have h1 : F'.fl.fvec b = (gS D : D.host.E) • flagDifferenceVectors D F0 F' (Sum.inr b) +
          flagDifferenceVectors D F0 F' (Sum.inl b) := by
        simp only [flagDifferenceVectors, Sum.elim_inr, Sum.elim_inl, smul_smul, mul_inv_cancel₀ hg, one_smul,
          sub_add_cancel]
      rw [h1]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
        (Submodule.subset_span ⟨_, rfl⟩)

end PI.UnitaryGroupMassFormula.CntFormula.R6
