import Formalism.LocalToGlobal.GlobalTheory.BlockActions.RestrictionSymmetric
import Formalism.LocalToGlobal.GlobalTheory.GL4.CTEqConjTranspose

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Matrix Formalism.UG

section Gen

variable {A : Type} [CommRing A]

theorem hform_reindexB {m n : Type} [Fintype m] [Fintype n] (σ : A →+* A) (e : m ≃ n) (J : Matrix m m A) (x y : m → A) :
    hform σ (J.reindex e e) (x ∘ e.symm) (y ∘ e.symm) = hform σ J x y := by
  unfold hform
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply]

theorem hform_smul_leftB {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A) (s : A) (x y : n → A) :
    hform σ J (s • x) y = σ s * hform σ J x y := by
  unfold hform
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_smul_rightB {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A) (s : A) (x y : n → A) :
    hform σ J x (s • y) = s * hform σ J x y := by
  unfold hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gramOf_apply {m n : Type} [Fintype m] [Fintype n] (σ : A →+* A) (M : Matrix m n A) (J : Matrix m m A) (a b : n) :
    ((M.map σ)ᵀ * J * M) a b = hform σ J (fun k => M k a) (fun k => M k b) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hform, Finset.sum_mul]
  rw [Finset.sum_comm]

end Gen

variable (D : D7)

abbrev crdM : (D.sp.X D.R.m).V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m) → D.host.E) :=
  letI := D.host.cmStar
  (D.sp.X D.R.m).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D D.R.m le_rfl)).symm)

abbrev crdP : D.sp.X'.V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E) :=
  letI := D.host.cmStar
  D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)

theorem hform_frame (S : @HSpace D.host.E _ _ D.host.cmStar) (v w : S.V) :
    hform (sigD D : D.host.E →+* D.host.E) S.gram (S.frame.equivFun v) (S.frame.equivFun w) = S.hT v w := by
  letI := D.host.cmStar
  rw [Formalism.L2.GlobalTheoryTheory.TraceIntegrality.hT_expand]
  unfold hform
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, mul_assoc]
  rfl

theorem hform_crdM (v w : (D.sp.X D.R.m).V) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (crdM D v) (crdM D w) = (D.sp.X D.R.m).hT v w := by
  letI := D.host.cmStar
  have e : ∀ x, crdM D x = (D.sp.X D.R.m).frame.equivFun x ∘ (finCongr (rankN D D.R.m le_rfl)).symm := fun x => rfl
  rw [e, e]
  unfold gramN
  rw [hform_reindexB, hform_frame]

theorem hform_crdP (v w : D.sp.X'.V) :
    hform (sigD D : D.host.E →+* D.host.E) (gramP D) (crdP D v) (crdP D w) = D.sp.X'.hT v w := by
  letI := D.host.cmStar
  have e : ∀ x, crdP D x = D.sp.X'.frame.equivFun x ∘ (finCongr (rankP D)).symm := fun x => rfl
  rw [e, e]
  unfold gramP
  rw [hform_reindexB, hform_frame]

theorem iXc_eq (x : Fin (D.R.N D.R.m - 1) → D.host.E) : iXc D x = crdM D (D.sp.iX' ((crdP D).symm x)) := rfl

theorem zc_eq : zc D = crdM D D.sp.z := rfl

theorem hform_iXc (x y : Fin (D.R.N D.R.m - 1) → D.host.E) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x) (iXc D y) =
      hform (sigD D : D.host.E →+* D.host.E) (gramP D) x y := by
  letI := D.host.cmStar
  rw [iXc_eq, iXc_eq, hform_crdM, D.sp.iX'_isom, ← hform_crdP, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem hform_iXc_zc (x : Fin (D.R.N D.R.m - 1) → D.host.E) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (iXc D x) (zc D) = 0 := by
  letI := D.host.cmStar
  rw [iXc_eq, zc_eq, hform_crdM]
  exact D.sp.z_orth _

theorem hform_zc_iXc (x : Fin (D.R.N D.R.m - 1) → D.host.E) :
    hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (iXc D x) = 0 := by
  letI := D.host.cmStar
  rw [iXc_eq, zc_eq, hform_crdM, ← (D.sp.X D.R.m).herm.eq (D.sp.iX' _) D.sp.z, D.sp.z_orth, map_zero]

variable {D}

theorem gram_bZ {u : D.what₂.Word} (z0 : Fin (D.R.N D.R.m) → D.host.E) (hz : ∃ a : D.host.E, z0 = a • zc D)
    (hn : hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 z0 = ((D.mem u).A.T : D.host.E)) :
    ((bZ u z0).map (sigD D : D.host.E →+* D.host.E))ᵀ * gramN D D.R.m le_rfl * bZ u z0 =
      Matrix.reindex (finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (finSumFinEquiv.trans (finCongr (Nm_succ D.R)))
        (Matrix.fromBlocks (gramP D) 0 0 (Matrix.of fun _ _ => ((D.mem u).A.T : D.host.E)⁻¹)) := by
  obtain ⟨a, rfl⟩ := hz
  have hT : ((D.mem u).A.T : D.host.E) ≠ 0 := Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero
  have hcol1 : ∀ i : Fin (D.R.N D.R.m - 1),
      (fun k => bZ u (a • zc D) k ((finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Sum.inl i))) = iXc D (Pi.single i 1) := by
    intro i
    funext k
    have hi : (((finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Sum.inl i) : Fin (D.R.N D.R.m)) : ℕ) < D.R.N D.R.m - 1 := by
      simp
    have hi' : (⟨_, hi⟩ : Fin (D.R.N D.R.m - 1)) = i := Fin.ext (by simp)
    simp only [bZ, dif_pos hi, hi', iXm, LinearMap.toMatrix'_apply]
  have hcol2 : ∀ j : Fin 1,
      (fun k => bZ u (a • zc D) k ((finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Sum.inr j))) =
        (a / ((D.mem u).A.T : D.host.E)) • zc D := by
    intro j
    funext k
    have hj : ¬ (((finSumFinEquiv.trans (finCongr (Nm_succ D.R))) (Sum.inr j) : Fin (D.R.N D.R.m)) : ℕ) < D.R.N D.R.m - 1 := by
      simp
    simp only [bZ, dif_neg hj, Pi.smul_apply, smul_eq_mul]
    ring
  ext x y
  obtain ⟨p, rfl⟩ := (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).surjective x
  obtain ⟨q, rfl⟩ := (finSumFinEquiv.trans (finCongr (Nm_succ D.R))).surjective y
  rw [gramOf_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases p with i | i <;> rcases q with j | j
  · rw [hcol1, hcol1, hform_iXc, Matrix.fromBlocks_apply₁₁]
    simp [hform, Pi.single_apply]
  · rw [hcol1, hcol2, hform_smul_rightB, hform_iXc_zc, mul_zero, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
  · rw [hcol2, hcol1, hform_smul_leftB, hform_zc_iXc, mul_zero, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · have ha : hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (a • zc D) (a • zc D) =
        (sigD D : D.host.E →+* D.host.E) a * (a * hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (zc D)) := by
      rw [hform_smul_leftB, hform_smul_rightB]
    rw [hcol2, hcol2, hform_smul_leftB, hform_smul_rightB, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, map_div₀, map_natCast]
    rw [ha] at hn
    rw [show (sigD D : D.host.E →+* D.host.E) a / ((D.mem u).A.T : D.host.E) * (a / ((D.mem u).A.T : D.host.E) *
      hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (zc D)) =
      ((sigD D : D.host.E →+* D.host.E) a * (a * hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) (zc D) (zc D))) /
        (((D.mem u).A.T : D.host.E) * ((D.mem u).A.T : D.host.E)) by ring, hn]
    field_simp

end Formalism.L2.GlobalTheoryTheory.Br
