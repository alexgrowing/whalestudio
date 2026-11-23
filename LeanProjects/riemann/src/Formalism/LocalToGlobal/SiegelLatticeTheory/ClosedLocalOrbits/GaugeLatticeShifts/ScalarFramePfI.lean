import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfH

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cof

variable {D : D7}

theorem GZ_apply (u v : Fin (D.R.rS + 1) → (VS D).V) (a b : Fin (D.R.rS + 1)) :
    GZ u v a b = (VS D).hT (u a) (v b) := rfl

theorem GDl_top' (u v : Fin (D.R.rS + 1) → (VS D).V) : GDl u v (D.R.rS + 1) = (GZ u v).det := by
  unfold GDl
  rw [dif_pos le_rfl]
  congr 1

theorem GDl_r' (u v : Fin (D.R.rS + 1) → (VS D).V) :
    GDl u v D.R.rS = ((GZ u v).submatrix Fin.castSucc Fin.castSucc).det := by
  unfold GDl
  rw [dif_pos (Nat.le_succ _)]
  have ecs : (Fin.castLE (Nat.le_succ D.R.rS) : Fin D.R.rS → Fin (D.R.rS + 1)) = Fin.castSucc :=
    funext fun i => Fin.ext rfl
  rw [ecs]

theorem om'_pair (u v : Fin (D.R.rS + 1) → (VS D).V) (a : Fin (D.R.rS + 1)) :
    (VS D).hT (u a) (Gom' u v) = if a = Fin.last _ then GDl u v (D.R.rS + 1) else 0 := by
  have key := congrFun (congrFun (Matrix.mul_adjugate (GZ u v)) a) (Fin.last _)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at key
  rw [GDl_top']
  unfold Gom'
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [show (∑ b, (GZ u v).adjugate b (Fin.last _) * (VS D).hT (u a) (v b)) =
      ∑ b, GZ u v a b * (GZ u v).adjugate b (Fin.last _) from
    Finset.sum_congr rfl fun b _ => by rw [GZ_apply, mul_comm], key]
  split_ifs <;> simp

theorem om'_decomp (u v : Fin (D.R.rS + 1) → (VS D).V) :
    Gom' u v - GDl u v D.R.rS • v (Fin.last _) ∈ Xs (S := VS D) v := by
  unfold Gom'
  rw [Fin.sum_univ_castSucc, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, ← GDl_r', add_sub_cancel_right]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem om_pair (u v : Fin (D.R.rS + 1) → (VS D).V) (b : Fin (D.R.rS + 1)) :
    (VS D).hT (Gom u v) (v b) = if b = Fin.last _ then GDl u v (D.R.rS + 1) else 0 := by
  have key := congrFun (congrFun (Matrix.adjugate_mul (GZ u v)) (Fin.last _)) b
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at key
  rw [GDl_top']
  unfold Gom
  rw [map_sum, LinearMap.sum_apply]
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
  rw [show (∑ a, (GZ u v).adjugate (Fin.last _) a * (VS D).hT (u a) (v b)) =
      ∑ a, (GZ u v).adjugate (Fin.last _) a * GZ u v a b from rfl, key]
  rcases eq_or_ne b (Fin.last _) with hb | hb
  · subst hb
    simp
  · rw [if_neg (Ne.symm hb), if_neg hb, smul_zero]

theorem om_decomp (u v : Fin (D.R.rS + 1) → (VS D).V) :
    Gom u v - star (GDl u v D.R.rS) • u (Fin.last _) ∈ Xs (S := VS D) u := by
  unfold Gom
  rw [Fin.sum_univ_castSucc, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, ← GDl_r', add_sub_cancel_right]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem lemB (u v : Fin (D.R.rS + 1) → (VS D).V) (hdet : GDl u v (D.R.rS + 1) ≠ 0) {q : (VS D).V}
    (hq : q ∈ Submodule.span D.host.E (Set.range v)) (h : ∀ a, (VS D).hT (u a) q = 0) : q = 0 := by
  obtain ⟨π, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hq
  have hm : Matrix.mulVec (GZ u v) π = 0 := by
    funext a
    have := h a
    rw [map_sum] at this
    simp only [map_smul, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, GZ_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [GDl_top'] at hdet
  have hπ := Matrix.eq_zero_of_mulVec_eq_zero hdet hm
  simp [hπ]

theorem eq_zero_of_orth_of_det_ne_zero (u v : Fin (D.R.rS + 1) → (VS D).V) (hdet : GDl u v (D.R.rS + 1) ≠ 0) {q : (VS D).V}
    (hq : q ∈ Submodule.span D.host.E (Set.range u)) (h : ∀ b, (VS D).hT q (v b) = 0) : q = 0 := by
  obtain ⟨κ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hq
  have hm : Matrix.vecMul (fun a => star (κ a)) (GZ u v) = 0 := by
    funext b
    have := h b
    rw [map_sum, LinearMap.sum_apply] at this
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at this
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, GZ_apply]
    exact this
  rw [GDl_top'] at hdet
  have hκ := Matrix.eq_zero_of_vecMul_eq_zero hdet hm
  have : κ = 0 := by
    funext a
    have := congrFun hκ a
    simpa using this
  simp [this]

theorem lemC (v : Fin (D.R.rS + 1) → (VS D).V) (hv : LinearIndependent D.host.E v) {c : D.host.E}
    (h : c • v (Fin.last _) ∈ Xs (S := VS D) v) : c = 0 := by
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 h
  have h0 : ∑ i, (Fin.snoc (α := fun _ => D.host.E) d (-c) i) • v i = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, neg_smul]
    rw [hd, add_neg_cancel]
  have := Fintype.linearIndependent_iff.1 hv _ h0 (Fin.last _)
  simpa using this

end Cof

end Formalism.L2.SG.Pf.ScalarFramePf
