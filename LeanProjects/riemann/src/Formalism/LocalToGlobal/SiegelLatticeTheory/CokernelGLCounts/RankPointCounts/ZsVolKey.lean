import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.SpanPerpZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBStable

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolKey

open Formalism.L2.SG.Pf.StabilizerIndexVolumes Matrix

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T T' : E}

theorem act_inv (f : Fin (r + 1) → S.V) (s : S.V ≃ₗ[E] S.V) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hP : P * P⁻¹ = 1) (hs : ∀ b, s (f b) = ∑ c, P c b • f c) (b : Fin (r + 1)) :
    s (∑ c, P⁻¹ c b • f c) = f b := by
  simp only [map_sum, map_smul, hs, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have h1 : ∀ d, ∑ c, P⁻¹ c b * P d c = (P * P⁻¹) d b := fun d => by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  simp only [h1, hP, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem up_inv_mul {P : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hP : Formalism.MainNotions.S.IsUpUni P) : P * P⁻¹ = 1 := by
  have htri : P.BlockTriangular id := fun i j hij => (hP i j).1 hij
  have hdet : P.det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => (hP i i).2 rfl
  exact Matrix.mul_nonsing_inv P (by rw [hdet]; exact isUnit_one)

theorem eq_sL (F : Formalism.MainNotions.S.FlagG S r T) (F' : Formalism.MainNotions.S.FlagG S r T') (hG : IsUnit (gramOf (gg F F')).det)
    (s : S.V ≃ₗ[E] S.V) (hs : ∀ x y, S.hT (s x) (s y) = S.hT x y)
    (P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hP : Formalism.MainNotions.S.IsUpUni P) (hQ : Formalism.MainNotions.S.IsUpUni Q)
    (hsf : ∀ b, s (F.fvec b) = ∑ c, P c b • F.fvec c) (hsf' : ∀ b, s (F'.fvec b) = ∑ c, Q c b • F'.fvec c)
    (hsX : ∀ x, (∀ i, S.hT (F.e i) x = 0) → s x - x ∈ Submodule.span E (Set.range F.e)) (x : S.V) :
    s x = sL (gg F F') (UU P Q) x := by
  classical
  have hframe : ∀ m, s (gg F F' m) = sL (gg F F') (UU P Q) (gg F F' m) := by
    intro m
    cases m with
    | inl b =>
      show s (F.fvec b) = sL (gg F F') (UU P Q) (F.fvec b)
      rw [hsf, sL_frame (F := F) (F' := F') hG P Q b]
    | inr b =>
      show s (F'.fvec b) = sL (gg F F') (UU P Q) (F'.fvec b)
      rw [hsf', sL_frame' (F := F) (F' := F') hG P Q b]
  have hy : ∀ l, S.hT (gg F F' l) (x - ∑ m, cOf (gg F F') x m • gg F F' m) = 0 := by
    intro l
    have h1 := congrFun (gram_cOf (gg F F') hG x) l
    rw [map_sub, map_sum, ← h1]
    simp only [map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, gramOf]
    rw [sub_eq_zero]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have hspan0 : ∀ w ∈ Submodule.span E (Set.range (gg F F')),
      S.hT w (x - ∑ m, cOf (gg F F') x m • gg F F' m) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      exact hy l
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
    | smul a v _ hv => rw [map_smulₛₗ, LinearMap.smul_apply, hv, smul_zero]
  have hpre : ∀ l, ∃ w ∈ Submodule.span E (Set.range (gg F F')), s w = gg F F' l := by
    intro l
    cases l with
    | inl b =>
      refine ⟨∑ c, P⁻¹ c b • F.fvec c, Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl c, rfl⟩), ?_⟩
      exact act_inv F.fvec s P (up_inv_mul hP) hsf b
    | inr b =>
      refine ⟨∑ c, Q⁻¹ c b • F'.fvec c, Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr c, rfl⟩), ?_⟩
      exact act_inv F'.fvec s Q (up_inv_mul hQ) hsf' b
  have hsy : s (x - ∑ m, cOf (gg F F') x m • gg F F' m) = x - ∑ m, cOf (gg F F') x m • gg F F' m := by
    have hy' : ∀ i, S.hT (F.e i) (x - ∑ m, cOf (gg F F') x m • gg F F' m) = 0 := by
      intro i
      have h2 := hy (Sum.inl i.castSucc)
      simpa [gg, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h2
    have hmem := hsX _ hy'
    have hdspan : s (x - ∑ m, cOf (gg F F') x m • gg F F' m) - (x - ∑ m, cOf (gg F F') x m • gg F F' m) ∈
        Submodule.span E (Set.range (gg F F')) := by
      refine Submodule.span_mono ?_ hmem
      rintro _ ⟨i, rfl⟩
      exact ⟨Sum.inl i.castSucc, by simp [gg, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]⟩
    have hdperp : ∀ l, S.hT (gg F F' l)
        (s (x - ∑ m, cOf (gg F F') x m • gg F F' m) - (x - ∑ m, cOf (gg F F') x m • gg F F' m)) = 0 := by
      intro l
      obtain ⟨w, hw, hwl⟩ := hpre l
      rw [map_sub, hy l, sub_zero, ← hwl, hs, hspan0 w hw]
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hdspan
    have hc0 : cOf (gg F F') (s (x - ∑ m, cOf (gg F F') x m • gg F F' m) -
        (x - ∑ m, cOf (gg F F') x m • gg F F' m)) = 0 := by
      rw [cOf_eq]
      have hz : (fun l => S.hT (gg F F' l) (s (x - ∑ m, cOf (gg F F') x m • gg F F' m) -
          (x - ∑ m, cOf (gg F F') x m • gg F F' m))) = 0 := funext hdperp
      rw [hz, Matrix.mulVec_zero]
    have hca : cOf (gg F F') (∑ m, a m • gg F F' m) = a := by
      have h3 := cOf_comb (gg F F') hG 0 a
      rw [zero_add] at h3
      rw [h3]
      have h4 := cOf_smul (gg F F') 0 0
      rw [zero_smul, zero_smul] at h4
      rw [h4, zero_add]
    rw [ha] at hca
    rw [hc0] at hca
    rw [← sub_eq_zero, ← ha, ← hca]
    simp
  have hx : x = (x - ∑ m, cOf (gg F F') x m • gg F F' m) + ∑ m, cOf (gg F F') x m • gg F F' m := by
    rw [sub_add_cancel]
  rw [hx, map_add, map_add, map_sum, map_sum, hsy, sL_perp (F := F) (F' := F') hG _ hy]
  congr 1
  exact Finset.sum_congr rfl fun m _ => by rw [map_smul, map_smul, hframe m]

theorem nlam_of_frames (F : Formalism.MainNotions.S.FlagG S r T) (F' : Formalism.MainNotions.S.FlagG S r T') (hG : IsUnit (gramOf (gg F F')).det)
    (hZu : IsUnit (Formalism.MainNotions.S.Zhat F F').det)
    (s : S.V ≃ₗ[E] S.V) (hs : ∀ x y, S.hT (s x) (s y) = S.hT x y)
    (P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hP : Formalism.MainNotions.S.IsUpUni P) (hQ : Formalism.MainNotions.S.IsUpUni Q)
    (hsf : ∀ b, s (F.fvec b) = ∑ c, P c b • F.fvec c) (hsf' : ∀ b, s (F'.fvec b) = ∑ c, Q c b • F'.fvec c)
    (hsX : ∀ x, (∀ i, S.hT (F.e i) x = 0) → s x - x ∈ Submodule.span E (Set.range F.e)) :
    (∀ j, ∀ x ∈ F'.Xa (j + 1), s x - x ∈ F'.Xa j) ∧
      (∀ x, (∀ i, S.hT (F'.e i) x = 0) → s x - x ∈ Submodule.span E (Set.range F'.e)) := by
  have hQd : Q.det = 1 := by
    have htri : Q.BlockTriangular id := fun i j hij => (hQ i j).1 hij
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => (hQ i i).2 rfl
  have hmat : P.conjTranspose * Formalism.MainNotions.S.Zhat F F' * Q = Formalism.MainNotions.S.Zhat F F' := by
    ext a b
    have h := hs (F.fvec a) (F'.fvec b)
    rw [hsf, hsf'] at h
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      Finset.mul_sum] at h
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS]
    rw [← h, Finset.sum_comm]
    simp only [Finset.sum_mul, RingHom.id_apply, starRingEnd_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => by ring
  have hZH : IsUnit (Formalism.MainNotions.S.Zhat F F').conjTranspose.det := by
    rw [Matrix.det_conjTranspose]
    exact hZu.star
  have hQH : IsUnit Q.conjTranspose.det := by
    rw [Matrix.det_conjTranspose, hQd, star_one]
    exact isUnit_one
  have h2 : Q.conjTranspose * (Formalism.MainNotions.S.Zhat F F').conjTranspose * P = (Formalism.MainNotions.S.Zhat F F').conjTranspose := by
    have h3 := congrArg Matrix.conjTranspose hmat
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc] at h3
  have e1 : (Formalism.MainNotions.S.Zhat F F').conjTranspose * P = (Q.conjTranspose)⁻¹ * (Formalism.MainNotions.S.Zhat F F').conjTranspose := by
    conv_rhs => rw [← h2]
    rw [Matrix.mul_assoc Q.conjTranspose, ← Matrix.mul_assoc (Q.conjTranspose)⁻¹, Matrix.nonsing_inv_mul _ hQH,
      Matrix.one_mul]
  have hrel : P = ((Formalism.MainNotions.S.Zhat F F').conjTranspose)⁻¹ * (Q.conjTranspose)⁻¹ * (Formalism.MainNotions.S.Zhat F F').conjTranspose := by
    rw [Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hZH, Matrix.one_mul]
  have hQl : Formalism.MainNotions.S.IsLoUni Q.conjTranspose := fun i j =>
    ⟨fun h => by simp [Matrix.conjTranspose_apply, (hQ j i).1 h],
     fun h => by subst h; simp [Matrix.conjTranspose_apply, (hQ i i).2 rfl]⟩
  refine ⟨fun j x hx => ?_, fun x hx => ?_⟩
  · rw [eq_sL F F' hG s hs P Q hP hQ hsf hsf' hsX x]
    exact sL_Xa' (F := F) (F' := F') hG hQ j x hx
  · rw [eq_sL F F' hG s hs P Q hP hQ hsf hsf' hsX x]
    exact sL_orth' (F := F) (F' := F') hG hQ hZH hrel (loUni_inv hQl) x hx

end Formalism.L2.SG.Pf.ZsVolKey

end
