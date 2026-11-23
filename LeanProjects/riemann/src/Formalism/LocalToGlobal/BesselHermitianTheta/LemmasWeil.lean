import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Matrix
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {R : Type*} [CommRing R] (c : R →+* R) {n m : ℕ}

theorem sum_eq_trace (J : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R) (x y : Matrix (Fin n) (Fin m) R) :
    ∑ i, ∑ j, ∑ k, ∑ l, c (x i j) * J k i * K j l * y k l = ((x.map c)ᵀ * Jᵀ * y * Kᵀ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem inv_hom (hc : ∀ a, c (c a) = a) (J g : Matrix (Fin n) (Fin n) R) (K h : Matrix (Fin m) (Fin m) R)
    (hg : (g.map c)ᵀ * J * g = J) (hh : (h.map c)ᵀ * K * h = K) (x y : Matrix (Fin n) (Fin m) R) :
    (((g.map c * x * hᵀ).map c)ᵀ * Jᵀ * (g.map c * y * hᵀ) * Kᵀ).trace = ((x.map c)ᵀ * Jᵀ * y * Kᵀ).trace := by
  have hgg : (g.map c).map c = g := by
    ext i j
    simp [hc]
  have e1 : (g.map c * x * hᵀ).map c = g * x.map c * (h.map c)ᵀ := by
    rw [Matrix.map_mul, Matrix.map_mul, hgg, Matrix.transpose_map]
  have h1 : gᵀ * Jᵀ * g.map c = Jᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hg
  have hg2 : ∀ M : Matrix (Fin n) (Fin m) R, gᵀ * (Jᵀ * (g.map c * M)) = Jᵀ * M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1]
  have hh1 : hᵀ * Kᵀ * h.map c = Kᵀ := by
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using congrArg Matrix.transpose hh
  have hh2 : hᵀ * (Kᵀ * h.map c) = Kᵀ := by
    rw [← Matrix.mul_assoc, hh1]
  rw [e1]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, hg2]
  conv_lhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hh2]

theorem inv_hom' (hc : ∀ a, c (c a) = a) (J g : Matrix (Fin n) (Fin n) R) (K h : Matrix (Fin m) (Fin m) R)
    (hg : (g.map c)ᵀ * J * g = J) (hh : (h.map c)ᵀ * K * h = K) (x y : Matrix (Fin n) (Fin m) R) :
    (((g * x * (h.map c)ᵀ).map c)ᵀ * J * (g * y * (h.map c)ᵀ) * K).trace = ((x.map c)ᵀ * J * y * K).trace := by
  have hhh : (h.map c).map c = h := by
    ext i j
    simp [hc]
  have e1 : (g * x * (h.map c)ᵀ).map c = g.map c * x.map c * hᵀ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hhh]
  have hg2 : ∀ M : Matrix (Fin n) (Fin m) R, (g.map c)ᵀ * (J * (g * M)) = J * M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg]
  have hh2 : (h.map c)ᵀ * (K * h) = K := by
    rw [← Matrix.mul_assoc, hh]
  rw [e1]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, hg2]
  conv_lhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc, hh2]

theorem idempotent_det_conj_identity (e : R) (h1 : e * e = e) (h2 : e * c e = 0) (g : Matrix (Fin n) (Fin n) R)
    (hs : ∀ i j, (e + c e) * (g - 1) i j = (g - 1) i j) (hd : c g.det * g.det = 1) :
    e * g.det + (1 - e) = g.det * c (e * g.det + (1 - e)) := by
  have h3 : c e * c e = c e := by rw [← map_mul, h1]
  have hf : (1 - (e + c e)) * (1 - (e + c e)) = 1 - (e + c e) := by
    linear_combination h1 + 2 * h2 + h3
  have hp : ∀ k : ℕ, (1 - (e + c e)) ^ (k + 1) = 1 - (e + c e) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, hf]
  have key : (1 - (e + c e)) * g.det = 1 - (e + c e) := by
    have hM : (1 - (e + c e)) • g = (1 - (e + c e)) • (1 : Matrix (Fin n) (Fin n) R) := by
      ext i j
      have := hs i j
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply] at this ⊢
      linear_combination (-1 : R) * this
    have hd' := congrArg Matrix.det hM
    rw [Matrix.det_smul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hd'
    cases n with
    | zero => rw [Matrix.det_isEmpty, mul_one]
    | succ k => rw [hp k] at hd'; exact hd'
  simp only [map_add, map_mul, map_sub, map_one]
  linear_combination -key - c e * hd

end Generic

variable {D : D7}

theorem cA_cA (a : AE D) : cA D (cA D a) = a := by
  have hs : ∀ x : D.host.E, D.sp.cm.sig (D.sp.cm.sig x) = x := by
    intro x
    unfold Formalism.BasicNotions.CMData.sig
    exact star_star x
  unfold cA sigR
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.map_tmul, hs]
  | add x y hx hy =>
    simp only [map_add] at *
    rw [hx, hy]

theorem mt_rel (V : HSp D) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D) := by
  have hg := g.2
  unfold HR at hg
  simp only [UG.UJ, JR] at hg
  exact hg

theorem hHom_actHom (V W : HSp D) (g : GA D V) (h : GA D W) (x y : WA V W) :
    hHom V W (actHom V W g h x) (actHom V W g h y) = hHom V W x y := by
  unfold hHom actHom
  have hc : ∀ a, cA D (cA D a) = a := cA_cA
  split_ifs with hr
  · have e1 := sum_eq_trace (cA D) ((HSpace.gram V).map (incA D)) ((HSpace.gram W).map (incA D))
      (cM (mt V g) * x * (mt W h)ᵀ) (cM (mt V g) * y * (mt W h)ᵀ)
    have e2 := sum_eq_trace (cA D) ((HSpace.gram V).map (incA D)) ((HSpace.gram W).map (incA D)) x y
    simp only [Matrix.map_apply] at e1 e2
    rw [e1, e2]
    exact inv_hom (cA D) hc _ _ _ _ (mt_rel V g) (mt_rel W h) x y
  · have e1 := sum_eq_trace (cA D) ((HSpace.gram V).map (incA D))ᵀ ((HSpace.gram W).map (incA D))ᵀ
      (mt V g * x * (cM (mt W h))ᵀ) (mt V g * y * (cM (mt W h))ᵀ)
    have e2 := sum_eq_trace (cA D) ((HSpace.gram V).map (incA D))ᵀ ((HSpace.gram W).map (incA D))ᵀ x y
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.transpose_transpose] at e1 e2
    rw [e1, e2]
    exact inv_hom' (cA D) hc _ _ _ _ (mt_rel V g) (mt_rel W h) x y

theorem sympl_actHom (V W : HSp D) (g : GA D V) (h : GA D W) (x y : WA V W) :
    sympl V W (actHom V W g h x) (actHom V W g h y) = sympl V W x y := by
  unfold sympl
  rw [hHom_actHom]

theorem hHom_transpose (V W : HSp D) (hne : V.rank ≠ W.rank) (x y : WA V W) :
    hHom W V x.transpose y.transpose = hHom V W x y := by
  unfold hHom
  simp only [Matrix.transpose_apply]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · rw [if_neg (show ¬ W.rank ≤ V.rank by omega), if_pos (show V.rank ≤ W.rank by omega)]
    have e1 := sum_eq_trace (cA D) ((HSpace.gram W).map (incA D))ᵀ ((HSpace.gram V).map (incA D))ᵀ xᵀ yᵀ
    have e2 := sum_eq_trace (cA D) ((HSpace.gram V).map (incA D)) ((HSpace.gram W).map (incA D)) x y
    simp only [Matrix.transpose_apply, Matrix.map_apply] at e1 e2
    rw [e1, e2, ← Matrix.trace_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map, Matrix.mul_assoc]
    conv_rhs => rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  · rw [if_pos (show W.rank ≤ V.rank by omega), if_neg (show ¬ V.rank ≤ W.rank by omega)]
    have e1 := sum_eq_trace (cA D) ((HSpace.gram W).map (incA D)) ((HSpace.gram V).map (incA D)) xᵀ yᵀ
    have e2 := sum_eq_trace (cA D) ((HSpace.gram V).map (incA D))ᵀ ((HSpace.gram W).map (incA D))ᵀ x y
    simp only [Matrix.transpose_apply, Matrix.map_apply] at e1 e2
    rw [e1, e2, ← Matrix.trace_transpose]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map, Matrix.mul_assoc]
    conv_rhs => rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]

theorem actHom_swap (V W : HSp D) (hne : V.rank ≠ W.rank) (g : GA D V) (h : GA D W) (x : WA V W) :
    actHom W V h g x.transpose = (actHom V W g h x).transpose := by
  unfold actHom
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · rw [if_neg (show ¬ W.rank ≤ V.rank by omega), if_pos (show V.rank ≤ W.rank by omega)]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  · rw [if_pos (show W.rank ≤ V.rank by omega), if_neg (show ¬ V.rank ≤ W.rank by omega)]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem splitFac_swap (V W : HSp D) (hne : V.rank ≠ W.rank) (c c' : (AE D)ˣ →* Circle) (x y : (AE D)ˣ) :
    splitFac W V c' c y x = splitFac V W c c' x y := by
  unfold splitFac
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · rw [if_neg (show ¬ W.rank ≤ V.rank by omega), if_pos (show V.rank ≤ W.rank by omega), mul_comm]
  · rw [if_pos (show W.rank ≤ V.rank by omega), if_neg (show ¬ V.rank ≤ W.rank by omega), mul_comm]

theorem gram_det_ne (V : HSp D) : V.gram.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  have hrow : ∀ i, ∑ j, V.gram i j * v j = 0 := fun i => by
    have := congrFun hJv i
    simpa [Matrix.mulVec, dotProduct] using this
  have hb : V.hT.flip (∑ j, v j • V.frame j) = 0 := by
    refine V.frame.ext fun i => ?_
    rw [LinearMap.flip_apply, LinearMap.zero_apply, map_sum, ← hrow i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
    exact mul_comm _ _
  have hy : ∀ x, V.hT x (∑ j, v j • V.frame j) = 0 := fun x => by
    have := LinearMap.congr_fun hb x
    rwa [LinearMap.flip_apply, LinearMap.zero_apply] at this
  have h0 := V.nondeg.2 _ hy
  funext i
  exact Fintype.linearIndependent_iff.mp V.frame.linearIndependent v h0 i

theorem det_conj_mul (V : HSp D) (g : GA D V) : cA D (mt V g).det * (mt V g).det = 1 := by
  have h := congrArg Matrix.det (mt_rel V g)
  have hd1 : ((mt V g).map (cA D)).det = cA D (mt V g).det := (RingHom.map_det (cA D) (mt V g)).symm
  have hd2 : (V.gram.map (incA D)).det = incA D V.gram.det := (RingHom.map_det (incA D) V.gram).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hd1, hd2] at h
  have hu : IsUnit (incA D V.gram.det) := (IsUnit.mk0 _ (gram_det_ne V)).map (incA D)
  apply hu.mul_left_cancel
  rw [mul_one]
  calc incA D V.gram.det * (cA D (mt V g).det * (mt V g).det)
      = cA D (mt V g).det * incA D V.gram.det * (mt V g).det := by ring
    _ = incA D V.gram.det := h

theorem isDetAt_root {e : AE D} (he : IsSplitIdem D e) (V : HSp D) (g : GA D V) (hs : SuppAt e V g) (x : (AE D)ˣ)
    (hx : IsDetAt e V g x) : IsDetRoot V g x := by
  unfold IsDetRoot
  unfold IsDetAt at hx
  unfold SuppAt at hs
  unfold IsSplitIdem at he
  rw [hx]
  exact idempotent_det_conj_identity (cA D) e he.1 he.2.1 (mt V g) hs (det_conj_mul V g)

variable {X : ThetaX D} {T : ThetaTied D X}

theorem PhiYupTied.kernel {Wl : WeilTied D X T} (h : PhiYupTied Wl) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m)
    (g : GA D (D.sp.Y (j + 1))) (k : GA D (D.sp.Y j)) :
    Wl.evS _ _ (Wl.om _ _ (X.carY μ (j + 1) j) (X.carY μ (j + 1) (j + 1)) (k, g) (X.PhiYup μ j)) 0 =
      Wl.evS _ _ (Wl.om _ _ (X.carY μ (j + 1) (j + 1)) (X.carY μ (j + 1) j) (g, k) (X.PhiY μ j)) 0 := by
  have s := Wl.om_swap _ _ (X.carY μ (j + 1) (j + 1)) (X.carY μ (j + 1) j) (rank_Y_ne X j hj)
    (row_lift_ok T μ (j + 1) (by omega) hj (j + 1) hj) (row_lift_ok T μ (j + 1) (by omega) hj j hj.le)
    g k (X.PhiY μ j) (X.PhiYup μ j) (h μ j hj) 0
  rwa [Matrix.transpose_zero] at s

end Formalism.L2.Theta

end
