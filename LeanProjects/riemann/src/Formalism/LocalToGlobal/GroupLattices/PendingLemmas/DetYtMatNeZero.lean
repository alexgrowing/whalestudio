import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

noncomputable section

namespace Formalism.L2.G.Pend

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem rankJ (j : ℕ) : (X.Fl.Pj j).m + 1 = NN X.G.P.m X.Fl.t j := by
  cases j with
  | zero => simp [Fills.Pj, NN]
  | succ j =>
    show X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1 = NN X.G.P.m X.Fl.t (j + 1)
    unfold NN
    ring

theorem NN_le (j : ℕ) : NN X.G.P.m X.t j ≤ NN X.G.P.m X.t (j + 1) := by
  unfold NN
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ j)) _

abbrev YI (j : ℕ) : Type :=
  Σ v : X.Pl, Fin (X.G.P.n' v) × (Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j))

def idxJ : (j : ℕ) →
    (Σ v : Fin (X.Fl.Pj j).nV, Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) → YI X j
  | 0, x => ⟨x.1, (x.2.1, (Fin.cast (rankJ X 0) x.2.2.1, Fin.cast (rankJ X 0) x.2.2.2))⟩
  | j + 1, x => ⟨x.1, (x.2.1, (Fin.cast (rankJ X (j + 1)) x.2.2.1, Fin.cast (rankJ X (j + 1)) x.2.2.2))⟩

def idxS (j : ℕ) (x : YI X (j + 1)) :
    (Σ v : Fin (X.Fl.Pj (j + 1)).nV,
      Fin ((X.Fl.Pj (j + 1)).n' v) × (Fin ((X.Fl.Pj (j + 1)).m + 1) × Fin ((X.Fl.Pj (j + 1)).m + 1))) :=
  ⟨x.1, (x.2.1, (Fin.cast (rankJ X (j + 1)).symm x.2.2.1, Fin.cast (rankJ X (j + 1)).symm x.2.2.2))⟩

variable (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]

abbrev DA (j : ℕ) : Type := MvPolynomial (X.ZA j) (XspC (X.Pj (j + 1)) Kc)

def dMat (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    Matrix (Fin (NN X.G.P.m X.t j)) (Fin (NN X.G.P.m X.t (j + 1))) (DA X Kc j) :=
  fun a b => MvPolynomial.X (⟨v, (s, a, b)⟩ : X.ZA j)

def yMat (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) (DA X Kc j) :=
  fun b t => MvPolynomial.C (MvPolynomial.X (idxS X j ⟨v, (s, (b, t))⟩))

def dyMat (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    Matrix (Fin (NN X.G.P.m X.t j)) (Fin (NN X.G.P.m X.t j)) (DA X Kc j) :=
  (dMat X Kc j v s * yMat X Kc j v s).submatrix id (Fin.castLE (NN_le X j))

def shiftI (j : ℕ) (t : Fin (NN X.G.P.m X.t j)) : Fin (NN X.G.P.m X.t (j + 1)) :=
  ⟨NN X.G.P.m X.t (j + 1) - NN X.G.P.m X.t j + t.val, by have := NN_le X j; have := t.isLt; omega⟩

def YtMat (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    Matrix (Fin (NN X.G.P.m X.t j)) (Fin (NN X.G.P.m X.t j)) (DA X Kc j) :=
  (yMat X Kc j v s).adjugate.submatrix (shiftI X j) id * (dMat X Kc j v s).transpose

def ySub (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    Matrix (Fin (NN X.G.P.m X.t j)) (Fin (NN X.G.P.m X.t j)) (DA X Kc j) :=
  if IsOddPos s then (YtMat X Kc j v s).adjugate else dyMat X Kc j v s

def subD (j : ℕ) : (X.Pj j).Xsp →ₐ[X.G.Kf] DA X Kc j :=
  MvPolynomial.aeval fun x => ySub X Kc j (idxJ X j x).1 (idxJ X j x).2.1 (idxJ X j x).2.2.1 (idxJ X j x).2.2.2

def cMu (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : ℤ := X.nuv v (j + 1) s 1

def szMu (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : ℤ := ∑ i ∈ Icc 1 (NN X.G.P.m X.t (j + 1)), X.nuv v (j + 1) s i

def exY (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : ℤ := cMu X j v s - szMu X j v s

def exT (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : ℤ :=
  cMu X j v s - (NN X.G.P.m X.t j : ℤ) * cMu X j v s + szMu X j v s

def numD (j : ℕ) : DA X Kc j :=
  ∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v),
    if IsOddPos s then (yMat X Kc j v s).det ^ (exY X j v s).toNat * (YtMat X Kc j v s).det ^ (exT X j v s).toNat
    else (dyMat X Kc j v s).det ^ (X.nuv v (j + 1) s (NN X.G.P.m X.t j)).toNat

def denD (j : ℕ) : DA X Kc j :=
  ∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v),
    if IsOddPos s then (yMat X Kc j v s).det ^ (-exY X j v s).toNat * (YtMat X Kc j v s).det ^ (-exT X j v s).toNat
    else 1

open Classical in

def divD (j : ℕ) : DA X Kc j →ₗ[X.G.Kf] DA X Kc j :=
  if h : Function.Injective (LinearMap.mulLeft X.G.Kf (denD X Kc j)) then
    Classical.choose (LinearMap.exists_leftInverse_of_injective (LinearMap.mulLeft X.G.Kf (denD X Kc j))
      (LinearMap.ker_eq_bot.2 h))
  else 0

theorem divD_mul (j : ℕ) (h : Function.Injective (LinearMap.mulLeft X.G.Kf (denD X Kc j))) (P : DA X Kc j) :
    divD X Kc j (denD X Kc j * P) = P := by
  unfold divD
  rw [dif_pos h]
  exact LinearMap.congr_fun (Classical.choose_spec (LinearMap.exists_leftInverse_of_injective
    (LinearMap.mulLeft X.G.Kf (denD X Kc j)) (LinearMap.ker_eq_bot.2 h))) P

def polDel (j : ℕ) : (X.Pj j).Xsp →ₗ[X.G.Kf] DA X Kc j :=
  (divD X Kc j).comp ((LinearMap.mulRight X.G.Kf (numD X Kc j)).comp (subD X Kc j).toLinearMap)

def GoodDeg (j : ℕ) (n : X.ZA j →₀ ℕ) : Prop :=
  ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)),
    ((∑ a, ∑ b, n ⟨v, (s, a, b)⟩ : ℕ) : ℤ) = ∑ i ∈ Icc 1 (NN X.G.P.m X.t (j + 1)), X.nuv v (j + 1) s i

open Classical in

def derAt (j : ℕ) (n : X.ZA j →₀ ℕ) (f : MvPowerSeries (X.ZA j) Kc) : Kc :=
  if GoodDeg X j n then (∏ x ∈ n.support, ((n x).factorial : Kc)) * MvPowerSeries.coeff n f else 0

theorem derAt_add (j : ℕ) (n : X.ZA j →₀ ℕ) (f f' : MvPowerSeries (X.ZA j) Kc) :
    derAt X Kc j n (f + f') = derAt X Kc j n f + derAt X Kc j n f' := by
  unfold derAt
  split_ifs <;> simp [mul_add]

theorem derAt_smul (j : ℕ) (n : X.ZA j →₀ ℕ) (c : X.G.Kf) (f : MvPowerSeries (X.ZA j) Kc) :
    derAt X Kc j n (c • f) = c • derAt X Kc j n f := by
  unfold derAt
  split_ifs
  · rw [show MvPowerSeries.coeff n (c • f) = c • MvPowerSeries.coeff n f from rfl, mul_smul_comm]
  · rw [smul_zero]

def pairD (j : ℕ) (P : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc) : XspC (X.Pj (j + 1)) Kc :=
  ∑ n ∈ P.support, derAt X Kc j n f • MvPolynomial.coeff n P

theorem pairD_eq (j : ℕ) (P : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc) (S : Finset (X.ZA j →₀ ℕ))
    (hS : P.support ⊆ S) : pairD X Kc j P f = ∑ n ∈ S, derAt X Kc j n f • MvPolynomial.coeff n P := by
  unfold pairD
  refine Finset.sum_subset hS fun n _ hn => ?_
  simp only [MvPolynomial.mem_support_iff, not_not] at hn
  rw [hn, smul_zero]

theorem pairD_add_left (j : ℕ) (P P' : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc) :
    pairD X Kc j (P + P') f = pairD X Kc j P f + pairD X Kc j P' f := by
  rw [pairD_eq X Kc j (P + P') f (P.support ∪ P'.support) MvPolynomial.support_add,
    pairD_eq X Kc j P f (P.support ∪ P'.support) (fun x hx => Finset.mem_union_left _ hx),
    pairD_eq X Kc j P' f (P.support ∪ P'.support) (fun x hx => Finset.mem_union_right _ hx),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPolynomial.coeff_add, smul_add]

theorem pairD_smul_left (j : ℕ) (c : X.G.Kf) (P : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc) :
    pairD X Kc j (c • P) f = c • pairD X Kc j P f := by
  rw [pairD_eq X Kc j (c • P) f P.support MvPolynomial.support_smul]
  unfold pairD
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPolynomial.coeff_smul, smul_comm]

theorem pairD_add_right (j : ℕ) (P : DA X Kc j) (f f' : MvPowerSeries (X.ZA j) Kc) :
    pairD X Kc j P (f + f') = pairD X Kc j P f + pairD X Kc j P f' := by
  unfold pairD
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [derAt_add, add_smul]

theorem pairD_smul_right (j : ℕ) (c : X.G.Kf) (P : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc) :
    pairD X Kc j P (c • f) = c • pairD X Kc j P f := by
  unfold pairD
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [derAt_smul, smul_assoc]

def delF (j : ℕ) : (X.Pj j).Xsp →ₗ[X.G.Kf] MvPowerSeries (X.ZA j) Kc →ₗ[X.G.Kf] XspC (X.Pj (j + 1)) Kc :=
  LinearMap.mk₂ X.G.Kf (fun G f => pairD X Kc j (polDel X Kc j G) f)
    (fun G G' f => by rw [map_add, pairD_add_left])
    (fun c G f => by rw [map_smul, pairD_smul_left])
    (fun G f f' => pairD_add_right X Kc j _ f f')
    (fun c G f => pairD_smul_right X Kc j c _ f)

theorem delF_apply (j : ℕ) (G : (X.Pj j).Xsp) (f : MvPowerSeries (X.ZA j) Kc) :
    delF X Kc j G f = pairD X Kc j (polDel X Kc j G) f := rfl

theorem del_deg (j : ℕ) (G : (X.Pj j).Xsp) (f : MvPowerSeries (X.ZA j) Kc)
    (h : ∀ n : X.ZA j →₀ ℕ, (∀ (v : X.Pl) (s : Fin (X.G.P.n' v)),
        ((∑ a, ∑ b, n ⟨v, (s, a, b)⟩ : ℕ) : ℤ) = ∑ i ∈ Icc 1 (NN X.G.P.m X.t (j + 1)), X.nuv v (j + 1) s i) →
      MvPowerSeries.coeff n f = 0) : delF X Kc j G f = 0 := by
  rw [delF_apply]
  unfold pairD
  refine Finset.sum_eq_zero fun n _ => ?_
  unfold derAt
  split_ifs with hg
  · rw [h n hg, mul_zero, zero_smul]
  · rw [zero_smul]

section NonZero

open Classical in

def evPt (j : ℕ) : DA X Kc j →+* Kc :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.eval fun i : (Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v) ×
      (Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj (j + 1)).m + 1))) => if i.2.2.1 = i.2.2.2 then (1 : Kc) else 0)
    (fun z : X.ZA j => if z.2.2.2 = shiftI X j z.2.2.1 then (1 : Kc) else 0)

theorem evPt_yMat (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : (evPt X Kc j).mapMatrix (yMat X Kc j v s) = 1 := by
  ext b t
  simp [RingHom.mapMatrix_apply, Matrix.map_apply, yMat, evPt, idxS, Matrix.one_apply]

theorem shiftI_injective (j : ℕ) : Function.Injective (shiftI X j) := by
  intro a b hab
  simp only [shiftI, Fin.mk.injEq] at hab
  exact Fin.ext (by omega)

theorem evPt_YtMat (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : (evPt X Kc j).mapMatrix (YtMat X Kc j v s) = 1 := by
  have hadj : ∀ i b, evPt X Kc j ((yMat X Kc j v s).adjugate i b) = (1 : Matrix _ _ Kc) i b := by
    intro i b
    have := congrArg (fun M => M i b) (RingHom.map_adjugate (evPt X Kc j) (yMat X Kc j v s))
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at this
    rw [this, ← RingHom.mapMatrix_apply, evPt_yMat, Matrix.adjugate_one]
  ext t a
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, YtMat, Matrix.mul_apply, Matrix.submatrix_apply,
    Matrix.transpose_apply, id, map_sum, map_mul, hadj, dMat, Matrix.one_apply]
  simp [evPt, (shiftI_injective X j).eq_iff, eq_comm]

theorem det_yMat_ne_zero (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : (yMat X Kc j v s).det ≠ 0 := by
  intro h0
  have := RingHom.map_det (evPt X Kc j) (yMat X Kc j v s)
  rw [h0, map_zero, evPt_yMat, Matrix.det_one] at this
  exact zero_ne_one this

theorem det_YtMat_ne_zero (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : (YtMat X Kc j v s).det ≠ 0 := by
  intro h0
  have := RingHom.map_det (evPt X Kc j) (YtMat X Kc j v s)
  rw [h0, map_zero, evPt_YtMat, Matrix.det_one] at this
  exact zero_ne_one this

theorem denD_ne_zero (j : ℕ) : denD X Kc j ≠ 0 := by
  unfold denD
  refine Finset.prod_ne_zero_iff.2 fun v _ => Finset.prod_ne_zero_iff.2 fun s _ => ?_
  split_ifs
  · exact mul_ne_zero (pow_ne_zero _ (det_yMat_ne_zero X Kc j v s)) (pow_ne_zero _ (det_YtMat_ne_zero X Kc j v s))
  · exact one_ne_zero

theorem divD_den_mul (j : ℕ) (P : DA X Kc j) : divD X Kc j (denD X Kc j * P) = P := divD_mul X Kc j (fun a b hab => mul_left_cancel₀ (denD_ne_zero X Kc j) (by simpa using hab)) P

theorem polDel_eq (j : ℕ) (G : (X.Pj j).Xsp) (R : DA X Kc j)
    (h : subD X Kc j G * numD X Kc j = denD X Kc j * R) : polDel X Kc j G = R := by
  simp only [polDel, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]
  rw [h, divD_den_mul]

end NonZero

theorem subD_X (j : ℕ) (x : Σ v : Fin (X.Fl.Pj j).nV,
    Fin ((X.Fl.Pj j).n' v) × (Fin ((X.Fl.Pj j).m + 1) × Fin ((X.Fl.Pj j).m + 1))) :
    subD X Kc j (MvPolynomial.X x) =
      ySub X Kc j (idxJ X j x).1 (idxJ X j x).2.1 (idxJ X j x).2.2.1 (idxJ X j x).2.2.2 := by
  unfold subD
  rw [MvPolynomial.aeval_X]

theorem ySub_odd (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (h : IsOddPos s) :
    ySub X Kc j v s = (YtMat X Kc j v s).adjugate := by
  simp only [ySub, if_pos h]

theorem delF_eq (j : ℕ) (G : (X.Pj j).Xsp) (R : DA X Kc j)
    (h : subD X Kc j G * numD X Kc j = denD X Kc j * R) (f : MvPowerSeries (X.ZA j) Kc) :
    delF X Kc j G f = pairD X Kc j R f := by
  rw [delF_apply, polDel_eq X Kc j G R h]

end Formalism.L2.G.Pend
