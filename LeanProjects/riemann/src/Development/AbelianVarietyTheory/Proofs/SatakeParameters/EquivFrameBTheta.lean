import Mathlib
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SuccMulSuccSubOneDivSucc
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Finset

noncomputable section

namespace GlobalTheory.FrameB

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

def frF (W : ∀ v : X.Pl, Fin (X.G.P.n' v) → Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc)
    (y : Σ v : Fin (X.Fl.Pj (j + 1)).nV, Fin ((X.Fl.Pj (j + 1)).n' v) × (Fin ((X.Fl.Pj (j + 1)).m + 1) × Fin ((X.Fl.Pj (j + 1)).m + 1))) :
    XspC (X.Pj (j + 1)) Kc :=
  ∑ b : Fin (NN X.G.P.m X.t (j + 1)), MvPolynomial.C (W y.1 y.2.1 (Fin.cast (rankJ X (j + 1)) y.2.2.1) b) *
    MvPolynomial.X ⟨y.1, (y.2.1, (Fin.cast (rankJ X (j + 1)).symm b, y.2.2.2))⟩

def tau0 (W : ∀ v : X.Pl, Fin (X.G.P.n' v) → Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc) :
    XspC (X.Pj (j + 1)) Kc →ₐ[Kc] XspC (X.Pj (j + 1)) Kc :=
  MvPolynomial.aeval (frF X Kc j W)

def mapT (W : ∀ v : X.Pl, Fin (X.G.P.n' v) → Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc) :
    DA X Kc j →+* DA X Kc j :=
  MvPolynomial.map (tau0 X Kc j W : XspC (X.Pj (j + 1)) Kc →+* XspC (X.Pj (j + 1)) Kc)

variable (W : ∀ v : X.Pl, Fin (X.G.P.n' v) → Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc)

theorem mapT_cD (a : Kc) : mapT X Kc j W (cD X Kc j a) = cD X Kc j a := by
  unfold mapT cD
  rw [RingHom.comp_apply, MvPolynomial.map_C]
  simp [tau0]

theorem mapT_dMat (v : X.Pl) (s : Fin (X.G.P.n' v)) : (dMat X Kc j v s).map (mapT X Kc j W) = dMat X Kc j v s := by
  ext a b
  simp [dMat, mapT]

theorem mapT_yMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (yMat X Kc j v s).map (mapT X Kc j W) = (W v s).map (cD X Kc j) * yMat X Kc j v s := by
  ext b t
  simp only [Matrix.map_apply, Matrix.mul_apply, yMat, mapT, MvPolynomial.map_C]
  rw [show (tau0 X Kc j W : XspC (X.Pj (j + 1)) Kc →+* XspC (X.Pj (j + 1)) Kc) (MvPolynomial.X (idxS X j ⟨v, (s, (b, t))⟩)) =
    frF X Kc j W (idxS X j ⟨v, (s, (b, t))⟩) from MvPolynomial.aeval_X _ _]
  simp only [frF, idxS, map_sum, map_mul, cD, RingHom.comp_apply, Fin.cast_cast, Fin.cast_eq_self]
  rfl

end GlobalTheory.FrameB

namespace GlobalTheory.FrameB

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

def thU (U : ∀ v : X.Pl, Fin (X.G.P.n' v) → Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc) :
    DA X Kc j →ₐ[XspC (X.Pj (j + 1)) Kc] DA X Kc j :=
  MvPolynomial.aeval fun z => (dMat X Kc j z.1 z.2.1 * (U z.1 z.2.1).map (cD X Kc j)) z.2.2.1 z.2.2.2

variable (U W : ∀ v : X.Pl, Fin (X.G.P.n' v) → Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc)

theorem thU_cD (a : Kc) : thU X Kc j U (cD X Kc j a) = cD X Kc j a := by
  unfold thU cD
  rw [RingHom.comp_apply, MvPolynomial.aeval_C]
  rfl

theorem thU_dMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (dMat X Kc j v s).map (thU X Kc j U) = dMat X Kc j v s * (U v s).map (cD X Kc j) := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.map_apply]
  show thU X Kc j U (MvPolynomial.X _) = _
  unfold thU
  rw [MvPolynomial.aeval_X]

theorem thU_yMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (yMat X Kc j v s).map (thU X Kc j U) = yMat X Kc j v s := by
  refine Matrix.ext fun b t => ?_
  rw [Matrix.map_apply]
  show thU X Kc j U (MvPolynomial.C _) = _
  unfold thU
  rw [MvPolynomial.aeval_C]
  rfl

theorem thU_dyMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (dyMat X Kc j v s).map (thU X Kc j U) =
      (dMat X Kc j v s * (U v s).map (cD X Kc j) * yMat X Kc j v s).submatrix id (Fin.castLE (NN_le X j)) := by
  unfold dyMat
  rw [← Matrix.submatrix_map, Matrix.map_mul, thU_dMat, thU_yMat]

theorem mapT_dyMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (dyMat X Kc j v s).map (mapT X Kc j W) =
      (dMat X Kc j v s * ((W v s).map (cD X Kc j) * yMat X Kc j v s)).submatrix id (Fin.castLE (NN_le X j)) := by
  unfold dyMat
  rw [← Matrix.submatrix_map, Matrix.map_mul, mapT_dMat, mapT_yMat]

theorem even_dyMat (v : X.Pl) (s : Fin (X.G.P.n' v)) (h : U v s = W v s) :
    (dyMat X Kc j v s).map (thU X Kc j U) = (dyMat X Kc j v s).map (mapT X Kc j W) := by
  rw [thU_dyMat, mapT_dyMat, h, Matrix.mul_assoc]

theorem sub_mul_left {m n o q : Type} [Fintype n] {R : Type} [CommRing R] (A : Matrix m n R) (B : Matrix n o R)
    (f : q → m) : (A * B).submatrix f id = A.submatrix f id * B := by
  ext i k
  simp [Matrix.mul_apply]

theorem odd_YtMat (v : X.Pl) (s : Fin (X.G.P.n' v)) (κ : Kc) (h : (U v s).transpose = κ • (W v s).adjugate) :
    (YtMat X Kc j v s).map (thU X Kc j U) = cD X Kc j κ • (YtMat X Kc j v s).map (mapT X Kc j W) := by
  have hy : ((yMat X Kc j v s).adjugate.submatrix (shiftI X j) id).map (thU X Kc j U) =
      (yMat X Kc j v s).adjugate.submatrix (shiftI X j) id := by
    rw [← Matrix.submatrix_map]
    have := RingHom.map_adjugate (thU X Kc j U : DA X Kc j →+* DA X Kc j) (yMat X Kc j v s)
    simp only [RingHom.mapMatrix_apply] at this
    rw [show (yMat X Kc j v s).map ((thU X Kc j U : DA X Kc j →+* DA X Kc j)) = yMat X Kc j v s from thU_yMat X Kc j U v s] at this
    exact congrArg (fun M => M.submatrix (shiftI X j) id) this
  have hy' : ((yMat X Kc j v s).adjugate.submatrix (shiftI X j) id).map (mapT X Kc j W) =
      ((yMat X Kc j v s).adjugate * ((W v s).map (cD X Kc j)).adjugate).submatrix (shiftI X j) id := by
    rw [← Matrix.submatrix_map]
    have := RingHom.map_adjugate (mapT X Kc j W) (yMat X Kc j v s)
    simp only [RingHom.mapMatrix_apply] at this
    rw [mapT_yMat, Matrix.adjugate_mul_distrib] at this
    rw [← this]
  unfold YtMat
  rw [Matrix.map_mul, Matrix.map_mul, hy, hy', Matrix.transpose_map, Matrix.transpose_map, thU_dMat, mapT_dMat,
    Matrix.transpose_mul, ← Matrix.transpose_map, h, sub_mul_left]
  have hm : (κ • (W v s).adjugate).map (cD X Kc j) = cD X Kc j κ • ((W v s).map (cD X Kc j)).adjugate := by
    rw [show ((W v s).map (cD X Kc j)).adjugate = (W v s).adjugate.map (cD X Kc j) from
      (RingHom.map_adjugate (cD X Kc j) (W v s)).symm]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [hm, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

end GlobalTheory.FrameB

namespace GlobalTheory.FrameB

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (j : ℕ)
  (U W : ∀ v : X.Pl, Fin (X.G.P.n' v) → Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc)
  (κ : ∀ v : X.Pl, Fin (X.G.P.n' v) → Kc)

def FrRel : Prop :=
  ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)),
    (¬ IsOddPos s → U v s = W v s) ∧ (IsOddPos s → (U v s).transpose = κ v s • (W v s).adjugate)

def sg (v : X.Pl) (s : Fin (X.G.P.n' v)) : Kc := if IsOddPos s then κ v s ^ (NN X.G.P.m X.t j - 1) else 1

variable {X Kc j U W κ}

theorem ySub_rel (h : FrRel X Kc j U W κ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (ySub X Kc j v s).map (thU X Kc j U) = cD X Kc j (sg X Kc j κ v s) • (ySub X Kc j v s).map (mapT X Kc j W) := by
  by_cases ho : IsOddPos s
  · rw [ySub_odd X Kc j v s ho]
    have h1 := RingHom.map_adjugate (thU X Kc j U : DA X Kc j →+* DA X Kc j) (YtMat X Kc j v s)
    have h2 := RingHom.map_adjugate (mapT X Kc j W) (YtMat X Kc j v s)
    simp only [RingHom.mapMatrix_apply] at h1 h2
    have h3 : (YtMat X Kc j v s).map ((thU X Kc j U : DA X Kc j →+* DA X Kc j)) =
        cD X Kc j (κ v s) • (YtMat X Kc j v s).map (mapT X Kc j W) := odd_YtMat X Kc j U W v s (κ v s) ((h v s).2 ho)
    rw [show (YtMat X Kc j v s).adjugate.map (thU X Kc j U) =
      (YtMat X Kc j v s).adjugate.map ((thU X Kc j U : DA X Kc j →+* DA X Kc j)) from rfl, h1, h3, h2,
      Matrix.adjugate_smul, Fintype.card_fin, sg, if_pos ho, map_pow]
  · have h0 : ySub X Kc j v s = dyMat X Kc j v s := by unfold ySub; rw [if_neg ho]
    rw [h0, even_dyMat X Kc j U W v s ((h v s).1 ho), sg, if_neg ho, map_one, one_smul]

def sS (X : Sys p) (Kc : Type) [Field Kc] (j : ℕ) (κ : ∀ v : X.Pl, Fin (X.G.P.n' v) → Kc) : Kc :=
  ∏ b : (Σ v : X.Pl, Fin (X.G.P.n' v)),
    if IsOddPos b.2 then (κ b.1 b.2 ^ (NN X.G.P.m X.t j - 1)) ^
      ((NN X.G.P.m X.t j : ℤ) * cMu X j b.1 b.2 - szMu X j b.1 b.2).toNat else 1

set_option maxHeartbeats 1000000 in
theorem thU_subD (h : FrRel X Kc j U W κ) (G : (X.Pj j).Xsp) (hO : OddDeg X j G) :
    thU X Kc j U (subD X Kc j G) = cD X Kc j (sS X Kc j κ) * mapT X Kc j W (subD X Kc j G) := by
  have hC : ∀ a : X.G.Kf, thU X Kc j U (subD X Kc j (MvPolynomial.C a)) = mapT X Kc j W (subD X Kc j (MvPolynomial.C a)) := by
    intro a
    rw [subD_C, thU_cD, mapT_cD]
  have hX : ∀ x, thU X Kc j U (subD X Kc j (MvPolynomial.X x)) =
      cD X Kc j (sg X Kc j κ (blkJ X j x).1 (blkJ X j x).2) * mapT X Kc j W (subD X Kc j (MvPolynomial.X x)) := by
    intro x
    rw [subD_X]
    have := congrFun (congrFun (ySub_rel h (idxJ X j x).1 (idxJ X j x).2.1) (idxJ X j x).2.2.1) (idxJ X j x).2.2.2
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this
    exact this
  have key := ringHom_scale
    ((thU X Kc j U : DA X Kc j →+* DA X Kc j).comp (subD X Kc j : (X.Pj j).Xsp →+* DA X Kc j))
    ((mapT X Kc j W).comp (subD X Kc j : (X.Pj j).Xsp →+* DA X Kc j))
    (fun x => cD X Kc j (sg X Kc j κ (blkJ X j x).1 (blkJ X j x).2))
    (fun a => by simpa only [RingHom.comp_apply, RingHom.coe_coe] using hC a)
    (fun x => by simpa only [RingHom.comp_apply, RingHom.coe_coe] using hX x)
    (cD X Kc j (sS X Kc j κ)) G ?_
  · simpa only [RingHom.comp_apply, RingHom.coe_coe] using key
  · intro m hm
    simp only [← map_pow, ← map_prod]
    congr 1
    rw [← Finset.prod_fiberwise Finset.univ (blkJ X j)]
    unfold sS
    refine Finset.prod_congr rfl fun b _ => ?_
    have h2 : ∏ x ∈ Finset.univ.filter (fun x => blkJ X j x = b), sg X Kc j κ (blkJ X j x).1 (blkJ X j x).2 ^ m x =
        sg X Kc j κ b.1 b.2 ^ (∑ x ∈ Finset.univ.filter (fun x => blkJ X j x = b), m x) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.1 hx).2]
    rw [h2]
    unfold sg
    by_cases hb : IsOddPos b.2
    · rw [if_pos hb, if_pos hb, ← hO m hm b hb, Int.toNat_natCast]
    · rw [if_neg hb, if_neg hb, one_pow]

end GlobalTheory.FrameB

namespace GlobalTheory.FrameB

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {Kc : Type} [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] {j : ℕ}
  {U W : ∀ v : X.Pl, Fin (X.G.P.n' v) → Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc}
  {κ : ∀ v : X.Pl, Fin (X.G.P.n' v) → Kc}

theorem thU_det_y (v : X.Pl) (s : Fin (X.G.P.n' v)) : thU X Kc j U (yMat X Kc j v s).det = (yMat X Kc j v s).det := by
  rw [AlgHom.map_det]
  show ((yMat X Kc j v s).map (thU X Kc j U)).det = _
  rw [thU_yMat]

theorem mapT_det_y (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    mapT X Kc j W (yMat X Kc j v s).det = cD X Kc j (W v s).det * (yMat X Kc j v s).det := by
  rw [RingHom.map_det]
  show ((yMat X Kc j v s).map (mapT X Kc j W)).det = _
  rw [mapT_yMat, Matrix.det_mul, det_map_cD]

theorem thU_det_y' (hW : ∀ v s, (W v s).det ≠ 0) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    thU X Kc j U (yMat X Kc j v s).det = cD X Kc j (W v s).det⁻¹ * mapT X Kc j W (yMat X Kc j v s).det := by
  rw [thU_det_y, mapT_det_y, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (hW v s), map_one, one_mul]

theorem thU_det_dy (h : FrRel X Kc j U W κ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (ho : ¬ IsOddPos s) :
    thU X Kc j U (dyMat X Kc j v s).det = mapT X Kc j W (dyMat X Kc j v s).det := by
  rw [AlgHom.map_det, RingHom.map_det]
  show ((dyMat X Kc j v s).map (thU X Kc j U)).det = ((dyMat X Kc j v s).map (mapT X Kc j W)).det
  rw [even_dyMat X Kc j U W v s ((h v s).1 ho)]

theorem thU_det_Yt (h : FrRel X Kc j U W κ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (ho : IsOddPos s) :
    thU X Kc j U (YtMat X Kc j v s).det = cD X Kc j (κ v s ^ NN X.G.P.m X.t j) * mapT X Kc j W (YtMat X Kc j v s).det := by
  rw [AlgHom.map_det, RingHom.map_det]
  show ((YtMat X Kc j v s).map (thU X Kc j U)).det = _
  rw [odd_YtMat X Kc j U W v s (κ v s) ((h v s).2 ho), Matrix.det_smul, Fintype.card_fin, map_pow]
  rfl

variable (X Kc j W κ) in

def kN : Kc := ∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v),
  if IsOddPos s then ((W v s).det⁻¹) ^ (exY X j v s).toNat * (κ v s ^ NN X.G.P.m X.t j) ^ (exT X j v s).toNat else 1

variable (X Kc j W κ) in

def kD : Kc := ∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v),
  if IsOddPos s then ((W v s).det⁻¹) ^ (-exY X j v s).toNat * (κ v s ^ NN X.G.P.m X.t j) ^ (-exT X j v s).toNat else 1

theorem thU_numD (h : FrRel X Kc j U W κ) (hW : ∀ v s, (W v s).det ≠ 0) :
    thU X Kc j U (numD X Kc j) = cD X Kc j (kN X Kc j W κ) * mapT X Kc j W (numD X Kc j) := by
  unfold numD kN
  simp only [map_prod]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  by_cases ho : IsOddPos s
  · simp only [if_pos ho, map_mul, map_pow, thU_det_y' hW, thU_det_Yt h v s ho]
    ring
  · simp only [if_neg ho]
    rw [map_pow, thU_det_dy h v s ho, map_one, one_mul, map_pow]

theorem thU_denD (h : FrRel X Kc j U W κ) (hW : ∀ v s, (W v s).det ≠ 0) :
    thU X Kc j U (denD X Kc j) = cD X Kc j (kD X Kc j W κ) * mapT X Kc j W (denD X Kc j) := by
  unfold denD kD
  simp only [map_prod]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  by_cases ho : IsOddPos s
  · simp only [if_pos ho, map_mul, map_pow, thU_det_y' hW, thU_det_Yt h v s ho]
    ring
  · simp only [if_neg ho]
    rw [map_one, map_one, map_one, one_mul]

theorem kD_ne (hW : ∀ v s, (W v s).det ≠ 0) (hk : ∀ v s, κ v s ≠ 0) : kD X Kc j W κ ≠ 0 := by
  unfold kD
  refine Finset.prod_ne_zero_iff.2 fun v _ => Finset.prod_ne_zero_iff.2 fun s _ => ?_
  split_ifs
  · exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (hW v s))) (pow_ne_zero _ (pow_ne_zero _ (hk v s)))
  · exact one_ne_zero

theorem thU_comp (U' : ∀ v : X.Pl, Fin (X.G.P.n' v) → Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc)
    (hUU : ∀ v s, U' v s * U v s = 1) (P : DA X Kc j) : thU X Kc j U' (thU X Kc j U P) = P := by
  have hc : (thU X Kc j U').comp (thU X Kc j U) = AlgHom.id _ _ := by
    refine MvPolynomial.algHom_ext fun z => ?_
    obtain ⟨v, s, a, b⟩ := z
    have h1 : ((dMat X Kc j v s).map (thU X Kc j U)).map (thU X Kc j U') = dMat X Kc j v s := by
      rw [thU_dMat, Matrix.map_mul, thU_dMat]
      have h2 : ((U v s).map (cD X Kc j)).map (thU X Kc j U') = (U v s).map (cD X Kc j) :=
        Matrix.ext fun a b => by rw [Matrix.map_apply, Matrix.map_apply, thU_cD]
      rw [h2, Matrix.mul_assoc, ← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    exact congrFun (congrFun h1 a) b
  exact congrArg (fun φ => φ P) hc

theorem thU_injective (hU : ∀ v s, IsUnit (U v s).det) : Function.Injective (thU X Kc j U) := by
  intro P Q hPQ
  have := congrArg (thU X Kc j (fun v s => (U v s)⁻¹)) hPQ
  rwa [thU_comp _ (fun v s => Matrix.nonsing_inv_mul _ (hU v s)), thU_comp _ (fun v s => Matrix.nonsing_inv_mul _ (hU v s))] at this

theorem thU_polDel (h : FrRel X Kc j U W κ) (hW : ∀ v s, (W v s).det ≠ 0) (hk : ∀ v s, κ v s ≠ 0)
    (hU : ∀ v s, IsUnit (U v s).det) (G : (X.Pj j).Xsp) (hG : GoodG X Kc j G) (hO : OddDeg X j G) :
    thU X Kc j U (polDel X Kc j G) =
      cD X Kc j (sS X Kc j κ * kN X Kc j W κ * (kD X Kc j W κ)⁻¹) * mapT X Kc j W (polDel X Kc j G) := by
  obtain ⟨R, hR⟩ := hG
  rw [polDel_eq X Kc j G R hR]
  have h1 := congrArg (thU X Kc j U) hR
  have h2 := congrArg (mapT X Kc j W) hR
  rw [map_mul, map_mul, thU_subD h G hO, thU_numD h hW, thU_denD h hW] at h1
  rw [map_mul, map_mul] at h2
  have hD : thU X Kc j U (denD X Kc j) ≠ 0 := by
    intro h0
    exact denD_ne_zero X Kc j (thU_injective hU (by rw [h0, map_zero]))
  rw [thU_denD h hW] at hD
  refine mul_left_cancel₀ hD ?_
  have hk' := kD_ne (X := X) (j := j) hW hk
  calc cD X Kc j (kD X Kc j W κ) * mapT X Kc j W (denD X Kc j) * thU X Kc j U R
      = cD X Kc j (sS X Kc j κ) * mapT X Kc j W (subD X Kc j G) * (cD X Kc j (kN X Kc j W κ) * mapT X Kc j W (numD X Kc j)) := h1.symm
    _ = cD X Kc j (sS X Kc j κ * kN X Kc j W κ) * (mapT X Kc j W (subD X Kc j G) * mapT X Kc j W (numD X Kc j)) := by
        rw [map_mul]; ring
    _ = cD X Kc j (sS X Kc j κ * kN X Kc j W κ) * (mapT X Kc j W (denD X Kc j) * mapT X Kc j W R) := by rw [h2]
    _ = _ := by
        have hinv : cD X Kc j (kD X Kc j W κ) * cD X Kc j (kD X Kc j W κ)⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel₀ hk', map_one]
        rw [map_mul (cD X Kc j) (sS X Kc j κ * kN X Kc j W κ) (kD X Kc j W κ)⁻¹]
        linear_combination (-(cD X Kc j (sS X Kc j κ * kN X Kc j W κ) * mapT X Kc j W (denD X Kc j) * mapT X Kc j W R)) * hinv

end GlobalTheory.FrameB

namespace GlobalTheory.FrameB

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {Kc : Type} [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] {j : ℕ}

theorem coeff_cD_mapT (W : ∀ v : X.Pl, Fin (X.G.P.n' v) → Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc)
    (k : Kc) (P : DA X Kc j) (n : X.ZA j →₀ ℕ) :
    MvPolynomial.coeff n (cD X Kc j k * mapT X Kc j W P) = (k • (tau0 X Kc j W).toLinearMap) (MvPolynomial.coeff n P) := by
  show MvPolynomial.coeff n (MvPolynomial.C _ * MvPolynomial.map _ P) = _
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, LinearMap.smul_apply, Algebra.smul_def]
  rfl

theorem aeval_linT_eq (U : ∀ v : X.Pl, Fin (X.G.P.n' v) → Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc)
    (V : X.ZA j → X.ZA j → Kc)
    (hV : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)) (a a' : Fin (NN X.G.P.m X.t j)) (b b' : Fin (NN X.G.P.m X.t (j + 1))),
      V ⟨v, (s, a, b)⟩ ⟨v, (s, a', b')⟩ = if a = a' then U v s b b' else 0)
    (hV0 : ∀ x y : X.ZA j, (⟨y.1, y.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) ≠ ⟨x.1, x.2.1⟩ → V x y = 0) :
    MvPolynomial.aeval (linT fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (V x y)) = thU X Kc j U := by
  refine MvPolynomial.algHom_ext fun y => ?_
  obtain ⟨v, s, a, b⟩ := y
  rw [MvPolynomial.aeval_X]
  unfold thU
  rw [MvPolynomial.aeval_X]
  unfold linT
  rw [sum_block X j _ v s (fun z hz => by
    beta_reduce
    rw [hV0 z _ (Ne.symm hz), map_zero, map_zero, zero_mul])]
  rw [Finset.sum_eq_single a (fun a' _ ha' => Finset.sum_eq_zero fun b' _ => by
    beta_reduce
    rw [hV, if_neg ha', map_zero, map_zero, zero_mul]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Matrix.mul_apply, Matrix.map_apply, hV, if_pos rfl, dMat]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [mul_comm]
  rfl

end GlobalTheory.FrameB

namespace GlobalTheory.FrameB

open Formalism.L2.KerInert.SecondKernelHermitian

section VOfShape

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {D : Formalism.BasicNotions.D7} (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc]
  (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (c : Kc) (j : ℕ) (La' : X.Lt (j + 1))

def mk (v : X.Pl) (s : Fin (X.G.P.n' v)) : Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc :=
  mAt X Kc (j + 1) v s (fd.frM (j + 1) La' v)

def uV (v : X.Pl) (s : Fin (X.G.P.n' v)) : Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc :=
  if IsOddPos s then c • (mAt X Kc (j + 1) v s (fd.frM (j + 1) La' v)⁻¹).transpose else c • mk Kc fd j La' v s

def wV (v : X.Pl) (s : Fin (X.G.P.n' v)) : Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc :=
  if IsOddPos s then mk Kc fd j La' v s else c • mk Kc fd j La' v s

def kV (v : X.Pl) (s : Fin (X.G.P.n' v)) : Kc :=
  if IsOddPos s then c * (mk Kc fd j La' v s).det⁻¹ else 1

theorem vOf_blk (v : X.Pl) (s : Fin (X.G.P.n' v)) (a a' : Fin (NN X.G.P.m X.t j)) (b b' : Fin (NN X.G.P.m X.t (j + 1))) :
    VOf Kc fd c j La' ⟨v, (s, a, b)⟩ ⟨v, (s, a', b')⟩ = if a = a' then uV Kc fd c j La' v s b b' else 0 := by
  unfold VOf uV mk mAt
  by_cases ha : a = a'
  · subst ha
    rw [if_pos ⟨rfl, rfl⟩, if_pos rfl]
    by_cases ho : IsOddPos s
    · rw [if_pos ho, if_pos ho]
      rfl
    · rw [if_neg ho, if_neg ho]
      rfl
  · rw [if_neg (fun h => ha h.2.symm), if_neg ha]

theorem vOf_off (x y : X.ZA j) (h : (⟨y.1, y.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) ≠ ⟨x.1, x.2.1⟩) :
    VOf Kc fd c j La' x y = 0 := by
  unfold VOf
  rw [if_neg (fun h' => h h'.1)]

theorem trSub_vOf : trSub X Kc j (VOf Kc fd c j La') = thU X Kc j (uV Kc fd c j La') :=
  aeval_linT_eq _ _ (vOf_blk Kc fd c j La') (vOf_off Kc fd c j La')

variable {Kc fd c j La'} (hF : ∀ v, IsUnit (fd.frM (j + 1) La' v).det) (hc : c ≠ 0)
include hF

theorem mk_det_ne (v : X.Pl) (s : Fin (X.G.P.n' v)) : (mk Kc fd j La' v s).det ≠ 0 := by
  unfold mk
  rw [det_mAt]
  exact ((hF v).map (tw X Kc v s)).ne_zero

theorem mAt_inv (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    mAt X Kc (j + 1) v s (fd.frM (j + 1) La' v)⁻¹ = (mk Kc fd j La' v s)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  unfold mk
  rw [mAt_mul, Matrix.mul_nonsing_inv _ (hF v), mAt_one]

include hc

theorem frRel_vOf : FrRel X Kc j (uV Kc fd c j La') (wV Kc fd c j La') (kV Kc fd c j La') := by
  intro v s
  refine ⟨fun ho => ?_, fun ho => ?_⟩
  · unfold uV wV
    rw [if_neg ho, if_neg ho]
  · unfold uV wV kV
    rw [if_pos ho, if_pos ho, if_pos ho, mAt_inv hF, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.transpose_smul,
      Matrix.transpose_transpose, smul_smul]

theorem wV_det_ne (v : X.Pl) (s : Fin (X.G.P.n' v)) : (wV Kc fd c j La' v s).det ≠ 0 := by
  unfold wV
  split_ifs
  · exact mk_det_ne hF v s
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) (mk_det_ne hF v s)

theorem kV_ne (v : X.Pl) (s : Fin (X.G.P.n' v)) : kV Kc fd c j La' v s ≠ 0 := by
  unfold kV
  split_ifs
  · exact mul_ne_zero hc (inv_ne_zero (mk_det_ne hF v s))
  · exact one_ne_zero

theorem uV_unit (v : X.Pl) (s : Fin (X.G.P.n' v)) : IsUnit (uV Kc fd c j La' v s).det := by
  refine isUnit_iff_ne_zero.2 ?_
  unfold uV
  split_ifs
  · rw [Matrix.det_smul, Matrix.det_transpose, mAt_inv hF, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (pow_ne_zero _ hc) (inv_ne_zero (mk_det_ne hF v s))
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) (mk_det_ne hF v s)

end VOfShape

end GlobalTheory.FrameB

namespace GlobalTheory.FrameB

open Formalism.L2.KerInert.SecondKernelHermitian

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {D : Formalism.BasicNotions.D7}

def tauV (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (c : Kc)
    (j : ℕ) (La' : X.Lt (j + 1)) : XspC (X.Pj (j + 1)) Kc →ₗ[Kc] XspC (X.Pj (j + 1)) Kc :=
  (sS X Kc j (kV Kc fd c j La') * kN X Kc j (wV Kc fd c j La') (kV Kc fd c j La') *
      (kD X Kc j (wV Kc fd c j La') (kV Kc fd c j La'))⁻¹) • (tau0 X Kc j (wV Kc fd c j La')).toLinearMap

theorem equiv_frame_b (Y : Pend X) (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (c : Y.Kc) (hc : c ≠ 0) (hF : FrInv fd) (j : ℕ) :
    DelYEqH Y (fun j La' => VOf Y.Kc fd c j La') (fun j c' L' => tauV Y.Kc fd c j (c', L')) j := by
  intro c' L' _ G hG hO n
  have hF' : ∀ v, IsUnit (fd.frM (j + 1) (c', L') v).det := fun v => hF (j + 1) (c', L') v
  rw [trSub_vOf, thU_polDel (frRel_vOf hF' hc) (wV_det_ne hF' hc) (kV_ne hF' hc) (uV_unit hF' hc) G hG hO, coeff_cD_mapT]
  rfl

end GlobalTheory.FrameB

namespace GlobalTheory.FrameB

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelSeries
  Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelHermitian

theorem ltC_ne {p : ℕ} [Fact p.Prime] {g : GL3Theta.G1 p} (hLT : Formalism.L2.G.Pend.LTIso g) : Formalism.L2.PairingIndexBounds.F.ltC g hLT ≠ 0 := by
  unfold Formalism.L2.PairingIndexBounds.F.ltC
  refine inv_ne_zero (mul_ne_zero (Units.ne_zero _) ?_)
  exact ((Units.isUnit _).map (Formalism.L2.G.Pend.wToC p)).ne_zero

end GlobalTheory.FrameB
