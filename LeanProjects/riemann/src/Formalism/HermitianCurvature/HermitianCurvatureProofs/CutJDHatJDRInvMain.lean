import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvCov

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.RInvCov

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B

theorem assembleP {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*} [Fintype ι] {t N : ℕ}
    (T : Finset (Fin t → Fin N)) (al : ι → ℂ) (R : ι → Fin t → Fin N) (be be' : (Fin t → Fin N) → ℂ)
    (pc : (Fin t → Fin N) → ι → ℂ) (qd : (Fin t → Fin N) → (Fin t → Fin N) → ℂ)
    (D : (Fin t → Fin N) → (Fin t → Fin N) → M) (lam mu : ℂ) (hlm : lam * mu = 1)
    (hA : ∀ X : (Fin t → Fin N) → M, ∑ c ∈ T, (∑ i, al i * pc c i) • X c = lam • ∑ i, al i • X (R i))
    (hB : ∀ d, ∑ J ∈ T, be J * qd J d = mu * be' d) :
    ∑ i, ∑ J ∈ T, (al i * be J) • ∑ c ∈ T, ∑ d ∈ T, (pc c i * qd J d) • D c d =
      ∑ i, ∑ J ∈ T, (al i * be' J) • D (R i) J := by
  have e1 : ∑ i, ∑ J ∈ T, (al i * be J) • ∑ c ∈ T, ∑ d ∈ T, (pc c i * qd J d) • D c d =
      ∑ c ∈ T, ∑ d ∈ T, ∑ i, ∑ J ∈ T, (al i * pc c i * (be J * qd J d)) • D c d := by
    simp only [Finset.smul_sum, smul_smul]
    calc ∑ i, ∑ J ∈ T, ∑ c ∈ T, ∑ d ∈ T, (al i * be J * (pc c i * qd J d)) • D c d
        = ∑ i, ∑ c ∈ T, ∑ J ∈ T, ∑ d ∈ T, (al i * be J * (pc c i * qd J d)) • D c d :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ c ∈ T, ∑ i, ∑ J ∈ T, ∑ d ∈ T, (al i * be J * (pc c i * qd J d)) • D c d := Finset.sum_comm
      _ = ∑ c ∈ T, ∑ i, ∑ d ∈ T, ∑ J ∈ T, (al i * be J * (pc c i * qd J d)) • D c d :=
          Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
      _ = ∑ c ∈ T, ∑ d ∈ T, ∑ i, ∑ J ∈ T, (al i * be J * (pc c i * qd J d)) • D c d :=
          Finset.sum_congr rfl (fun c _ => Finset.sum_comm)
      _ = _ := by
          refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ =>
            Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => ?_))))
          congr 1
          ring
  have e2 : ∑ c ∈ T, ∑ d ∈ T, ∑ i, ∑ J ∈ T, (al i * pc c i * (be J * qd J d)) • D c d =
      ∑ c ∈ T, (∑ i, al i * pc c i) • ∑ d ∈ T, (∑ J ∈ T, be J * qd J d) • D c d := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [smul_smul, Finset.sum_mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_smul]
  rw [e1, e2]
  simp_rw [hB]
  rw [hA (fun c => ∑ d ∈ T, (mu * be' d) • D c d)]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => ?_))
  congr 1
  linear_combination (al i * be' J) * hlm

theorem assembleM {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*} [Fintype ι] {t N : ℕ}
    (T : Finset (Fin t → Fin N)) (bb : ι → ℂ) (C : ι → Fin t → Fin N) (al al' : (Fin t → Fin N) → ℂ)
    (pc : (Fin t → Fin N) → (Fin t → Fin N) → ℂ) (qd : ι → (Fin t → Fin N) → ℂ)
    (D : (Fin t → Fin N) → (Fin t → Fin N) → M) (lam mu : ℂ) (hlm : lam * mu = 1)
    (hA : ∀ c, ∑ J ∈ T, al J * pc c J = lam * al' c)
    (hB : ∀ X : (Fin t → Fin N) → M, ∑ d ∈ T, (∑ i, bb i * qd i d) • X d = mu • ∑ i, bb i • X (C i)) :
    ∑ i, ∑ J ∈ T, (bb i * al J) • ∑ c ∈ T, ∑ d ∈ T, (pc c J * qd i d) • D c d =
      ∑ i, ∑ J ∈ T, (bb i * al' J) • D J (C i) := by
  have e1 : ∑ i, ∑ J ∈ T, (bb i * al J) • ∑ c ∈ T, ∑ d ∈ T, (pc c J * qd i d) • D c d =
      ∑ d ∈ T, ∑ c ∈ T, ∑ i, ∑ J ∈ T, (bb i * qd i d * (al J * pc c J)) • D c d := by
    simp only [Finset.smul_sum, smul_smul]
    calc ∑ i, ∑ J ∈ T, ∑ c ∈ T, ∑ d ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d
        = ∑ i, ∑ c ∈ T, ∑ J ∈ T, ∑ d ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ i, ∑ c ∈ T, ∑ d ∈ T, ∑ J ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun c _ => Finset.sum_comm))
      _ = ∑ i, ∑ d ∈ T, ∑ c ∈ T, ∑ J ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ d ∈ T, ∑ i, ∑ c ∈ T, ∑ J ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d := Finset.sum_comm
      _ = ∑ d ∈ T, ∑ c ∈ T, ∑ i, ∑ J ∈ T, (bb i * al J * (pc c J * qd i d)) • D c d :=
          Finset.sum_congr rfl (fun d _ => Finset.sum_comm)
      _ = _ := by
          refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun c _ =>
            Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => ?_))))
          congr 1
          ring
  have e2 : ∑ d ∈ T, ∑ c ∈ T, ∑ i, ∑ J ∈ T, (bb i * qd i d * (al J * pc c J)) • D c d =
      ∑ d ∈ T, (∑ i, bb i * qd i d) • ∑ c ∈ T, (∑ J ∈ T, al J * pc c J) • D c d := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [smul_smul, Finset.sum_mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_smul]
  rw [e1, e2]
  simp_rw [hA]
  rw [hB (fun d => ∑ c ∈ T, (lam * al' c) • D c d)]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => ?_))
  congr 1
  linear_combination (bb i * al' J) * hlm

end Formalism.FourierDecayAlt.P.CutMP.RInvCov

namespace Formalism.FourierDecayAlt.P.CutMP.RInvCov

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem one_GV : (1 : Mat k r) ∈ GV k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem left_GV (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) :
    (Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r := by
  have := WeylGroupFacts.uh_inv (Formalism.FourierDecayAlt.P.B5.inSS_left D hp)
  rwa [Matrix.mul_inv_rev] at this

theorem rho_eq (D : RealPlaceData k r Wp Wq) (p : SS k r) (G : Mat k r → (Wq →L[ℂ] Wp)) :
    B.rho D p G = fun x => Formalism.FourierDecayAlt.P.JFxB.Lq D p
      (G ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1)))) := by
  rw [Formalism.FourierDecayAlt.P.JFxB.rho_eq_trn']
  funext x
  simp only [Formalism.FourierDecayAlt.P.BetaSesquilinearity.trn, Matrix.mul_assoc]

open Classical in
theorem jset_eq : (Finset.univ.filter fun C : Fin (r + k) → Fin (2 * r + k + 1) => StrictMono C) = jSetR k r := rfl

theorem qminor_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn ((r + k : ℕ) : ℕ∞) (GV k r) F) {g : Mat k r} (hg : g ∈ GV k r)
    (a b : Fin (r + k) → Fin (2 * r + k + 1)) (u : ℂ) :
    qminorOp (Q.EH k r) a b u (B.rho D p F) g = Formalism.FourierDecayAlt.P.JFxB.Lq D p
      (∑ c ∈ jSetR k r, ∑ d ∈ jSetR k r,
        (((Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r)⁻¹.submatrix c a).det *
          ((Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r).submatrix b d).det) •
        qminorOp (Q.EH k r) c d u F
          ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1)))) := by
  have hSG : (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r) ∈ GV k r := Formalism.FourierDecayAlt.P.B5.inSS_right D hp
  have hAG := left_GV D hp
  have hgS : g * (Matrix.of p.2.2 * Matrix.of p.2.1) ∈ GV k r := WeylGroupFacts.uh_mul hg hSG
  have hG' : CkOn ((r + k : ℕ) : ℕ∞) (GV k r) (fun x =>
      F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1)))) := by
    have := Formalism.FourierDecayAlt.P.B5.ckOn_translate hF hAG hSG
    have e : (fun x => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * (Matrix.of p.2.2 * Matrix.of p.2.1))) =
        fun x => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1))) := by
      funext x; simp only [Matrix.mul_assoc]
    rwa [e] at this
  have hFa : Loc ((r + k : ℕ) : ℕ∞) (fun y => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * y))
      (g * (Matrix.of p.2.2 * Matrix.of p.2.1)) := by
    have := Formalism.FourierDecayAlt.P.B5.ckOn_translate hF hAG (one_GV (k := k) (r := r))
    have e : (fun x => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * 1)) =
        fun y => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * y) := by
      funext x; simp only [Matrix.mul_one]
    rw [e] at this
    exact this _ hgS
  rw [rho_eq D p F]
  have h1 : qminorOp (Q.EH k r) a b u (fun x => Formalism.FourierDecayAlt.P.JFxB.Lq D p
      (F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1))))) g =
      Formalism.FourierDecayAlt.P.JFxB.Lq D p (qminorOp (Q.EH k r) a b u (fun x =>
        F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (x * (Matrix.of p.2.2 * Matrix.of p.2.1)))) g) :=
    Formalism.FourierDecayAlt.P.CutMP.CapInv.post_qm (Formalism.FourierDecayAlt.P.JFxB.Lq D p) _ hG' a b u hg
  rw [h1]
  congr 1
  have h2 := qminor_right (Matrix.of p.2.2 * Matrix.of p.2.1) hSG a b u
    (fun y => F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * y)) g hgS hFa
  rw [jset_eq] at h2
  refine h2.trans (Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_)))
  rw [qminor_left]

end Formalism.FourierDecayAlt.P.CutMP.RInvCov

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B RInvCov

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jDRInvFn_of (hA : RInvAlphaP) (hB : RInvBetaP) (hBL : RInvBetaLeftP) : JDRInvFn := by
  intro k r Wp Wq _ _ _ _ D Y p hp F hF g hg
  have hgG : g ∈ B.GV k r := hg.1
  have hSG : (Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r) ∈ B.GV k r := Formalism.FourierDecayAlt.P.B5.inSS_right D hp
  have hgS : g * (Matrix.of p.2.2 * Matrix.of p.2.1) ∈ B.GV k r := WeylGroupFacts.uh_mul hgG hSG
  rw [rho_eq D p (rhatOp k r D.z D.z' Y F)]
  show rhatOp k r D.z D.z' Y (B.rho D p F) g = Formalism.FourierDecayAlt.P.JFxB.Lq D p (rhatOp k r D.z D.z' Y F
    ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))))
  simp only [rhatOp]
  rw [map_sum]
  refine Eq.trans (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => by
    rw [qminor_rho D hp hF hgG]))) ?_
  have key := assembleP (M := Wq →L[ℂ] Wp) (jSetR k r) (alP k r D.z') (rowsR k r)
    (fun J => beJ k r D.z g J)
    (fun J => beJ k r D.z ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))) J)
    (fun c i => (((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r)⁻¹).submatrix c (rowsR k r i)).det)
    (fun J d => ((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r).submatrix J d).det)
    (fun c d => qminorOp (Q.EH k r) c d (Q.uC k r 0 Y) F
      ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))))
    ((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r)⁻¹).det (Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r).det
    (by rw [← Matrix.det_mul, (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hSG).2, Matrix.det_one])
    (fun X => hA k r D.z' (Matrix.of p.2.1) (Matrix.of p.2.2) D.z'_mem hp.2.2.1 hp.2.2.2 (Wq →L[ℂ] Wp) X)
    (fun d => by
      rw [hB k r D.z g _ hgG hSG d, hBL k r D.z _ _ _ D.z_mem hp.1 hp.2.1 hgS d])
  have key2 := congrArg (Formalism.FourierDecayAlt.P.JFxB.Lq D p) key
  simp only [map_sum, map_smul] at key2 ⊢
  refine Eq.trans ?_ (key2.trans ?_)
  · rfl
  · rfl

theorem jDRInvFnM_of (hA : RInvAlphaM) (hAL : RInvAlphaLeftM) (hB : RInvBetaM) : JDRInvFnM := by
  intro k r Wp Wq _ _ _ _ D Y p hp F hF g hg
  have hgG : g ∈ B.GV k r := hg.1
  have hSG : (Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r) ∈ B.GV k r := Formalism.FourierDecayAlt.P.B5.inSS_right D hp
  have hgS : g * (Matrix.of p.2.2 * Matrix.of p.2.1) ∈ B.GV k r := WeylGroupFacts.uh_mul hgG hSG
  rw [rho_eq D p (rvhatOp k r D.z D.z' Y F)]
  show rvhatOp k r D.z D.z' Y (B.rho D p F) g = Formalism.FourierDecayAlt.P.JFxB.Lq D p (rvhatOp k r D.z D.z' Y F
    ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))))
  simp only [rvhatOp]
  rw [map_sum]
  refine Eq.trans (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun J _ => by
    rw [qminor_rho D hp hF hgG]))) ?_
  have key := assembleM (M := Wq →L[ℂ] Wp) (jSetR k r) (beM k r D.z') (colsV k r)
    (fun J => alJ k r D.z g J)
    (fun J => alJ k r D.z ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))) J)
    (fun c J => (((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r)⁻¹).submatrix c J).det)
    (fun t d => ((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r).submatrix (colsV k r t) d).det)
    (fun c d => qminorOp (Q.EH k r) c d (Q.uC k r (Fin.last r) Y - 1) F
      ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (g * (Matrix.of p.2.2 * Matrix.of p.2.1))))
    ((Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r)⁻¹).det (Matrix.of p.2.2 * Matrix.of p.2.1 : B.Mat k r).det
    (by rw [← Matrix.det_mul, (Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.gv_inv hSG).2, Matrix.det_one])
    (fun c => by
      rw [hA k r D.z g _ hgG hSG c, hAL k r D.z _ _ _ D.z_mem hp.1 hp.2.1 hgS c])
    (fun X => hB k r D.z' (Matrix.of p.2.1) (Matrix.of p.2.2) D.z'_mem hp.2.2.1 hp.2.2.2 (Wq →L[ℂ] Wp) X)
  have key2 := congrArg (Formalism.FourierDecayAlt.P.JFxB.Lq D p) key
  simp only [map_sum, map_smul] at key2 ⊢
  refine Eq.trans ?_ (key2.trans ?_)
  · rfl
  · rfl

end Formalism.FourierDecayAlt.P.CutMP
