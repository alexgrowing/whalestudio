import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGRawSmooth

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

open Formalism.FourierDecayAlt.P.CutMP.Gauge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section fam

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)}

theorem famR_add {Φ Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)} (hΦ : FamR P Bs Dc Φ) (hΨ : FamR P Bs Dc Ψ) :
    FamR P Bs Dc (Φ + Ψ) :=
  ⟨hΦ.1, hΦ.2.1, hΦ.2.2.1, Formalism.FourierDecayAlt.P.Qx3.sf_add hΦ.2.2.2.1 hΨ.2.2.2.1,
    fun c hc => Formalism.FourierDecayAlt.P.Qx8.FFl_add (hΦ.2.2.2.2 c hc) (hΨ.2.2.2.2 c hc)⟩

theorem famR_smul {Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)} (hΦ : FamR P Bs Dc Φ) (a : ℂ) :
    FamR P Bs Dc (a • Φ) :=
  ⟨hΦ.1, hΦ.2.1, hΦ.2.2.1, Formalism.FourierDecayAlt.P.Qx3.sf_csmul a hΦ.2.2.2.1,
    fun c hc => Formalism.FourierDecayAlt.P.Qx8.FFl_smul (hΦ.2.2.2.2 c hc) a⟩

theorem famR_neg {Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)} (hΦ : FamR P Bs Dc Φ) : FamR P Bs Dc (-Φ) := by
  have h := famR_smul hΦ (-1)
  rwa [neg_one_smul] at h

theorem famR_sub {Φ Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)} (hΦ : FamR P Bs Dc Φ) (hΨ : FamR P Bs Dc Ψ) :
    FamR P Bs Dc (Φ - Ψ) := by
  rw [sub_eq_add_neg]
  exact famR_add hΦ (famR_neg hΨ)

theorem famR_zero (hΦ : FamR P Bs Dc (fun _ _ => 0)) : FamR P Bs Dc 0 := hΦ

theorem famR_opL {Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)} (hΦ : FamR P Bs Dc Φ) (a : Fin P.r) (j : Fin 6) :
    FamR P Bs Dc (Q.crd (opL a j) Φ) :=
  ⟨hΦ.1, hΦ.2.1, hΦ.2.2.1, Formalism.FourierDecayAlt.P.family_operators Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Fin.last P.r) Dc Φ
    Bs.z_mem Bs.z'_mem hΦ.1 hΦ.2.2.2 a j⟩

end fam

section tr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsV_add (A C : Wq →L[ℂ] Wp) : B.hsVec (A + C) = B.hsVec A + B.hsVec C := by
  unfold B.hsVec; ext i; simp

theorem hsV_smul (a : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (a • A) = a • B.hsVec A := by
  unfold B.hsVec; ext i; simp

theorem hsV_zero : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsVec; ext i; simp

def Lin (v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) : (Wq →L[ℂ] Wp) →ₗ[ℂ] ℂ where
  toFun A := inner ℂ v (B.hsVec A)
  map_add' A C := by rw [hsV_add, inner_add_right]
  map_smul' a A := by rw [hsV_smul, inner_smul_right]; rfl

theorem Lin_apply (v : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) (A : Wq →L[ℂ] Wp) :
    Lin v A = inner ℂ v (B.hsVec A) := rfl

variable (P : M.Par)

def trR (μ : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) : M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P (rawR P μ e Φ ρ)

variable {P} (μ : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))

theorem rawR_add (Φ Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) :
    rawR P μ e (Φ + Ψ) ρ = rawR P μ e Φ ρ + rawR P μ e Ψ ρ := by
  funext q
  simp only [rawR, Pi.add_apply, hsV_add, inner_add_right, mul_add]

theorem rawR_smul (a : ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) :
    rawR P μ e (a • Φ) ρ = a • rawR P μ e Φ ρ := by
  funext q
  simp only [rawR, Pi.smul_apply, hsV_smul, inner_smul_right, smul_eq_mul]
  ring

theorem rawR_zero (ρ : M.Ty P) : rawR P μ e 0 ρ = 0 := by
  funext q
  simp [rawR, hsV_zero]

theorem toSm_smul (a : ℂ) (u : MA.Qp P.r P.TT → ℂ) : MA.toSm P (a • u) = a • MA.toSm P u := by
  by_cases hu : u ∈ MA.smSub P.r P.TT
  · rw [toSm_of_mem P hu, toSm_of_mem P (Subalgebra.smul_mem _ hu a)]
    rfl
  · by_cases ha : a = 0
    · subst ha
      rw [zero_smul, zero_smul, toSm_of_mem P (zero_mem _)]
      rfl
    · have h : a • u ∉ MA.smSub P.r P.TT := fun h => hu (by
        have := Subalgebra.smul_mem _ h a⁻¹
        rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this)
      simp [MA.toSm, hu, h]

theorem toSm_zero : MA.toSm P (0 : MA.Qp P.r P.TT → ℂ) = 0 := by
  rw [toSm_of_mem P (zero_mem _)]
  rfl

theorem trR_smul (a : ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) : trR P μ e (a • Φ) = a • trR P μ e Φ := by
  funext ρ
  simp only [trR, rawR_smul, toSm_smul, Pi.smul_apply]

theorem trR_zero : trR P μ e 0 = 0 := by
  funext ρ
  simp only [trR, rawR_zero, toSm_zero, Pi.zero_apply]

theorem trR_add (Φ Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΦ : ∀ ρ, rawR P μ e Φ ρ ∈ MA.smSub P.r P.TT)
    (hΨ : ∀ ρ, rawR P μ e Ψ ρ ∈ MA.smSub P.r P.TT) : trR P μ e (Φ + Ψ) = trR P μ e Φ + trR P μ e Ψ := by
  funext ρ
  simp only [trR, rawR_add, Pi.add_apply]
  exact toSm_add P (hΦ ρ) (hΨ ρ)

theorem trR_sub (Φ Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΦ : ∀ ρ, rawR P μ e Φ ρ ∈ MA.smSub P.r P.TT)
    (hΨ : ∀ ρ, rawR P μ e Ψ ρ ∈ MA.smSub P.r P.TT) : trR P μ e (Φ - Ψ) = trR P μ e Φ - trR P μ e Ψ := by
  have hΨ' : ∀ ρ, rawR P μ e ((-1 : ℂ) • Ψ) ρ ∈ MA.smSub P.r P.TT := fun ρ => by
    rw [rawR_smul]; exact Subalgebra.smul_mem _ (hΨ ρ) _
  rw [sub_eq_add_neg, ← neg_one_smul ℂ Ψ, trR_add μ e _ _ hΦ hΨ', trR_smul, neg_one_smul, ← sub_eq_add_neg]

end tr

section coord

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem muZ_glev (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) := by
  have hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
    exact q.2.2
  exact Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mem_UWb (Bs.sec.2 _ hζ).1)

theorem fderiv_ext (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    {Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)} {Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)} (hΦ : FamR P Bs Dc Φ)
    (ρ : M.Ty P) (q : MA.Qp P.r P.TT) (d : Fin P.r → ℂ) :
    fderiv ℝ (MA.ext (rawR P Bs.μsec e Φ ρ)) q.1 (d, 0) =
      ((wR P.k P.TT q.1.2 : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ q.1.2))
        (B.hsVec (fderiv ℝ (fun c' => Φ c' (NF.muZ P.k P.r Bs.μsec q.1.2)) q.1.1 d)) := by
  have hu := raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he Dc Φ hΦ ρ
  have hdiff : DifferentiableAt ℝ (MA.ext (rawR P Bs.μsec e Φ ρ)) q.1 := MA.ext_smooth_diff hu q.1 q.2
  have hι : HasFDerivAt (fun c' : Fin P.r → ℂ => ((c', q.1.2) : MA.E P.r))
      (ContinuousLinearMap.inl ℝ (Fin P.r → ℂ) ℂ) q.1.1 := hasFDerivAt_prodMk_left q.1.1 q.1.2
  have hcomp : HasFDerivAt (fun c' : Fin P.r → ℂ => MA.ext (rawR P Bs.μsec e Φ ρ) (c', q.1.2))
      ((fderiv ℝ (MA.ext (rawR P Bs.μsec e Φ ρ)) q.1).comp (ContinuousLinearMap.inl ℝ (Fin P.r → ℂ) ℂ)) q.1.1 :=
    by
      have h0 : HasFDerivAt (MA.ext (rawR P Bs.μsec e Φ ρ)) (fderiv ℝ (MA.ext (rawR P Bs.μsec e Φ ρ)) q.1)
          ((fun c' : Fin P.r → ℂ => ((c', q.1.2) : MA.E P.r)) q.1.1) := hdiff.hasFDerivAt
      have := h0.comp q.1.1 hι
      exact this
  have hopen : ∀ᶠ c' in nhds q.1.1, ((c', q.1.2) : MA.E P.r) ∈ MA.Qset P.r P.TT :=
    hι.continuousAt.preimage_mem_nhds ((MA.Qset_open _ _).mem_nhds q.2)
  set m := NF.muZ P.k P.r Bs.μsec q.1.2 with hm
  set v := B.hsVec (e ρ q.1.2) with hv
  let Lr : (Wq →L[ℂ] Wp) →L[ℝ] ℂ := (LinearMap.toContinuousLinearMap (Lin v)).restrictScalars ℝ
  have hLr : ∀ A, Lr A = inner ℂ v (B.hsVec A) := fun A => rfl
  have heq : (fun c' : Fin P.r → ℂ => MA.ext (rawR P Bs.μsec e Φ ρ) (c', q.1.2)) =ᶠ[nhds q.1.1]
      fun c' => ((wR P.k P.TT q.1.2 : ℝ) : ℂ) * Lr (Φ c' m) := by
    filter_upwards [hopen] with c' hc'
    simp only [MA.ext, hc', dif_pos, rawR, hLr, hv, hm]
  have hd : DifferentiableAt ℝ (fun c' => Φ c' m) q.1.1 :=
    Formalism.FourierDecayAlt.P.Qx3.fam_differentiableAt (x := (q.1.1, m)) hΦ.2.2.2.1 ⟨q.2.1, hΦ.2.2.1 q⟩ (muZ_glev hpl q)
  have hg : HasFDerivAt (fun c' => ((wR P.k P.TT q.1.2 : ℝ) : ℂ) * Lr (Φ c' m))
      (((wR P.k P.TT q.1.2 : ℝ) : ℂ) • Lr.comp (fderiv ℝ (fun c' => Φ c' m) q.1.1)) q.1.1 :=
    (Lr.hasFDerivAt.comp q.1.1 hd.hasFDerivAt).const_mul _
  have h1 : fderiv ℝ (MA.ext (rawR P Bs.μsec e Φ ρ)) q.1 (d, 0) =
      fderiv ℝ (fun c' : Fin P.r → ℂ => MA.ext (rawR P Bs.μsec e Φ ρ) (c', q.1.2)) q.1.1 d := by
    rw [hcomp.fderiv]
    rfl
  rw [h1, heq.fderiv_eq, hg.fderiv]
  rfl

end coord

section ops

variable {r : ℕ} {TT : ℝ}

theorem dirE_vc (l : Fin r) : MA.dirE (M.vc l) = ((Pi.single l 1, 0) : MA.E r) := by
  simp [MA.dirE, M.vc]

theorem dirE_vcb (l : Fin r) : MA.dirE (M.vcb l) = ((Pi.single l 1, 0) : MA.E r) := by
  simp [MA.dirE, M.vcb]

theorem I_dirE_vc (l : Fin r) : Complex.I • MA.dirE (M.vc l) = ((Pi.single l Complex.I, 0) : MA.E r) := by
  rw [dirE_vc]
  ext j <;> simp [Pi.single_apply]

theorem I_dirE_vcb (l : Fin r) : Complex.I • MA.dirE (M.vcb l) = ((Pi.single l Complex.I, 0) : MA.E r) := by
  rw [dirE_vcb]
  ext j <;> simp [Pi.single_apply]

theorem coordE_vc (l : Fin r) (x : MA.E r) : MA.coordE (M.vc l) x = x.1 l := by
  simp [MA.coordE, MA.zE, M.vc]

theorem coordE_vcb (l : Fin r) (x : MA.E r) : MA.coordE (M.vcb l) x = star (x.1 l) := by
  simp [MA.coordE, MA.zE, M.vcb]

theorem sgn_vc (l : Fin r) : (ofLex (M.vc l)).2 = 0 := by simp [M.vc]

theorem sgn_vcb (l : Fin r) : ¬ (ofLex (M.vcb l)).2 = 0 := by simp [M.vcb]

theorem inv_coordQ_apply (v : M.Var r) (hv : ∀ x ∈ MA.Qset r TT, MA.coordE v x ≠ 0) (q : MA.Qp r TT) :
    ((Ring.inverse (MA.coordQ (TT := TT) v) : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = (MA.coordE v q.1)⁻¹ := by
  have hsm : (fun q : MA.Qp r TT => (MA.coordE v q.1)⁻¹) ∈ MA.smSub r TT := by
    show ContDiffOn ℝ MA.sm (MA.ext fun q : MA.Qp r TT => (MA.coordE v q.1)⁻¹) (MA.Qset r TT)
    refine (((MA.coordE_smooth v).contDiffOn).inv fun x hx => hv x hx).congr fun x hx => ?_
    simp [MA.ext, hx]
  let w : MA.SmQ r TT := ⟨_, hsm⟩
  have h1 : MA.coordQ (TT := TT) v * w = 1 := by
    apply Subtype.ext; funext q
    show MA.coordE v q.1 * (MA.coordE v q.1)⁻¹ = 1
    exact mul_inv_cancel₀ (hv q.1 q.2)
  have h2 : w * MA.coordQ (TT := TT) v = 1 := by
    apply Subtype.ext; funext q
    show (MA.coordE v q.1)⁻¹ * MA.coordE v q.1 = 1
    exact inv_mul_cancel₀ (hv q.1 q.2)
  let u : (MA.SmQ r TT)ˣ := ⟨MA.coordQ v, w, h1, h2⟩
  have hu : (u : MA.SmQ r TT) = MA.coordQ v := rfl
  rw [← hu, Ring.inverse_unit]
  rfl

end ops

section coordTr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}
  {Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)} {Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)}

theorem smR (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (hΦ : FamR P Bs Dc Φ) (ρ : M.Ty P) : rawR P Bs.μsec e Φ ρ ∈ MA.smSub P.r P.TT :=
  raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he Dc Φ hΦ ρ

theorem trR_val (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (hΦ : FamR P Bs Dc Φ) (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    ((trR P Bs.μsec e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = rawR P Bs.μsec e Φ ρ q := by
  unfold trR
  rw [toSm_of_mem P (smR hpl hk he hΦ ρ)]

theorem trR_p (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (hΦ : FamR P Bs Dc Φ) (l : Fin P.r) :
    trR P Bs.μsec e (Q.crd (pOp l) Φ) = fun ρ => MA.eulerQ (TT := P.TT) (M.vc l) (trR P Bs.μsec e Φ ρ) := by
  have hΦ' : FamR P Bs Dc (Q.crd (pOp l) Φ) := famR_opL hΦ l 0
  funext ρ
  apply Subtype.ext; funext q
  rw [trR_val hpl hk he hΦ' ρ q]
  show _ = MA.coordE (M.vc l) q.1 * MA.wirt (M.vc l) (MA.ext ((trR P Bs.μsec e Φ ρ : MA.SmQ P.r P.TT) :
    MA.Qp P.r P.TT → ℂ)) q.1
  have he1 : ((trR P Bs.μsec e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) = rawR P Bs.μsec e Φ ρ :=
    funext fun q' => trR_val hpl hk he hΦ ρ q'
  rw [he1, MA.wirt, I_dirE_vc, dirE_vc, if_pos (sgn_vc l), coordE_vc, fderiv_ext hpl hk he hΦ,
    fderiv_ext hpl hk he hΦ]
  have hc : q.1.1 ∈ OmX P.r := q.2.1
  simp only [rawR, Q.crd, pOp, if_pos hc, wirt]
  have key : ∀ X : Wq →L[ℂ] Wp, inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec X) = Lin (B.hsVec (e ρ q.1.2)) X :=
    fun _ => rfl
  simp only [key, map_smul, map_sub, smul_eq_mul]
  ring

theorem trR_pb (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (hΦ : FamR P Bs Dc Φ) (l : Fin P.r) :
    trR P Bs.μsec e (Q.crd (pbOp l) Φ) = fun ρ => MA.eulerQ (TT := P.TT) (M.vcb l) (trR P Bs.μsec e Φ ρ) := by
  have hΦ' : FamR P Bs Dc (Q.crd (pbOp l) Φ) := famR_opL hΦ l 3
  funext ρ
  apply Subtype.ext; funext q
  rw [trR_val hpl hk he hΦ' ρ q]
  show _ = MA.coordE (M.vcb l) q.1 * MA.wirt (M.vcb l) (MA.ext ((trR P Bs.μsec e Φ ρ : MA.SmQ P.r P.TT) :
    MA.Qp P.r P.TT → ℂ)) q.1
  have he1 : ((trR P Bs.μsec e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) = rawR P Bs.μsec e Φ ρ :=
    funext fun q' => trR_val hpl hk he hΦ ρ q'
  rw [he1, MA.wirt, I_dirE_vcb, dirE_vcb, if_neg (sgn_vcb l), coordE_vcb, fderiv_ext hpl hk he hΦ,
    fderiv_ext hpl hk he hΦ]
  have hc : q.1.1 ∈ OmX P.r := q.2.1
  simp only [rawR, Q.crd, pbOp, if_pos hc, wirtBar]
  have key : ∀ X : Wq →L[ℂ] Wp, inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec X) = Lin (B.hsVec (e ρ q.1.2)) X :=
    fun _ => rfl
  simp only [key, map_smul, map_add, smul_eq_mul]
  ring

theorem trR_mul (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (hΦ : FamR P Bs Dc Φ) (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΨ : FamR P Bs Dc Ψ) (f : (Fin P.r → ℂ) → ℂ)
    (hfΨ : ∀ c g, Ψ c g = f c • Φ c g) (φ : MA.SmQ P.r P.TT)
    (hφ : ∀ q : MA.Qp P.r P.TT, (φ : MA.Qp P.r P.TT → ℂ) q = f q.1.1) :
    trR P Bs.μsec e Ψ = fun ρ => φ * trR P Bs.μsec e Φ ρ := by
  funext ρ
  apply Subtype.ext; funext q
  rw [trR_val hpl hk he hΨ ρ q]
  show _ = (φ : MA.Qp P.r P.TT → ℂ) q * ((trR P Bs.μsec e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q
  rw [trR_val hpl hk he hΦ ρ q, hφ q]
  simp only [rawR, hfΨ, hsV_smul, inner_smul_right]
  ring

end coordTr

section model

variable (P : M.Par)

theorem actA_diag (d : M.Ty P → (MA.DQ P).Pr) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (Matrix.diagonal d) f = fun ρ => (d ρ).1 (f ρ) := by
  funext ρ
  show ∑ π', (Matrix.diagonal d ρ π').1 (f π') = (d ρ).1 (f ρ)
  refine (Finset.sum_eq_single ρ (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ ρ) h)).trans ?_
  · have h0 : Matrix.diagonal d ρ b = 0 := Matrix.diagonal_apply_ne _ (Ne.symm hb)
    exact (congrArg (fun w : (MA.DQ P).Pr => w.1 (f b)) h0).trans (op_zero_apply P (f b))
  · have h1 : Matrix.diagonal d ρ ρ = d ρ := Matrix.diagonal_apply_eq _ _
    exact congrArg (fun w : (MA.DQ P).Pr => w.1 (f ρ)) h1

theorem actA_sc (w : (MA.DQ P).Pr) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.sc P (MA.DQ P) w) f = fun ρ => w.1 (f ρ) := by
  rw [MA.sc, Matrix.scalar_apply, actA_diag]

theorem actA_one (f : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 1 f = f := by
  rw [← Matrix.diagonal_one, actA_diag]
  rfl

theorem actA_algebraMap (Y : ℂ) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (algebraMap ℂ (MA.A P (MA.DQ P)) Y) f = Y • f := by
  rw [Matrix.algebraMap_eq_diagonal, actA_diag]
  funext ρ
  show (algebraMap ℂ (MA.DQ P).Op Y) (f ρ) = Y • f ρ
  rfl

theorem actA_neg (x : MA.A P (MA.DQ P)) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (-x) f = -MA.actA P x f := by
  have h := actA_add P x (-x) f
  rw [add_neg_cancel, actA_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem star_sc (w : (MA.DQ P).Pr) : star (MA.sc P (MA.DQ P) w) = MA.sc P (MA.DQ P) (star w) := by
  rw [MA.sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, MA.sc,
    Matrix.scalar_apply]
  rfl

end model

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem
