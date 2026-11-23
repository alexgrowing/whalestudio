import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeVLem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GT

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

section sm

variable {r : ℕ} {TT : ℝ}

theorem smInv_mem (f : MA.SmQ r TT) (hf : ∀ q, (f : MA.Qp r TT → ℂ) q ≠ 0) :
    (fun q => ((f : MA.Qp r TT → ℂ) q)⁻¹) ∈ MA.smSub r TT := by
  have hsm : ContDiffOn ℝ MA.sm (MA.ext (f : MA.Qp r TT → ℂ)) (MA.Qset r TT) := f.2
  have hne : ∀ x ∈ MA.Qset r TT, MA.ext (f : MA.Qp r TT → ℂ) x ≠ 0 := by
    intro x hx
    simp only [MA.ext, dif_pos hx]
    exact hf _
  show ContDiffOn ℝ MA.sm (MA.ext (fun q => ((f : MA.Qp r TT → ℂ) q)⁻¹)) (MA.Qset r TT)
  exact (hsm.inv hne).congr fun x hx => by simp only [Pi.inv_apply, MA.ext, dif_pos hx]

theorem inverse_apply (f : MA.SmQ r TT) (hf : ∀ q, (f : MA.Qp r TT → ℂ) q ≠ 0) (q : MA.Qp r TT) :
    ((Ring.inverse f : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = ((f : MA.Qp r TT → ℂ) q)⁻¹ := by
  obtain ⟨g, hg⟩ : ∃ g : MA.SmQ r TT, ∀ q, (g : MA.Qp r TT → ℂ) q = ((f : MA.Qp r TT → ℂ) q)⁻¹ :=
    ⟨⟨_, smInv_mem f hf⟩, fun _ => rfl⟩
  have hfg : f * g = 1 := by
    apply Subtype.ext
    funext q'
    show (f : MA.Qp r TT → ℂ) q' * (g : MA.Qp r TT → ℂ) q' = 1
    rw [hg, mul_inv_cancel₀ (hf q')]
  have hu : IsUnit f := ⟨⟨f, g, hfg, by rw [mul_comm]; exact hfg⟩, rfl⟩
  have hinv : Ring.inverse f = g := by
    calc Ring.inverse f = Ring.inverse f * (f * g) := by rw [hfg, mul_one]
      _ = g := by rw [← mul_assoc, Ring.inverse_mul_cancel f hu, one_mul]
  rw [hinv, hg]

theorem coordQ_vz (q : MA.Qp r TT) : ((MA.coordQ (r := r) (TT := TT) M.vz : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = q.1.2 := by
  show MA.coordE (M.vz (r := r)) q.1 = q.1.2
  simp [MA.coordE, MA.zE, M.vz]

theorem coordQ_vzb (q : MA.Qp r TT) :
    ((MA.coordQ (r := r) (TT := TT) M.vzb : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = (starRingEnd ℂ) q.1.2 := by
  show MA.coordE (M.vzb (r := r)) q.1 = (starRingEnd ℂ) q.1.2
  simp [MA.coordE, MA.zE, M.vzb]

end sm

def ggS (P : M.Par) : MA.SmQ P.r P.TT := (MA.DQ P).gg P.TT

section tr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem trR_unit (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (φ : MA.SmQ P.r P.TT) (hφ : ∀ q, (φ : MA.Qp P.r P.TT → ℂ) q ≠ 0)
    (hΨ : ∀ q : MA.Qp P.r P.TT, (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
      (φ : MA.Qp P.r P.TT → ℂ) q • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)) :
    trR P Bs e Ψ = fun ρ => φ * trR P Bs e Φ ρ := by
  have hsm : ∀ (c : ℂ) (A : Wq →L[ℂ] Wp), B.hsVec (c • A) = c • B.hsVec A := by
    intro c A
    unfold B.hsVec
    ext i
    simp
  funext ρ
  have hraw : rawR P Bs.μsec e (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
      fun q => (φ : MA.Qp P.r P.TT → ℂ) q * rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q := by
    funext q
    simp only [rawR]
    rw [hΨ q, hsm, inner_smul_right]
    ring
  show MA.toSm P (rawR P Bs.μsec e (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) =
    φ * MA.toSm P (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ)
  rw [hraw]
  generalize rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ = u
  unfold MA.toSm
  by_cases hu : u ∈ MA.smSub P.r P.TT
  · have hmul : (fun q => (φ : MA.Qp P.r P.TT → ℂ) q * u q) ∈ MA.smSub P.r P.TT :=
      (MA.smSub P.r P.TT).mul_mem φ.2 hu
    rw [dif_pos hmul, dif_pos hu]
    rfl
  · have hmul : (fun q => (φ : MA.Qp P.r P.TT → ℂ) q * u q) ∉ MA.smSub P.r P.TT := by
      intro hm
      apply hu
      have h2 := (MA.smSub P.r P.TT).mul_mem (smInv_mem φ hφ) hm
      convert h2 using 1
      funext q
      simp [hφ q]
    rw [dif_neg hmul, dif_neg hu, mul_zero]

theorem sec_pt (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (q : MA.Qp P.r P.TT) :
    (q.1.1, NF.muZ P.k P.r Bs.μsec q.1.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' ∧
      Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) (NF.muZ P.k P.r Bs.μsec q.1.2) = q.1.2 := by
  have hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
    exact q.2.2
  have hq : (q.1.1, q.1.2) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨q.2.1, hζ⟩
  exact ⟨Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hpl.2.1 hpl.2.2.1 Bs.sec hq,
    Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ⟩

theorem tt_pos (P : M.Par) (hP : P.OK) : 0 < P.TT := by
  show 0 < P.T * P.T'
  exact mul_pos hP.T_pos hP.T'_pos

theorem zeta_ne (P : M.Par) (hP : P.OK) (q : MA.Qp P.r P.TT) : q.1.2 ≠ 0 := by
  have h2 : P.TT < Complex.normSq q.1.2 :=
    (q.2 : (∀ l, q.1.1 l ≠ 0) ∧ P.TT < Complex.normSq q.1.2).2
  intro h
  rw [h, map_zero] at h2
  linarith [tt_pos P hP]

theorem gg_ne (P : M.Par) (q : MA.Qp P.r P.TT) : (q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ)) ≠ 0 := by
  have h2 : P.TT < Complex.normSq q.1.2 :=
    (q.2 : (∀ l, q.1.1 l ≠ 0) ∧ P.TT < Complex.normSq q.1.2).2
  rw [Complex.mul_conj]
  intro h
  have h3 : ((Complex.normSq q.1.2 - P.TT : ℝ) : ℂ) = 0 := by
    push_cast
    exact h
  rw [Complex.ofReal_eq_zero] at h3
  linarith

theorem trR_fn (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (j : Fin 6)
    (φ : MA.SmQ P.r P.TT) (hφ : ∀ q, (φ : MA.Qp P.r P.TT → ℂ) q ≠ 0)
    (hv : ∀ q : MA.Qp P.r P.TT, Q.fnVal P.k P.r Bs.z Bs.z' j (NF.muZ P.k P.r Bs.μsec q.1.2) = (φ : MA.Qp P.r P.TT → ℂ) q)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    trR P Bs e (X.fn j Φ) =
      fun ρ => φ * trR P Bs e Φ ρ := by
  refine trR_unit P Bs e Φ (X.fn j Φ) φ hφ fun q => ?_
  have h := X.fn_apply j Φ _ (sec_pt P Bs hpl q).1
  dsimp only at h
  rw [h, hv q]

end tr

theorem gauge_function_holds : GTFn := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e Φ
  obtain ⟨hpl, -, -, hL, -, -, -⟩ := hH
  have hP : P.OK := hpl.1
  have hz := fun q => (sec_pt P Bs hpl q).2
  have hzv : ∀ q : MA.Qp P.r P.TT, ((MA.coordQ (r := P.r) (TT := P.TT) M.vz : MA.SmQ P.r P.TT) :
      MA.Qp P.r P.TT → ℂ) q ≠ 0 := fun q => by rw [coordQ_vz]; exact zeta_ne P hP q
  have hzbv : ∀ q : MA.Qp P.r P.TT, ((MA.coordQ (r := P.r) (TT := P.TT) M.vzb : MA.SmQ P.r P.TT) :
      MA.Qp P.r P.TT → ℂ) q ≠ 0 := fun q => by
    rw [coordQ_vzb]; exact (map_ne_zero _).2 (zeta_ne P hP q)
  have hgg : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    show ((MA.coordQ (r := P.r) (TT := P.TT) M.vz : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q *
        ((MA.coordQ (r := P.r) (TT := P.TT) M.vzb : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q - (P.TT : ℂ) = _
    rw [coordQ_vz, coordQ_vzb]
  have hggv : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q ≠ 0 :=
    fun q => by rw [hgg]; exact gg_ne P q
  have hGG : ∀ q : MA.Qp P.r P.TT, ((Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) : ℝ) : ℂ) =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    rw [Complex.mul_conj]
    unfold Q.GGl
    rw [hz q, hpl.2.2.2.1, hpl.2.2.2.2.1]
    have hT : ((P.TT : ℝ) : ℂ) = (P.T : ℂ) * (P.T' : ℂ) := by
      show (((P.T * P.T' : ℝ)) : ℂ) = _
      push_cast; ring
    rw [hT]
    push_cast
    ring
  have hsc : ∀ (w : (MA.DQ P).Pr) (f : M.Ty P → MA.SmQ P.r P.TT),
      MA.actA P (MA.sc P (MA.DQ P) w) f = fun ρ => w.1 (f ρ) := VLem.actA_sc P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 0 _ hzv (fun q => by rw [coordQ_vz]; exact hz q) Φ).trans ?_
    exact (hsc ((MA.DQ P).zP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 1 (Ring.inverse (MA.coordQ M.vz))
      (fun q => by rw [inverse_apply _ hzv]; exact inv_ne_zero (hzv q))
      (fun q => by rw [inverse_apply _ hzv, coordQ_vz]; show (Q.zetaL _ _ _ _ _ _)⁻¹ = _; rw [hz q]) Φ).trans ?_
    exact (hsc ((MA.DQ P).ziP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 2 _ hzbv (fun q => by
      rw [coordQ_vzb]; show star (Q.zetaL _ _ _ _ _ _) = _; rw [hz q]; rfl) Φ).trans ?_
    exact (hsc ((MA.DQ P).zbP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 3 (Ring.inverse (MA.coordQ M.vzb))
      (fun q => by rw [inverse_apply _ hzbv]; exact inv_ne_zero (hzbv q))
      (fun q => by
        rw [inverse_apply _ hzbv, coordQ_vzb]; show (star (Q.zetaL _ _ _ _ _ _))⁻¹ = _; rw [hz q]; rfl) Φ).trans ?_
    exact (hsc ((MA.DQ P).zbiP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 4 _ hggv (fun q => by rw [hgg]; exact hGG q) Φ).trans ?_
    exact (hsc ((MA.DQ P).ggP P.TT) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 5 (Ring.inverse (ggS P))
      (fun q => by rw [inverse_apply _ hggv]; exact inv_ne_zero (hggv q))
      (fun q => by rw [inverse_apply _ hggv, hgg]; show ((Q.GGl _ _ _ _ _ : ℝ) : ℂ)⁻¹ = _; rw [hGG q]) Φ).trans ?_
    exact (hsc ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ)).symm

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GT
