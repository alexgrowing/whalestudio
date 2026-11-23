import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGVTr

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

open Formalism.FourierDecayAlt.P.CutMP.Gauge

noncomputable section

theorem star_algebraMap_real (P : M.Par) (Y : ℝ) :
    star (algebraMap ℂ (MA.A P (MA.DQ P)) (Y : ℂ)) = algebraMap ℂ (MA.A P (MA.DQ P)) (Y : ℂ) := by
  rw [← algebraMap_star_comm, Complex.star_def, Complex.conj_ofReal]

theorem star_Ts_mul_0 (P : M.Par) (σ : Wd.Site (MA.A P (MA.DQ P))) (Y : ℂ) (V : Wd.M2 (MA.A P (MA.DQ P))) :
    star ((Wd.Ts σ Y * V) 0 0) =
      star (V 0 0) * star (algebraMap ℂ (MA.A P (MA.DQ P)) Y + σ.p) + -(star (V 1 0) * star σ.c) := by
  simp only [Wd.Ts, Formalism.YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, star_add, star_mul, star_neg, neg_mul, mul_neg]

theorem star_Ts_mul_1 (P : M.Par) (σ : Wd.Site (MA.A P (MA.DQ P))) (Y : ℂ) (V : Wd.M2 (MA.A P (MA.DQ P))) :
    star ((Wd.Ts σ Y * V) 1 0) = star (V 0 0) * star σ.ci := by
  simp [Wd.Ts, Formalism.YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two, star_add, star_mul]

theorem actA_sp (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (star (MA.siteA P (MA.DQ P) l).p) f = fun ρ => -MA.eulerQ (TT := P.TT) (M.vcb l) (f ρ) := by
  show MA.actA P (star (MA.sc P (MA.DQ P) _)) f = _
  rw [star_sc, actA_sc]
  rfl

theorem actA_sc' (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (star (MA.siteA P (MA.DQ P) l).c) f = fun ρ => MA.coordQ (TT := P.TT) (M.vcb l) * f ρ := by
  show MA.actA P (star (MA.sc P (MA.DQ P) _)) f = _
  rw [star_sc, actA_sc]
  rfl

theorem actA_sci (P : M.Par) (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (star (MA.siteA P (MA.DQ P) l).ci) f =
      fun ρ => Ring.inverse (MA.coordQ (TT := P.TT) (M.vcb l)) * f ρ := by
  show MA.actA P (star (MA.sc P (MA.DQ P) _)) f = _
  rw [star_sc, actA_sc]
  rfl

section ind

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}

theorem vabs_ind (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e) (Y : ℝ) :
    ∀ i : ℕ, i ≤ P.r → ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      FamR P Bs Dc Φ →
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 0) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 0) Φ) =
          MA.actA P (star (Vp P Y i 0 0)) (trR P Bs.μsec e Φ)) ∧
      (FamR P Bs Dc (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 1) Φ) ∧
        trR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 1) Φ) =
          MA.actA P (star (Vp P Y i 1 0)) (trR P Bs.μsec e Φ)) := by
  intro i
  induction i with
  | zero =>
    intro _ Dc Φ hΦ
    have h0 : Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) 0) 0) Φ = Φ := rfl
    have h1 : Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) 0) 1) Φ = 0 := rfl
    have v0 : Vp P Y 0 0 0 = 1 := by simp [Vp_zero]
    have v1 : Vp P Y 0 1 0 = 0 := by simp [Vp_zero]
    rw [h0, h1, v0, v1, star_one, star_zero, actA_one, actA_zero, trR_zero]
    refine ⟨⟨hΦ, rfl⟩, ⟨?_, rfl⟩⟩
    have := famR_smul hΦ 0
    rwa [zero_smul] at this
  | succ i ih =>
    intro hi Dc Φ hΦ
    have h : i < P.r := hi
    set l : Fin P.r := ⟨i, h⟩ with hl
    have hv : Q.vABs (E := Wq →L[ℂ] Wp) P.r (Y : ℂ) (i + 1) =
        (fun f => (Q.vABs P.r (Y : ℂ) i).1 ((Y : ℂ) • f - pbOp l f) - (Q.vABs P.r (Y : ℂ) i).2 (cbOp l f),
          fun f => (Q.vABs P.r (Y : ℂ) i).1 (cbiOp l f)) := by
      simp only [Q.vABs, dif_pos h, hl]
    set Ψ := (Y : ℂ) • Φ - Q.crd (pbOp l) Φ with hΨ
    have hpb : FamR P Bs Dc (Q.crd (pbOp l) Φ) := famR_opL hΦ l 3
    have hcb : FamR P Bs Dc (Q.crd (cbOp l) Φ) := famR_opL hΦ l 4
    have hcbi : FamR P Bs Dc (Q.crd (cbiOp l) Φ) := famR_opL hΦ l 5
    have hΨf : FamR P Bs Dc Ψ := famR_sub (famR_smul hΦ _) hpb
    obtain ⟨⟨hA, tA⟩, -⟩ := ih (Nat.le_of_lt h) Dc Ψ hΨf
    obtain ⟨-, ⟨hB, tB⟩⟩ := ih (Nat.le_of_lt h) Dc _ hcb
    obtain ⟨⟨hA', tA'⟩, -⟩ := ih (Nat.le_of_lt h) Dc _ hcbi
    have e0 : Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) (i + 1)) 0) Φ =
        Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 0) Ψ - Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 1) (Q.crd (cbOp l) Φ) := by
      rw [hv]; rfl
    have e1 : Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) (i + 1)) 1) Φ =
        Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) i) 0) (Q.crd (cbiOp l) Φ) := by
      rw [hv]; rfl
    have tΨ : trR P Bs.μsec e Ψ =
        MA.actA P (star (algebraMap ℂ (MA.A P (MA.DQ P)) (Y : ℂ) + (MA.siteA P (MA.DQ P) l).p))
          (trR P Bs.μsec e Φ) := by
      rw [hΨ, trR_sub _ _ _ _ (fun ρ => smR hpl hk he (famR_smul hΦ _) ρ) (fun ρ => smR hpl hk he hpb ρ),
        trR_smul, trR_pb hpl hk he hΦ, star_add, star_algebraMap_real, actA_add, actA_algebraMap, actA_sp,
        sub_eq_add_neg]
      rfl
    have tcb : trR P Bs.μsec e (Q.crd (cbOp l) Φ) =
        MA.actA P (star (MA.siteA P (MA.DQ P) l).c) (trR P Bs.μsec e Φ) := by
      rw [actA_sc']
      exact trR_mul hpl hk he hΦ _ hcb (fun c => star (c l)) (fun _ _ => rfl) _ (fun q => coordE_vcb _ _)
    have tcbi : trR P Bs.μsec e (Q.crd (cbiOp l) Φ) =
        MA.actA P (star (MA.siteA P (MA.DQ P) l).ci) (trR P Bs.μsec e Φ) := by
      rw [actA_sci]
      exact trR_mul hpl hk he hΦ _ hcbi (fun c => (star (c l))⁻¹) (fun _ _ => rfl) _ (fun q => by
        rw [inv_coordQ_apply _ (fun x hx => by rw [coordE_vcb]; exact (star_ne_zero).2 (hx.1 _)), coordE_vcb])
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [e0]; exact famR_sub hA hB
    · rw [e0, trR_sub _ _ _ _ (fun ρ => smR hpl hk he hA ρ) (fun ρ => smR hpl hk he hB ρ), tA, tB, tΨ, tcb,
        Vp_succ P Y i h, star_Ts_mul_0, actA_add, actA_mul, actA_neg, actA_mul, sub_eq_add_neg]
    · rw [e1]; exact hA'
    · rw [e1, tA', tcbi, Vp_succ P Y i h, star_Ts_mul_1, actA_mul]

end ind

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge

open VLem

theorem gauge_conj_vector_transition : GVsTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he Dc Φ hΦ Y a
  have h := vabs_ind hpl hk he Y P.r le_rfl Dc Φ hΦ
  rw [sitesCommonSpace_v0_eq_Vp]
  fin_cases a
  · exact ⟨h.1.1, fun ρ => congrFun h.1.2 ρ⟩
  · exact ⟨h.2.1, fun ρ => congrFun h.2.2 ρ⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge
