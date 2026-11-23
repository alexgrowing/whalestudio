import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Topx1

namespace Formalism.FourierDecayAlt.P.PBI

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def GrpInt (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (V : Wq →L[ℂ] Wp) : Prop :=
  ∀ hB ∈ UWset k r S.z', hB *ᵥ ν' = ν' → (S.π (m₀ * hB * m₀⁻¹)).comp (V.comp (S.π' hB⁻¹)) = V

theorem gen_dOp_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) {X : B.Mat k r}
    (hX : QrD.InLieW k r S.z' X) (hXν : X *ᵥ ν' = 0) (hY : QrD.InLieW k r S.z (m₀ * X * m₀⁻¹)) :
    (QrD.dOp S.π (m₀ * X * m₀⁻¹)).comp V = V.comp (QrD.dOp S.π' X) := by
  obtain ⟨hmU, -, hiU, -, um, -, -⟩ := vecw_base_parts S hbase
  have key : ∀ t : ℝ, (S.π (NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)))).comp V =
      V.comp (S.π' (NormedSpace.exp ((t : ℂ) • X))) := by
    intro t
    have hhB := QrD.exp_uw hX t
    have hBν := Qx8.exp_fix hXν t
    set hB := NormedSpace.exp ((t : ℂ) • X) with hhBdef
    have hconj : NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)) = m₀ * hB * m₀⁻¹ := by
      have h := LeftDerivativeCurves.exp_swap hiU X t
      rw [Matrix.nonsing_inv_nonsing_inv _ um] at h
      calc NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹))
          = m₀ * (m₀⁻¹ * NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹))) := by
            rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ um, Matrix.one_mul]
        _ = m₀ * hB * m₀⁻¹ := by rw [h, Matrix.mul_assoc]
    have h := hV hB hhB hBν
    have hinv := WeylGroupFacts.uw_inv hhB
    have uB := WeylGroupFacts.isUnit_of_uh hhB.1
    rw [hconj]
    calc (S.π (m₀ * hB * m₀⁻¹)).comp V
        = ((S.π (m₀ * hB * m₀⁻¹)).comp (V.comp (S.π' hB⁻¹))).comp (S.π' hB) := by
          rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, ← S.π'_rep.2 _ hinv _ hhB,
            Matrix.nonsing_inv_mul _ uB, S.π'_rep.1]
          rfl
      _ = V.comp (S.π' hB) := by rw [h]
  have hd1 := QrD.dOp_hasDeriv S.π'_rep S.π'_cont hX
  have hd2 := QrD.dOp_hasDeriv S.π_rep S.π_cont hY
  let L1 : (Wq →L[ℂ] Wq) →L[ℂ] (Wq →L[ℂ] Wp) := ContinuousLinearMap.compL ℂ Wq Wq Wp V
  let L2 : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq Wp Wp).flip V
  have h1 := (L1.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd1
  have h2 := (L2.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd2
  have hfun : ((L2.restrictScalars ℝ) ∘ fun t : ℝ => S.π (NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)))) =
      ((L1.restrictScalars ℝ) ∘ fun t : ℝ => S.π' (NormedSpace.exp ((t : ℂ) • X))) := by
    funext t
    exact key t
  rw [hfun] at h2
  exact h2.unique h1

theorem gen_ecOp_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) {m : ℕ}
    {Bs' : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [S.z', ν'] Bs') (a b : Fin m) :
    (QrD.ecOp S.π (Q.unitB (Hpk k r) (fun a => m₀ *ᵥ Bs' a) a b)).comp V =
      V.comp (QrD.ecOp S.π' (Q.unitB (Hpk k r) Bs' a b)) := by
  obtain ⟨hmU, -, -, -, um, -, -⟩ := vecw_base_parts S hbase
  have hBz : Q.IsFrameOf k r [S.z] (fun a => m₀ *ᵥ Bs' a) :=
    vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (vecw_frame_fwd S hbase hB)
  have hBz' : Q.IsFrameOf k r [S.z'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  have hBν : Q.IsFrameOf k r [ν'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  obtain ⟨e1, e2, e3⟩ := vecw_conj_eq hmU um Bs' a b
  have lY := QrD.frame_lie hBz a b
  have lX := QrD.frame_lie hBz' a b
  have lν := QrD.frame_lie hBν a b
  rw [e1, e2, e3] at lY
  unfold QrD.ecOp
  rw [e1, e2, e3, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, gen_dOp_intertwine S hbase V hV lX.1 lν.1.2 lY.1,
    gen_dOp_intertwine S hbase V hV lX.2 lν.2.2 lY.2]

theorem gen_capRep_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) {m : ℕ}
    {Bs' : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [S.z', ν'] Bs') (w : ℂ) (v : Wq) :
    Q.capRep k r S.π (fun a => m₀ *ᵥ Bs' a) w (V v) = V (Q.capRep k r S.π' Bs' w v) := by
  have hBz : Q.IsFrameOf k r [S.z] (fun a => m₀ *ᵥ Bs' a) :=
    vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (vecw_frame_fwd S hbase hB)
  have hBz' : Q.IsFrameOf k r [S.z'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  unfold Q.capRep
  refine vecw_qmF V.toLinearMap _ _ (fun i j y => ?_) id id w v
  have lY := QrD.frame_lie hBz i j
  have lX := QrD.frame_lie hBz' i j
  simp only [ContinuousLinearMap.coe_coe]
  rw [QrD.ecRep_eq S.π_rep S.π_cont lY.1 lY.2, QrD.ecRep_eq S.π'_rep S.π'_cont lX.1 lX.2]
  have h := congrArg (fun L : Wq →L[ℂ] Wp => L y) (gen_ecOp_intertwine S hbase V hV hB i j)
  simpa using h

end gen

open Finset

theorem types_of_grpInt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (S : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (TP : Formalism.FourierDecayAlt.Top.TypeProj P S.π S.z (m₀ *ᵥ ν')) (hPl : Q.IsPlace P S.z S.z' S.π S.π')
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) :
    ∑ ρ : M.Ty P, (TP.E ρ).comp V = V := by
  obtain ⟨hOK, hz, hz', -, -, hty, hty'⟩ := hPl
  obtain ⟨hmU, hmW, -, -, -, hzeq, -⟩ := vecw_base_parts S hbase
  obtain ⟨hν, hνz, hνν, -, -⟩ := id hbase
  have he : inWb P.k P.r (m₀ *ᵥ ν') := hmW ν' hν
  have hee : herm (Hpk P.k P.r) (m₀ *ᵥ ν') (m₀ *ᵥ ν') = 1 := by rw [Dx2.DF.herm_m0_mulVec_invariant m₀ hmU]; exact hνν
  have hez : herm (Hpk P.k P.r) (m₀ *ᵥ ν') S.z = 0 := by
    rw [hzeq, Qx8.herm_smul_right', Dx2.DF.herm_m0_mulVec_invariant m₀ hmU, hνz, mul_zero]
  obtain ⟨Bs₀', hB₀'⟩ := vecw_frame_exists P.k P.r hOK.k_pos S.z' ν' hz' S.T'_pos hν hνz hνν
  have hB₀ := vecw_frame_fwd S hbase hB₀'
  obtain ⟨S', hInt', -, heig⟩ := branching_proof Wq (parametersUPrimeForU P) (parameters_u_prime_for_u_ok hOK) rfl S.z' ν' S.π' hz'
    S.T'_pos hty' hν hνz hνν
  have heig' : ∀ (σ : M.Ty (parametersUPrimeForU P)) (w : ℂ), ∀ v ∈ S' σ,
      Q.capRep P.k P.r S.π' Bs₀' w v = M.xC (parametersUPrimeForU P) σ (w - ((P.k : ℂ) - 2) / 2) • v :=
    fun σ w v hv => heig Bs₀' hB₀' σ w v hv
  refine ContinuousLinearMap.ext fun f => ?_
  rw [_root_.sum_apply]
  simp only [ContinuousLinearMap.comp_apply]
  have hf : f ∈ ⨆ σ, S' σ := by rw [hInt'.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction S' (motive := fun f => ∑ ρ, TP.E ρ (V f) = V f) hf ?_ ?_ ?_
  · intro σ v hv
    refine vecw_good_of_eig hOK hz S.T_pos hty he hez hee TP hB₀ σ _ fun w => ?_
    rw [gen_capRep_intertwine S hbase V hV hB₀' w v, heig' σ w v hv, map_smul]
  · simp
  · intro a b ha hb
    simp only [map_add, Finset.sum_add_distrib, ha, hb]

end Formalism.FourierDecayAlt.P.PBI
