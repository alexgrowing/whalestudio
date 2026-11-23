import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTypeNormMeas
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower

namespace Formalism.FourierDecayAlt.P.CutBP.TNM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Matrix

noncomputable section

section cov

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : B.Mat k r → (W →L[ℂ] W)}

theorem tc_dOp_conj (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {g : B.Mat k r}
    (hg : g ∈ UWset k r z) {X : B.Mat k r} (hX : P.QrD.InLieW k r z X)
    (hY : P.QrD.InLieW k r z (g * X * g⁻¹)) :
    (P.QrD.dOp π (g * X * g⁻¹)).comp (π g) = (π g).comp (P.QrD.dOp π X) := by
  have hiU := WeylGroupFacts.uh_inv hg.1
  have ug := WeylGroupFacts.isUnit_of_uh hg.1
  have key : ∀ t : ℝ, (π (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)))).comp (π g) =
      (π g).comp (π (NormedSpace.exp ((t : ℂ) • X))) := by
    intro t
    have hE := P.QrD.exp_uw hX t
    have hE' := P.QrD.exp_uw hY t
    have hconj : NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g = g * NormedSpace.exp ((t : ℂ) • X) := by
      have h := P.LeftDerivativeCurves.exp_swap hiU X t
      rw [Matrix.nonsing_inv_nonsing_inv _ ug] at h
      calc NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g
          = g * (g⁻¹ * NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) * g := by
            rw [← Matrix.mul_assoc g, Matrix.mul_nonsing_inv _ ug, Matrix.one_mul]
        _ = g * (NormedSpace.exp ((t : ℂ) • X) * g⁻¹) * g := by rw [h]
        _ = g * NormedSpace.exp ((t : ℂ) • X) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ug, Matrix.mul_one]
    rw [← hπ.2 _ hE' _ hg, ← hπ.2 _ hg _ hE, hconj]
  have hd1 := P.QrD.dOp_hasDeriv hπ hc hX
  have hd2 := P.QrD.dOp_hasDeriv hπ hc hY
  let L1 : (W →L[ℂ] W) →L[ℂ] (W →L[ℂ] W) := ContinuousLinearMap.compL ℂ W W W (π g)
  let L2 : (W →L[ℂ] W) →L[ℂ] (W →L[ℂ] W) := (ContinuousLinearMap.compL ℂ W W W).flip (π g)
  have h1 := (L1.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd1
  have h2 := (L2.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd2
  have hfun : ((L2.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)))) =
      ((L1.restrictScalars ℝ) ∘ fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) := by
    funext t
    exact key t
  rw [hfun] at h2
  exact h2.unique h1

theorem tc_inWb {g : B.Mat k r} (hg : g ∈ UWset k r z) {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) :
    inWb k r (g *ᵥ w) := by
  obtain ⟨hU, hme, hms, -⟩ := P.Dx2.VV.uw_parts hg
  exact P.Dx2.DF.m0_mulVec_mem_orthogonal g hU hme hms hw

theorem tc_ecOp_conj (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {g : B.Mat k r}
    (hg : g ∈ UWset k r z) {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [z] Bs)
    (a b : Fin m) :
    (P.QrD.ecOp π (Q.unitB (Hpk k r) (fun a => g *ᵥ Bs a) a b)).comp (π g) =
      (π g).comp (P.QrD.ecOp π (Q.unitB (Hpk k r) Bs a b)) := by
  have ug := WeylGroupFacts.isUnit_of_uh hg.1
  have hgB : Q.IsFrameOf k r [z] (fun a => g *ᵥ Bs a) :=
    P.Topx1.vecw_frame_map hg.1 (fun w hw => tc_inWb hg hw) (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      exact ⟨1, z, by simp, by rw [hv, one_smul, hg.2.2]⟩) hB
  obtain ⟨e1, e2, e3⟩ := P.Topx1.vecw_conj_eq hg.1 ug Bs a b
  have lY := P.QrD.frame_lie hgB a b
  have lX := P.QrD.frame_lie hB a b
  rw [e1, e2, e3] at lY
  unfold P.QrD.ecOp
  rw [e1, e2, e3, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, tc_dOp_conj hπ hc hg lX.1 lY.1, tc_dOp_conj hπ hc hg lX.2 lY.2]

theorem tc_capRep_conj (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {g : B.Mat k r}
    (hg : g ∈ UWset k r z) {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [z] Bs)
    (w : ℂ) (v : W) :
    Q.capRep k r π (fun a => g *ᵥ Bs a) w (π g v) = π g (Q.capRep k r π Bs w v) := by
  have hgB : Q.IsFrameOf k r [z] (fun a => g *ᵥ Bs a) :=
    P.Topx1.vecw_frame_map hg.1 (fun w hw => tc_inWb hg hw) (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      exact ⟨1, z, by simp, by rw [hv, one_smul, hg.2.2]⟩) hB
  unfold Q.capRep
  refine P.Topx1.vecw_qmF (π g).toLinearMap _ _ (fun i j y => ?_) id id w v
  have lY := P.QrD.frame_lie hgB i j
  have lX := P.QrD.frame_lie hB i j
  simp only [ContinuousLinearMap.coe_coe]
  rw [P.QrD.ecRep_eq hπ hc lY.1 lY.2, P.QrD.ecRep_eq hπ hc lX.1 lX.2]
  have h := congrArg (fun L : W →L[ℂ] W => L y) (tc_ecOp_conj hπ hc hg hB i j)
  simpa using h

end cov

theorem type_commutation_holds : TypeComm := by
  intro PP Wp _ _ _ π z e TP hπ hc hu hk hz hTz he hez hee g hg l hl ρ
  have ug := WeylGroupFacts.isUnit_of_uh hg.1
  have hgi : g⁻¹ ∈ UWset PP.k PP.r z := WeylGroupFacts.uw_inv hg
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hl
    have : e = 0 := by
      rw [← Matrix.one_mulVec e, ← Matrix.nonsing_inv_mul _ ug, ← Matrix.mulVec_mulVec, hl, Matrix.mulVec_zero]
    rw [this] at hee
    simp [herm] at hee
  have hli : g⁻¹ *ᵥ e = l⁻¹ • e := by
    calc g⁻¹ *ᵥ e = g⁻¹ *ᵥ (l⁻¹ • (l • e)) := by rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
      _ = l⁻¹ • (g⁻¹ *ᵥ (g *ᵥ e)) := by rw [hl, Matrix.mulVec_smul]
      _ = l⁻¹ • e := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ug, Matrix.one_mulVec]
  obtain ⟨Bs₀, hB₀⟩ := Formalism.FourierDecayAlt.P.Topx1.typ_frame_exists PP.k PP.r hk z e hz hTz he hez hee
  have hB₀z : Q.IsFrameOf PP.k PP.r [z] Bs₀ := Formalism.FourierDecayAlt.P.Topx1.vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB₀

  have keep : ∀ h ∈ UWset PP.k PP.r z, ∀ c : ℂ, c ≠ 0 → h *ᵥ e = c • e →
      ∀ v, TP.E ρ (π h (TP.E ρ v)) = π h (TP.E ρ v) := by
    intro h hh c hc0 hce v
    have hB1 : Q.IsFrameOf PP.k PP.r [z, e] (fun a => h *ᵥ Bs₀ a) :=
      Formalism.FourierDecayAlt.P.Topx1.vecw_frame_map hh.1 (fun w hw => tc_inWb hh hw) (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact ⟨1, v, by simp, by rw [one_smul, hh.2.2]⟩
        · exact ⟨c⁻¹, v, by simp, by rw [hce, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩) hB₀
    refine TP.full _ hB1 ρ _ fun w => ?_
    rw [tc_capRep_conj hπ hc hh hB₀z w, TP.eigen Bs₀ hB₀ ρ w v, map_smul]
  have kg := keep g hg l hl0 hl
  have kgi := keep g⁻¹ hgi l⁻¹ (inv_ne_zero hl0) hli

  let large₂ : Wp →ₗᵢ[ℂ] Wp := { toLinearMap := (π g : Wp →ₗ[ℂ] Wp), norm_map' := hu g hg }
  have hinn : ∀ x y, inner ℂ (π g x) (π g y) = inner ℂ x y := fun x y => large₂.inner_map_map x y
  have hgg : ∀ y, π g (π g⁻¹ y) = y := by
    intro y
    rw [← ContinuousLinearMap.comp_apply, ← hπ.2 _ hg _ hgi, Matrix.mul_nonsing_inv _ ug, hπ.1]
    rfl
  set E := TP.E ρ with hE
  have hEE : ∀ x, E (E x) = x - (x - E x) := by
    intro x; simp only [sub_sub_cancel]
    exact congrArg (fun L : Wp →L[ℂ] Wp => L x) (TP.idem ρ)
  have hker : ∀ y, E y = 0 → E (π g y) = 0 := by
    intro y hy
    have horth : ∀ u, inner ℂ (π g y) (E u) = 0 := by
      intro u
      calc inner ℂ (π g y) (E u) = inner ℂ (π g y) (π g (π g⁻¹ (E u))) := by rw [hgg]
        _ = inner ℂ y (π g⁻¹ (E u)) := hinn _ _
        _ = inner ℂ y (E (π g⁻¹ (E u))) := by rw [kgi u]
        _ = inner ℂ (E y) (π g⁻¹ (E u)) := (TP.selfAdj ρ _ _).symm
        _ = 0 := by rw [hy, inner_zero_left]
    have hidem : E (E (π g y)) = E (π g y) := congrArg (fun L : Wp →L[ℂ] Wp => L (π g y)) (TP.idem ρ)
    have h0 : inner ℂ (E (π g y)) (E (π g y)) = 0 := by
      rw [TP.selfAdj ρ, hidem, horth]
    exact inner_self_eq_zero.1 h0
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  have hidem : E (E x) = E x := congrArg (fun L : Wp →L[ℂ] Wp => L x) (TP.idem ρ)
  have hsplit : x = E x + (x - E x) := by abel
  have hy : E (x - E x) = 0 := by rw [map_sub, hidem, sub_self]
  conv_lhs => rw [hsplit, map_add, map_add, hker _ hy, add_zero, kg x]

end

end Formalism.FourierDecayAlt.P.CutBP.TNM
