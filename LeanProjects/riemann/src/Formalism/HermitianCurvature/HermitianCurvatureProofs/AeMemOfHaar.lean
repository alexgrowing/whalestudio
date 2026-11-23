import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevAInv

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section reorder

variable {X Y A X' Y' A' : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A] [MeasurableSpace X']
  [MeasurableSpace Y'] [MeasurableSpace A']

def reorderE : ((X × Y) × (X' × Y')) × (A × A') ≃ᵐ (X × (A × Y)) × (X' × (A' × Y')) where
  toFun q := ((q.1.1.1, (q.2.1, q.1.1.2)), (q.1.2.1, (q.2.2, q.1.2.2)))
  invFun p := (((p.1.1, p.1.2.2), (p.2.1, p.2.2.2)), (p.1.2.1, p.2.2.1))
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    change Measurable fun q : ((X × Y) × (X' × Y')) × (A × A') => ((q.1.1.1, (q.2.1, q.1.1.2)), (q.1.2.1, (q.2.2, q.1.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable fun p : (X × (A × Y)) × (X' × (A' × Y')) => (((p.1.1, p.1.2.2), (p.2.1, p.2.2.2)), (p.1.2.1, p.2.2.1))
    fun_prop

theorem reorder_mp (μX : Measure X) (μY : Measure Y) (μA : Measure A) (μX' : Measure X') (μY' : Measure Y')
    (μA' : Measure A') [SigmaFinite μX] [SigmaFinite μY] [SigmaFinite μA] [SigmaFinite μX'] [SigmaFinite μY']
    [SigmaFinite μA'] :
    MeasurePreserving (reorderE (X := X) (Y := Y) (A := A) (X' := X') (Y' := Y') (A' := A'))
      (((μX.prod μY).prod (μX'.prod μY')).prod (μA.prod μA'))
      ((μX.prod (μA.prod μY)).prod (μX'.prod (μA'.prod μY'))) := by
  have h1 := Dx2.SplitM.middle_four_swap_measure_preserving (μX.prod μY) (μX'.prod μY') μA μA'
  have h2 := ((MeasurePreserving.id μX).prod (Measure.measurePreserving_swap (μ := μY) (ν := μA))).comp
    (measurePreserving_prodAssoc μX μY μA)
  have h2' := ((MeasurePreserving.id μX').prod (Measure.measurePreserving_swap (μ := μY') (ν := μA'))).comp
    (measurePreserving_prodAssoc μX' μY' μA')
  have hall := (h2.prod h2').comp h1
  convert hall using 1
  funext ⟨⟨⟨x, y⟩, ⟨x', y'⟩⟩, ⟨a, a'⟩⟩
  rfl

end reorder

variable {k : ℕ}

def MCOm : Prop :=
  ∀ (k ρ : ℕ) (z0 z0' : Fin (2 * ρ + k + 1) → ℂ), inWb k ρ z0 → inWb k ρ z0' → ∀ c : ℂ, c ≠ 0 →
    ∀ γ ∈ B.GV k ρ, γ ∈ Q.OmPlus k ρ z0 z0' →
      D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) ∈
        JF.Om k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0'))

theorem ae_mem_of_haar {r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ U := by
  rw [ae_iff]; exact h.conc

theorem jfStep_of (hO : MCOm) : JFStep := by
  intro k ρ m e Wp Wq _ _ _ _ _ _ B1 B0 hz hz' hπ hπ' hW1 hW1' hW0 hW0' hN1 hN0 f1 f0 c hc hf1 hstep γ hγ hγO
  subst e
  rw [Dx2.Tower.castV_rfl] at hz hz'
  set κ : 1 + ρ = ρ + 1 := Nat.add_comm 1 ρ with hκ
  have hπ1 : ∀ y : B.Mat k ρ, B0.π y = B1.π (D.castM κ (ιLev k 1 ρ y)) := by
    intro y; rw [hπ y]; unfold lev1; rw [Dx2.MN.castM_rfl]
  have hπ1' : ∀ y : B.Mat k ρ, B0.π' y = B1.π' (D.castM κ (ιLev k 1 ρ y)) := by
    intro y; rw [hπ' y]; unfold lev1; rw [Dx2.MN.castM_rfl]
  have hmc : mc rfl c γ = D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) := by
    unfold mc; rw [Dx2.MN.castM_rfl]

  have hμW : B1.μW = B0.μW.map (levA ρ) :=
    muW_lev B0.z B0.μW B1.μW B0.haarW (by rw [← hz]; exact B1.haarW) hW0 hW1
  have hμW' : B1.μW' = B0.μW'.map (levA ρ) :=
    muW_lev B0.z' B0.μW' B1.μW' B0.haarW' (by rw [← hz']; exact B1.haarW') hW0' hW1'
  have hμN : B1.μN = ((B2.μHeis k ρ).prod (D.muN k ρ)).map (Qm ρ) := by rw [hN1, muN_succ']

  have hOm := hO k ρ B0.z B0.z' B0.z_mem B0.z'_mem c hc γ hγ hγO
  rw [← hz, ← hz', ← hmc] at hOm
  have hInt := rhs_int B1 f1 hf1 _ hOm
  have hsH := sf_heis (k := k) ρ
  have hsN := sf_muN (k := k) ρ
  have hfW : IsFiniteMeasure B0.μW := ⟨by rw [hW0]; exact ENNReal.one_lt_top⟩
  have hfW' : IsFiniteMeasure B0.μW' := ⟨by rw [hW0']; exact ENNReal.one_lt_top⟩
  set T : (Mt k ρ × (Mt k (1 + ρ) × Mt k ρ)) × (Mt k ρ × (Mt k (1 + ρ) × Mt k ρ)) → B.SS k (ρ + 1) :=
    Prod.map (Prod.map (levA ρ) (Qm ρ)) (Prod.map (levA ρ) (Qm ρ)) with hT
  have hTm : Measurable T :=
    ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable).prodMap
      ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable)
  set big := (B0.μW.prod ((B2.μHeis k ρ).prod (D.muN k ρ))).prod
    (B0.μW'.prod ((B2.μHeis k ρ).prod (D.muN k ρ))) with hbig
  have hμSS : B1.μSS = big.map T := by
    unfold B.RealPlaceData.μSS
    rw [hμW, hμW', hμN, Measure.map_prod_map _ _ (levA_cont ρ).measurable (Qm_cont ρ).measurable,
      Measure.map_prod_map _ _ (levA_cont ρ).measurable (Qm_cont ρ).measurable,
      Measure.map_prod_map _ _ ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable)
        ((levA_cont ρ).measurable.prodMap (Qm_cont ρ).measurable)]
  set FI := JF.integrand B1 f1 (mc rfl c γ) with hFI
  have hR : B.JF B1 f1 (mc rfl c γ) = ∫ p, FI p ∂B1.μSS := rfl
  have hL : B.JF B0 f0 γ = ∫ p, JF.integrand B0 f0 γ p ∂((B0.μW.prod (D.muN k ρ)).prod (B0.μW'.prod (D.muN k ρ))) := by
    rw [← hN0]; rfl
  have hAE : AEStronglyMeasurable FI (big.map T) := by rw [← hμSS]; exact hInt.aestronglyMeasurable
  have hInt2 : Integrable (FI ∘ T) big := (integrable_map_measure hAE hTm.aemeasurable).1 (by rw [← hμSS]; exact hInt)
  have hRmp := reorder_mp B0.μW (D.muN k ρ) (B2.μHeis k ρ) B0.μW' (D.muN k ρ) (B2.μHeis k ρ)
  have hInt3 : Integrable (FI ∘ T ∘ reorderE) (((B0.μW.prod (D.muN k ρ)).prod (B0.μW'.prod (D.muN k ρ))).prod
      ((B2.μHeis k ρ).prod (B2.μHeis k ρ))) :=
    (hRmp.integrable_comp_emb reorderE.measurableEmbedding).2 hInt2
  rw [hR, hμSS, integral_map hTm.aemeasurable hAE, ← hRmp.integral_comp reorderE.measurableEmbedding]
  change B.JF B0 f0 γ = ∫ x, (FI ∘ T ∘ reorderE) x ∂_
  rw [integral_prod _ hInt3, hL]

  have w1 : ∀ᵐ x ∂B0.μW, Matrix.of x ∈ UWset k ρ B0.z := ae_mem_of_haar B0.haarW
  have w1' : ∀ᵐ x ∂B0.μW', Matrix.of x ∈ UWset k ρ B0.z' := ae_mem_of_haar B0.haarW'
  have w2 : ∀ᵐ x ∂(D.muN k ρ), Matrix.of x ∈ Nset k ρ := ae_mem_of_haar (Dx2.MN.haar ρ)
  have wH : ∀ᵐ x ∂(B2.μHeis k ρ), Matrix.of x ∈ Nset k (1 + ρ) := by
    filter_upwards [ae_mem_of_haar (Formalism.FourierDecayAlt.P.heisenberg_haar_measure k ρ)] with x hx
    obtain ⟨p, hp⟩ := hx
    rw [← hp]; exact Formalism.FourierDecayAlt.P.heisenberg_mem_unipotent k ρ p
  set μO := (B0.μW.prod (D.muN k ρ)).prod (B0.μW'.prod (D.muN k ρ)) with hμO
  have o1 : ∀ᵐ o ∂μO, Matrix.of o.1.1 ∈ UWset k ρ B0.z :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae w1)
  have o2 : ∀ᵐ o ∂μO, Matrix.of o.1.2 ∈ Nset k ρ :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae w2)
  have o3 : ∀ᵐ o ∂μO, Matrix.of o.2.1 ∈ UWset k ρ B0.z' :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae w1')
  have o4 : ∀ᵐ o ∂μO, Matrix.of o.2.2 ∈ Nset k ρ :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae w2)
  have i1 : ∀ᵐ i ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)), Matrix.of i.1 ∈ Nset k (1 + ρ) :=
    Measure.quasiMeasurePreserving_fst.ae wH
  have i2 : ∀ᵐ i ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)), Matrix.of i.2 ∈ Nset k (1 + ρ) :=
    Measure.quasiMeasurePreserving_snd.ae wH
  apply integral_congr_ae
  filter_upwards [o1, o2, o3, o4] with o ho1 ho2 ho3 ho4
  obtain ⟨⟨h0, y⟩, ⟨h0', y'⟩⟩ := o
  simp only at ho1 ho2 ho3 ho4
  have hH := Ux3.hpk_det k ρ
  have hgG : Matrix.of y * Matrix.of h0 ∈ B.GV k ρ := HermitianFormFactor.UH_mul ho2.1 ho1.1
  have hgG' : Matrix.of y' * Matrix.of h0' ∈ B.GV k ρ := HermitianFormFactor.UH_mul ho4.1 ho3.1
  set γh := (Matrix.of y * Matrix.of h0)⁻¹ * γ * (Matrix.of y' * Matrix.of h0') with hγhd
  have hγh : γh ∈ B.GV k ρ := HermitianFormFactor.UH_mul (HermitianFormFactor.UH_mul (HermitianFormFactor.UH_inv hH hgG) hγ) hgG'

  have hrep := B0.π_rep
  have hrep' := B0.π'_rep
  have hi0 : (Matrix.of h0)⁻¹ ∈ UWset k ρ B0.z := WeylGroupFacts.uw_inv ho1
  have hi0' : (Matrix.of h0')⁻¹ ∈ UWset k ρ B0.z' := WeylGroupFacts.uw_inv ho3
  have hu0 : IsUnit (Matrix.of h0).det := HermitianFormFactor.UH_unit hH ho1.1
  have hu0' : IsUnit (Matrix.of h0').det := HermitianFormFactor.UH_unit hH ho3.1
  let eA : Wp ≃L[ℂ] Wp := ContinuousLinearEquiv.equivOfInverse (B0.π (Matrix.of h0)) (B0.π (Matrix.of h0)⁻¹)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hi0 _ ho1, Matrix.nonsing_inv_mul _ hu0, hrep.1]; rfl)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ ho1 _ hi0, Matrix.mul_nonsing_inv _ hu0, hrep.1]; rfl)
  let eB : Wq ≃L[ℂ] Wq := ContinuousLinearEquiv.equivOfInverse (B0.π' (Matrix.of h0')) (B0.π' (Matrix.of h0')⁻¹)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep'.2 _ hi0' _ ho3, Matrix.nonsing_inv_mul _ hu0', hrep'.1]; rfl)
    (fun v => by
      rw [← ContinuousLinearMap.comp_apply, ← hrep'.2 _ ho3 _ hi0', Matrix.mul_nonsing_inv _ hu0', hrep'.1]; rfl)
  let Λ : (Wq →L[ℂ] Wp) ≃L[ℂ] (Wq →L[ℂ] Wp) := eB.arrowCongr eA
  have hΛ : ∀ Tm : Wq →L[ℂ] Wp, Λ Tm = (B0.π (Matrix.of h0)).comp (Tm.comp (B0.π' (Matrix.of h0')⁻¹)) := by
    intro Tm; ext v; rfl
  set K : ℂ := psi k ρ B0.z cStd (Matrix.of y) * star (psi k ρ B0.z' cStd (Matrix.of y')) with hK
  set Ψ : Mt k (1 + ρ) × Mt k (1 + ρ) → (Wq →L[ℂ] Wp) := fun p => psiInt B1 f1 c γh (Matrix.of p.1) (Matrix.of p.2)
    with hΨ
  symm
  calc ∫ i, (FI ∘ T ∘ reorderE) (((h0, y), (h0', y')), i) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ))
      = ∫ i, K • Λ (Ψ (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) i.1,
          conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) i.2)) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ)) := by
        apply integral_congr_ae
        filter_upwards [i1, i2] with i hi1 hi2
        rw [hΛ]
        show JF.integrand B1 f1 (mc rfl c γ) ((levA ρ h0, Qm ρ (i.1, y)), (levA ρ h0', Qm ρ (i.2, y'))) = _
        rw [hmc, pt_eq B1 B0 hz hz' hπ1 hπ1' f1 c γ h0 y h0' y' i.1 i.2 ho1 ho2 ho3 ho4 hi1 hi2]
    _ = K • Λ (∫ i, Ψ (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) i.1,
          conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) i.2) ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ))) := by
        rw [integral_smul, Λ.integral_comp_comm]
    _ = K • Λ (∫ i, Ψ i ∂((B2.μHeis k ρ).prod (B2.μHeis k ρ))) := by
        rw [heis_conj_int ρ hgG hgG' Ψ]
    _ = K • Λ (∫ xx : U.RC k 1 ρ × U.RC k 1 ρ, psiInt B1 f1 c γh (U.Rn k 1 ρ xx.1) (U.Rn k 1 ρ xx.2)
          ∂((U.muRC k 1 ρ).prod (U.muRC k 1 ρ))) := by
        rw [← heis_int ρ (fun b b' => psiInt B1 f1 c γh b b')]
    _ = K • Λ (f0 γh) := by
        rw [hstep γh hγh]
        rfl
    _ = JF.integrand B0 f0 γ ((h0, y), (h0', y')) := by
        rw [hΛ]
        unfold JF.integrand JF.xiP B.rho B.sgs
        congr 3
        show f0 γh = f0 ((Matrix.of h0)⁻¹ * (Matrix.of y)⁻¹ * γ * Matrix.of y' * Matrix.of h0')
        rw [hγhd, Matrix.mul_inv_rev]
        simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P.PBH
