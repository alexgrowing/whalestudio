import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NegMulCCancel

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants
open Formalism.FourierDecayAlt.P.LeftFubiniLemmas

section fubini

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def psiH {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : ℂ := G.psi U.betaU (U.subS (lhOf σ v))

theorem volume_empty_blocks_real (p : ℕ) : (volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).real Set.univ = 1 := by
  rw [Measure.volume_eq_prod, measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod]
  rw [volume_pi, volume_pi, Measure.pi_univ, Measure.pi_univ]
  simp [volume_pi, Measure.pi_univ]

def regroup (σ : Equiv.Perm (Fin p)) :
    XL k p ρ σ ≃ᵐ PBQ.XP k p ρ × ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ) :=
  MeasurableEquiv.prodAssoc.symm

theorem regroup_apply (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) : regroup σ x = ((x.1, x.2.1), x.2.2) := rfl

theorem regroup_mp (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) :
    MeasurePreserving (regroup σ) (muL Bj σ)
      ((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod
        (volume : Measure (U.LW σ → ℂ)))) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  exact (measurePreserving_prodAssoc (Bj.μW.prod Bj.μN) (U.muRC k p ρ)
    ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ)))).symm

def fH (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ)
    (q : PBQ.XP k p ρ × ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ)) : Wq →L[ℂ] Wp :=
  psiH σ q.2.2 • PBQ.pbI Bj B0 rfl H (U.mMap k p ρ (lhOf σ q.2.2 * U.hMat σ d) g) q.1

theorem ellL_eq (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (σ : Equiv.Perm (Fin p))
    (d : Fin p → ℂ) (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k ρ) (x : XL k p ρ σ) (hx : GoodL Bj σ x) :
    ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g)) = fH Bj B0 σ d H g (regroup σ x) := by
  have hP : PBQ.GoodP Bj (x.1, x.2.1) := hx
  have hs : sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g =
      D.castM rfl (PBQ.sP Bj (x.1, x.2.1)) * U.mMap k p ρ (lhOf σ x.2.2.2 * U.hMat σ d) g := by
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, sxL, if_pos hx, PBQ.sP, if_pos hP]
    have e := embedding_map_lower_unipotent k p ρ (lhOf σ x.2.2.2) (U.hMat σ d) 1 g (lh_unit σ x.2.2.2)
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.PBM.muP_one, Matrix.mul_one] at e
    rw [e]
    have e2 := embedded_group_measure_preserving k p ρ ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹)
      ((lhOf σ x.2.2.2)ᴴ⁻¹)
    simp only [Matrix.mul_assoc] at e2 ⊢
    rw [← Matrix.mul_assoc (U.muP k p ρ _) (U.embG k p ρ _), ← e2, Matrix.mul_assoc]
  rw [hs, regroup_apply]
  unfold fH ellL PBQ.pbI cL PBQ.cP psiH
  simp only [_root_.smul_apply, ContinuousLinearMap.compL_apply, smul_smul]
  congr 1
  ring

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jfSliceInt (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ => psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g))
        volume ∧
      B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
        ∫ v : U.LW σ → ℂ, psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g) := by
  obtain ⟨hint, hJ⟩ := core_lf hp σ d hd Bj B0 hz' hπ' hW' hW0' hNj hN0 g hg H hHc R hR
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  have hsf : SigmaFinite (PBQ.muXP (p := p) Bj) := by unfold PBQ.muXP; infer_instance
  have hae : (fun x => ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g))) =ᵐ[muL Bj σ]
      fun x => fH Bj B0 σ d H g (regroup σ x) := by
    filter_upwards [ae_goodL Bj σ] with x hx
    exact ellL_eq Bj B0 σ d H g x hx
  have mp := regroup_mp Bj σ
  have hint2 : Integrable (fH Bj B0 σ d H g)
      ((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))).prod
        (volume : Measure (U.LW σ → ℂ)))) :=
    (mp.integrable_comp_emb (regroup σ).measurableEmbedding).1 ((hint.congr hae))
  have hJ2 : B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
      ∫ q, fH Bj B0 σ d H g q ∂((PBQ.muXP Bj).prod ((volume : Measure ((Fin 0 → Fin p → ℂ) ×
        (Fin p → Fin 0 → ℂ))).prod (volume : Measure (U.LW σ → ℂ)))) := by
    rw [hJ, integral_congr_ae hae, mp.integral_comp' (fH Bj B0 σ d H g)]
  have hin : ∀ c : ((Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ)) × (U.LW σ → ℂ),
      ∫ xP, fH Bj B0 σ d H g (xP, c) ∂(PBQ.muXP Bj) =
        psiH σ c.2 • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ c.2 * U.hMat σ d) g) := by
    intro c
    unfold fH PBQ.pbF
    exact integral_smul (psiH σ c.2) _
  have hR1 := hint2.integral_prod_right
  simp only [hin] at hR1
  have hR2 := hR1.integral_prod_right
  simp only [integral_const, volume_empty_blocks_real, one_smul] at hR2
  refine ⟨hR2, ?_⟩
  rw [hJ2, integral_prod_symm _ hint2]
  simp only [hin]
  rw [integral_fun_snd (fun v : U.LW σ → ℂ => psiH σ v • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g)),
    volume_empty_blocks_real, one_smul]

end fubini

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem slice_integral_jacobian_factor {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ =>
        G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf σ v)) • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (LeftFubiniLemmas.lhOf σ v * U.hMat σ d) g))
        volume ∧
      B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
        ∫ v : U.LW σ → ℂ,
          G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf σ v)) • PBQ.pbF Bj B0 rfl H (U.mMap k p ρ (LeftFubiniLemmas.lhOf σ v * U.hMat σ d) g) :=
  SliceIntegralLemmas.jfSliceInt hp σ d hd Bj B0 hz' hπ' hW' hW0' hNj hN0 g hg H hHc R hR

end Formalism.FourierDecayAlt.P
