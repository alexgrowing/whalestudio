import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatPolyOK
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDCCLower

open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

def RDSPolyProp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (o κ : ℕ) (Θ : B.DiffOp k r Wp Wq), CutMP.PolyOp o κ Θ → B.Commutes D (B.GPos D) Θ → OpProp1 D Θ

def RDSAGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsPlace P D.z D.z' D.π D.π' → ∀ y : ℂ,
    ∃ Θ Θv : B.DiffOp P.k P.r Wp Wq, (∃ o κ : ℕ, CutMP.PolyOp o κ Θ) ∧ (∃ o κ : ℕ, CutMP.PolyOp o κ Θv) ∧
      B.Commutes D (B.GPos D) Θ ∧ B.Commutes D (B.GPos D) Θv ∧
      ∀ J : B.Mat P.k P.r → (Wq →L[ℂ] Wp), J ∈ Q.FFl P.k P.r D.z D.z' D.π D.π' 0 (JF.Om P.k P.r D.z D.z') →
        ∀ x ∈ DomR P.k P.r D.z D.z',
          resG P.k P.r (Fin.last P.r) (B.opApply Θ J) x.1 x.2 =
              CutMP.dMul (CutMP.drF P.r) (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) (resG P.k P.r (Fin.last P.r) J)) x.1 x.2 ∧
            resG P.k P.r (Fin.last P.r) (B.opApply Θv J) x.1 x.2 =
              CutMP.dMul (CutMP.drbF P.r) (Q.crd (Q.cmp (CutMP.vABm P.r y P.r) 0) (resG P.k P.r (Fin.last P.r) J))
                x.1 x.2

def RDSARad : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π')
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r), IsActualLevel X L →
    ∀ (y : ℂ) (Φ : RadSp P.k P.r z z' π π'),
      (((L.Ahat y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) =
          CutMP.dMul (CutMP.drF P.r) (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp))) ∧
        (((L.Ahatv y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) =
          CutMP.dMul (CutMP.drbF P.r) (Q.crd (Q.cmp (CutMP.vABm P.r y P.r) 0) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)))

def RDSALoc : Prop :=
  ∀ (r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (y : ℂ) (f f' : (Fin r → ℂ) → E),
    (∀ c ∈ OmX r, f c = f' c) → ∀ c ∈ OmX r,
      (Q.vAB r y r).1 f c = (Q.vAB r y r).1 f' c ∧ (CutMP.vABm r y r).1 f c = (CutMP.vABm r y r).1 f' c

theorem rds_dMul_loc {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (hLoc : RDSALoc) (y : ℂ)
    (Φ Ψ : Fn k r E) (g : Mx k r) (hΦΨ : ∀ c ∈ OmX r, Φ c g = Ψ c g) (c : Fin r → ℂ) (hc : c ∈ OmX r) :
    CutMP.dMul (CutMP.drF r) (Q.crd (Q.cmp (Q.vAB r y r) 0) Φ) c g =
        CutMP.dMul (CutMP.drF r) (Q.crd (Q.cmp (Q.vAB r y r) 0) Ψ) c g ∧
      CutMP.dMul (CutMP.drbF r) (Q.crd (Q.cmp (CutMP.vABm r y r) 0) Φ) c g =
        CutMP.dMul (CutMP.drbF r) (Q.crd (Q.cmp (CutMP.vABm r y r) 0) Ψ) c g := by
  obtain ⟨h1, h2⟩ := hLoc r E y (fun c' => Φ c' g) (fun c' => Ψ c' g) (fun c' hc' => hΦΨ c' hc') c hc
  simp only [CutMP.dMul, Q.crd, Q.cmp, if_true]
  exact ⟨by rw [h1], by rw [h2]⟩

theorem rDSOpA_of_parts (hP : RDSPolyProp) (hG : RDSAGrp) (hR : RDSARad) (hLoc : RDSALoc) : RDSOpA := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ hz hz' hπ hπ' _ Y _ _ _ _
  subst hz hz' hπ hπ'
  obtain ⟨hPl, -, hL, -⟩ := hD
  obtain ⟨Θ, Θv, ⟨o, κ, hpo⟩, hpv, hc, hcv, hres⟩ := hG Wp Wq P D hPl Y
  refine ⟨Θ, hP P.k P.r Wp Wq D o κ Θ hpo hc, ?_⟩
  intro J hJ Φ hΦ x hx
  have e := congrFun (congrFun (hR Wp Wq P D.z D.z' D.π D.π' X L hL Y Φ).1 x.1) x.2
  refine ((hres J hJ x hx).1).trans (Eq.trans ?_ e.symm)
  obtain ⟨hc1, hg1, hG1⟩ := hx
  exact (rds_dMul_loc hLoc Y _ _ x.2
    (fun c' hc' => (hΦ (c', x.2) ⟨hc', hg1, hG1⟩).symm) x.1 hc1).1

theorem rDSOpAv_of_parts (hP : RDSPolyProp) (hG : RDSAGrp) (hR : RDSARad) (hLoc : RDSALoc) : RDSOpAv := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ hz hz' hπ hπ' _ Y _ _ _ _
  subst hz hz' hπ hπ'
  obtain ⟨hPl, -, hL, -⟩ := hD
  obtain ⟨Θ, Θv, hpa, ⟨o, κ, hpo⟩, hca, hc, hres⟩ := hG Wp Wq P D hPl (Y + 1)
  refine ⟨Θv, hP P.k P.r Wp Wq D o κ Θv hpo hc, ?_⟩
  intro J hJ Φ hΦ x hx
  have e := congrFun (congrFun (hR Wp Wq P D.z D.z' D.π D.π' X L hL (Y + 1) Φ).2 x.1) x.2
  refine ((hres J hJ x hx).2).trans (Eq.trans ?_ e.symm)
  obtain ⟨hc1, hg1, hG1⟩ := hx
  exact (rds_dMul_loc hLoc (Y + 1) _ _ x.2
    (fun c' hc' => (hΦ (c', x.2) ⟨hc', hg1, hG1⟩).symm) x.1 hc1).2

end Formalism.FourierDecayAlt.P.CutSE
